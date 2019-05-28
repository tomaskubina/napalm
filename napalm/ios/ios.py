"""NAPALM Cisco IOS Handler."""
# Copyright 2015 Spotify AB. All rights reserved.
#
# The contents of this file are licensed under the Apache License, Version 2.0
# (the "License"); you may not use this file except in compliance with the
# License. You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations under
# the License.

from __future__ import print_function
from __future__ import unicode_literals

import copy
import functools
import os
import re
import socket
import telnetlib
import tempfile
import uuid
from collections import defaultdict

from netmiko import FileTransfer, InLineTransfer

import napalm.base.constants as C
import napalm.base.helpers
from napalm.base.base import NetworkDriver
from napalm.base.exceptions import (
    ReplaceConfigException,
    MergeConfigException,
    ConnectionClosedException,
    CommandErrorException,
)
from napalm.base.helpers import (
    canonical_interface_name,
    transform_lldp_capab,
    textfsm_extractor,
)
from napalm.base.netmiko_helpers import netmiko_args
from napalm.base.utils import py23_compat

# Easier to store these as constants
HOUR_SECONDS = 3600
DAY_SECONDS = 24 * HOUR_SECONDS
WEEK_SECONDS = 7 * DAY_SECONDS
YEAR_SECONDS = 365 * DAY_SECONDS

# STD REGEX PATTERNS
IP_ADDR_REGEX = r"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}"
IPV4_ADDR_REGEX = IP_ADDR_REGEX
IPV6_ADDR_REGEX_1 = r"::"
IPV6_ADDR_REGEX_2 = r"[0-9a-fA-F:]{1,39}::[0-9a-fA-F:]{1,39}"
IPV6_ADDR_REGEX_3 = (
    r"[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}:"
    "[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}:[0-9a-fA-F]{1,4}"
)
# Should validate IPv6 address using an IP address library after matching with this regex
IPV6_ADDR_REGEX = "(?:{}|{}|{})".format(
    IPV6_ADDR_REGEX_1, IPV6_ADDR_REGEX_2, IPV6_ADDR_REGEX_3
)

MAC_REGEX = r"[a-fA-F0-9]{4}\.[a-fA-F0-9]{4}\.[a-fA-F0-9]{4}"
VLAN_REGEX = r"\d{1,4}"
INT_REGEX = r"(^\w{1,2}\d{1,3}/\d{1,2}|^\w{1,2}\d{1,3})"
RE_IPADDR = re.compile(r"{}".format(IP_ADDR_REGEX))
RE_IPADDR_STRIP = re.compile(r"({})\n".format(IP_ADDR_REGEX))
RE_MAC = re.compile(r"{}".format(MAC_REGEX))

# Period needed for 32-bit AS Numbers
ASN_REGEX = r"[\d\.]+"

IOS_COMMANDS = {
    "show_mac_address": ["show mac-address-table", "show mac address-table"]
}

AFI_COMMAND_MAP = {
    "IPv4 Unicast": "ipv4 unicast",
    "IPv6 Unicast": "ipv6 unicast",
    "VPNv4 Unicast": "vpnv4 all",
    "VPNv6 Unicast": "vpnv6 unicast all",
    "IPv4 Multicast": "ipv4 multicast",
    "IPv6 Multicast": "ipv6 multicast",
    "L2VPN E-VPN": "l2vpn evpn",
    "MVPNv4 Unicast": "ipv4 mvpn all",
    "MVPNv6 Unicast": "ipv6 mvpn all",
    "VPNv4 Flowspec": "ipv4 flowspec",
    "VPNv6 Flowspec": "ipv6 flowspec",
}


class IOSDriver(NetworkDriver):
    """NAPALM Cisco IOS Handler."""

    def __init__(self, hostname, username, password, timeout=60, optional_args=None):
        """NAPALM Cisco IOS Handler."""
        if optional_args is None:
            optional_args = {}
        self.hostname = hostname
        self.username = username
        self.password = password
        self.timeout = timeout

        self.transport = optional_args.get("transport", "ssh")

        # Retrieve file names
        self.candidate_cfg = optional_args.get("candidate_cfg", "candidate_config.txt")
        self.merge_cfg = optional_args.get("merge_cfg", "merge_config.txt")
        self.rollback_cfg = optional_args.get("rollback_cfg", "rollback_config.txt")
        self.inline_transfer = optional_args.get("inline_transfer", False)
        if self.transport == "telnet":
            # Telnet only supports inline_transfer
            self.inline_transfer = True

        # None will cause autodetection of dest_file_system
        self._dest_file_system = optional_args.get("dest_file_system", None)
        self.auto_rollback_on_error = optional_args.get("auto_rollback_on_error", True)

        # Control automatic execution of 'file prompt quiet' for file operations
        self.auto_file_prompt = optional_args.get("auto_file_prompt", True)

        # Track whether 'file prompt quiet' has been changed by NAPALM.
        self.prompt_quiet_changed = False
        # Track whether 'file prompt quiet' is known to be configured
        self.prompt_quiet_configured = None

        self.netmiko_optional_args = netmiko_args(optional_args)

        # Set the default port if not set
        default_port = {"ssh": 22, "telnet": 23}
        self.netmiko_optional_args.setdefault("port", default_port[self.transport])

        self.device = None
        self.config_replace = False

        self.platform = "ios"
        self.profile = [self.platform]
        self.use_canonical_interface = optional_args.get("canonical_int", False)

    def open(self):
        """Open a connection to the device."""
        device_type = "cisco_ios"
        if self.transport == "telnet":
            device_type = "cisco_ios_telnet"
        self.device = self._netmiko_open(
            device_type, netmiko_optional_args=self.netmiko_optional_args
        )

    def _discover_file_system(self):
        try:
            return self.device._autodetect_fs()
        except Exception:
            msg = (
                "Netmiko _autodetect_fs failed (to workaround specify "
                "dest_file_system in optional_args.)"
            )
            raise CommandErrorException(msg)

    def close(self):
        """Close the connection to the device and do the necessary cleanup."""

        # Return file prompt quiet to the original state
        if self.auto_file_prompt and self.prompt_quiet_changed is True:
            self.device.send_config_set(["no file prompt quiet"])
            self.prompt_quiet_changed = False
            self.prompt_quiet_configured = False
        self._netmiko_close()

    def _send_command(self, command):
        """Wrapper for self.device.send.command().

        If command is a list will iterate through commands until valid command.
        """
        try:
            if isinstance(command, list):
                for cmd in command:
                    output = self.device.send_command(cmd)
                    if "% Invalid" not in output:
                        break
            else:
                output = self.device.send_command(command)
            return self._send_command_postprocess(output)
        except (socket.error, EOFError) as e:
            raise ConnectionClosedException(str(e))

    def is_alive(self):
        """Returns a flag with the state of the connection."""
        null = chr(0)
        if self.device is None:
            return {"is_alive": False}
        if self.transport == "telnet":
            try:
                # Try sending IAC + NOP (IAC is telnet way of sending command
                # IAC = Interpret as Command (it comes before the NOP)
                self.device.write_channel(telnetlib.IAC + telnetlib.NOP)
                return {"is_alive": True}
            except UnicodeDecodeError:
                # Netmiko logging bug (remove after Netmiko >= 1.4.3)
                return {"is_alive": True}
            except AttributeError:
                return {"is_alive": False}
        else:
            # SSH
            try:
                # Try sending ASCII null byte to maintain the connection alive
                self.device.write_channel(null)
                return {"is_alive": self.device.remote_conn.transport.is_active()}
            except (socket.error, EOFError):
                # If unable to send, we can tell for sure that the connection is unusable
                return {"is_alive": False}
        return {"is_alive": False}

    @staticmethod
    def _create_tmp_file(config):
        """Write temp file and for use with inline config and SCP."""
        tmp_dir = tempfile.gettempdir()
        rand_fname = py23_compat.text_type(uuid.uuid4())
        filename = os.path.join(tmp_dir, rand_fname)
        with open(filename, "wt") as fobj:
            fobj.write(config)
        return filename

    def _load_candidate_wrapper(
        self, source_file=None, source_config=None, dest_file=None, file_system=None
    ):
        """
        Transfer file to remote device for either merge or replace operations

        Returns (return_status, msg)
        """
        return_status = False
        msg = ""
        if source_file and source_config:
            raise ValueError("Cannot simultaneously set source_file and source_config")

        if source_config:
            if self.inline_transfer:
                (return_status, msg) = self._inline_tcl_xfer(
                    source_config=source_config,
                    dest_file=dest_file,
                    file_system=file_system,
                )
            else:
                # Use SCP
                tmp_file = self._create_tmp_file(source_config)
                (return_status, msg) = self._scp_file(
                    source_file=tmp_file, dest_file=dest_file, file_system=file_system
                )
                if tmp_file and os.path.isfile(tmp_file):
                    os.remove(tmp_file)
        if source_file:
            if self.inline_transfer:
                (return_status, msg) = self._inline_tcl_xfer(
                    source_file=source_file,
                    dest_file=dest_file,
                    file_system=file_system,
                )
            else:
                (return_status, msg) = self._scp_file(
                    source_file=source_file,
                    dest_file=dest_file,
                    file_system=file_system,
                )
        if not return_status:
            if msg == "":
                msg = "Transfer to remote device failed"
        return (return_status, msg)

    def load_replace_candidate(self, filename=None, config=None):
        """
        SCP file to device filesystem, defaults to candidate_config.

        Return None or raise exception
        """
        self.config_replace = True
        return_status, msg = self._load_candidate_wrapper(
            source_file=filename,
            source_config=config,
            dest_file=self.candidate_cfg,
            file_system=self.dest_file_system,
        )
        if not return_status:
            raise ReplaceConfigException(msg)

    def load_merge_candidate(self, filename=None, config=None):
        """
        SCP file to remote device.

        Merge configuration in: copy <file> running-config
        """
        self.config_replace = False
        return_status, msg = self._load_candidate_wrapper(
            source_file=filename,
            source_config=config,
            dest_file=self.merge_cfg,
            file_system=self.dest_file_system,
        )
        if not return_status:
            raise MergeConfigException(msg)

    def _normalize_compare_config(self, diff):
        """Filter out strings that should not show up in the diff."""
        ignore_strings = [
            "Contextual Config Diffs",
            "No changes were found",
            "ntp clock-period",
        ]
        if self.auto_file_prompt:
            ignore_strings.append("file prompt quiet")

        new_list = []
        for line in diff.splitlines():
            for ignore in ignore_strings:
                if ignore in line:
                    break
            else:  # nobreak
                new_list.append(line)
        return "\n".join(new_list)

    @staticmethod
    def _normalize_merge_diff_incr(diff):
        """Make the compare config output look better.

        Cisco IOS incremental-diff output

        No changes:
        !List of Commands:
        end
        !No changes were found
        """
        new_diff = []

        changes_found = False
        for line in diff.splitlines():
            if re.search(r"order-dependent line.*re-ordered", line):
                changes_found = True
            elif "No changes were found" in line:
                # IOS in the re-order case still claims "No changes were found"
                if not changes_found:
                    return ""
                else:
                    continue

            if line.strip() == "end":
                continue
            elif "List of Commands" in line:
                continue
            # Filter blank lines and prepend +sign
            elif line.strip():
                if re.search(r"^no\s+", line.strip()):
                    new_diff.append("-" + line)
                else:
                    new_diff.append("+" + line)
        return "\n".join(new_diff)

    @staticmethod
    def _normalize_merge_diff(diff):
        """Make compare_config() for merge look similar to replace config diff."""
        new_diff = []
        for line in diff.splitlines():
            # Filter blank lines and prepend +sign
            if line.strip():
                new_diff.append("+" + line)
        if new_diff:
            new_diff.insert(
                0, "! incremental-diff failed; falling back to echo of merge file"
            )
        else:
            new_diff.append("! No changes specified in merge file.")
        return "\n".join(new_diff)

    def compare_config(self):
        """
        show archive config differences <base_file> <new_file>.

        Default operation is to compare system:running-config to self.candidate_cfg
        """
        # Set defaults
        base_file = "running-config"
        base_file_system = "system:"
        if self.config_replace:
            new_file = self.candidate_cfg
        else:
            new_file = self.merge_cfg
        new_file_system = self.dest_file_system

        base_file_full = self._gen_full_path(
            filename=base_file, file_system=base_file_system
        )
        new_file_full = self._gen_full_path(
            filename=new_file, file_system=new_file_system
        )

        if self.config_replace:
            cmd = "show archive config differences {} {}".format(
                base_file_full, new_file_full
            )
            diff = self.device.send_command_expect(cmd)
            diff = self._normalize_compare_config(diff)
        else:
            # merge
            cmd = "show archive config incremental-diffs {} ignorecase".format(
                new_file_full
            )
            diff = self.device.send_command_expect(cmd)
            if "error code 5" in diff or "returned error 5" in diff:
                diff = (
                    "You have encountered the obscure 'error 5' message. This generally "
                    "means you need to add an 'end' statement to the end of your merge changes."
                )
            elif "% Invalid" not in diff:
                diff = self._normalize_merge_diff_incr(diff)
            else:
                cmd = "more {}".format(new_file_full)
                diff = self.device.send_command_expect(cmd)
                diff = self._normalize_merge_diff(diff)

        return diff.strip()

    def _file_prompt_quiet(f):
        """Decorator to toggle 'file prompt quiet' for methods that perform file operations."""

        @functools.wraps(f)
        def wrapper(self, *args, **kwargs):
            if not self.prompt_quiet_configured:
                if self.auto_file_prompt:
                    # disable file operation prompts
                    self.device.send_config_set(["file prompt quiet"])
                    self.prompt_quiet_changed = True
                    self.prompt_quiet_configured = True
                else:
                    # check if the command is already in the running-config
                    cmd = "file prompt quiet"
                    show_cmd = "show running-config | inc {}".format(cmd)
                    output = self.device.send_command_expect(show_cmd)
                    if cmd in output:
                        self.prompt_quiet_configured = True
                    else:
                        msg = (
                            "on-device file operations require prompts to be disabled. "
                            "Configure 'file prompt quiet' or set 'auto_file_prompt=True'"
                        )
                        raise CommandErrorException(msg)

            # call wrapped function
            return f(self, *args, **kwargs)

        return wrapper

    @_file_prompt_quiet
    def _commit_handler(self, cmd):
        """
        Special handler for hostname change on commit operation. Also handles username removal
        which prompts for confirmation (username removal prompts for each user...)
        """
        current_prompt = self.device.find_prompt().strip()
        terminating_char = current_prompt[-1]
        # Look for trailing pattern that includes '#' and '>'
        pattern1 = r"[>#{}]\s*$".format(terminating_char)
        # Handle special username removal pattern
        pattern2 = r".*all username.*confirm"
        patterns = r"(?:{}|{})".format(pattern1, pattern2)
        output = self.device.send_command_expect(cmd, expect_string=patterns)
        loop_count = 50
        new_output = output
        for i in range(loop_count):
            if re.search(pattern2, new_output):
                # Send confirmation if username removal
                new_output = self.device.send_command_timing(
                    "\n", strip_prompt=False, strip_command=False
                )
                output += new_output
            else:
                break
        # Reset base prompt in case hostname changed
        self.device.set_base_prompt()
        return output

    def commit_config(self, message=""):
        """
        If replacement operation, perform 'configure replace' for the entire config.

        If merge operation, perform copy <file> running-config.
        """
        if message:
            raise NotImplementedError(
                "Commit message not implemented for this platform"
            )
        # Always generate a rollback config on commit
        self._gen_rollback_cfg()

        if self.config_replace:
            # Replace operation
            filename = self.candidate_cfg
            cfg_file = self._gen_full_path(filename)
            if not self._check_file_exists(cfg_file):
                raise ReplaceConfigException("Candidate config file does not exist")
            if self.auto_rollback_on_error:
                cmd = "configure replace {} force revert trigger error".format(cfg_file)
            else:
                cmd = "configure replace {} force".format(cfg_file)
            output = self._commit_handler(cmd)
            if (
                ("original configuration has been successfully restored" in output)
                or ("error" in output.lower())
                or ("not a valid config file" in output.lower())
                or ("failed" in output.lower())
            ):
                msg = "Candidate config could not be applied\n{}".format(output)
                raise ReplaceConfigException(msg)
            elif "%Please turn config archive on" in output:
                msg = "napalm-ios replace() requires Cisco 'archive' feature to be enabled."
                raise ReplaceConfigException(msg)
        else:
            # Merge operation
            filename = self.merge_cfg
            cfg_file = self._gen_full_path(filename)
            if not self._check_file_exists(cfg_file):
                raise MergeConfigException("Merge source config file does not exist")
            cmd = "copy {} running-config".format(cfg_file)
            output = self._commit_handler(cmd)
            if "Invalid input detected" in output:
                self.rollback()
                err_header = "Configuration merge failed; automatic rollback attempted"
                merge_error = "{0}:\n{1}".format(err_header, output)
                raise MergeConfigException(merge_error)

        # After a commit - we no longer know whether this is configured or not.
        self.prompt_quiet_configured = None

        # Save config to startup (both replace and merge)
        output += self.device.save_config()

    def discard_config(self):
        """Discard loaded candidate configurations."""
        self._discard_config()

    @_file_prompt_quiet
    def _discard_config(self):
        """Set candidate_cfg to current running-config. Erase the merge_cfg file."""
        discard_candidate = "copy running-config {}".format(
            self._gen_full_path(self.candidate_cfg)
        )
        discard_merge = "copy null: {}".format(self._gen_full_path(self.merge_cfg))
        self.device.send_command_expect(discard_candidate)
        self.device.send_command_expect(discard_merge)

    def rollback(self):
        """Rollback configuration to filename or to self.rollback_cfg file."""
        filename = self.rollback_cfg
        cfg_file = self._gen_full_path(filename)
        if not self._check_file_exists(cfg_file):
            raise ReplaceConfigException("Rollback config file does not exist")
        cmd = "configure replace {} force".format(cfg_file)
        self.device.send_command_expect(cmd)

        # After a rollback - we no longer know whether this is configured or not.
        self.prompt_quiet_configured = None

        # Save config to startup
        self.device.save_config()

    def _inline_tcl_xfer(
        self, source_file=None, source_config=None, dest_file=None, file_system=None
    ):
        """
        Use Netmiko InlineFileTransfer (TCL) to transfer file or config to remote device.

        Return (status, msg)
        status = boolean
        msg = details on what happened
        """
        if source_file:
            return self._xfer_file(
                source_file=source_file,
                dest_file=dest_file,
                file_system=file_system,
                TransferClass=InLineTransfer,
            )
        if source_config:
            return self._xfer_file(
                source_config=source_config,
                dest_file=dest_file,
                file_system=file_system,
                TransferClass=InLineTransfer,
            )
        raise ValueError("File source not specified for transfer.")

    def _scp_file(self, source_file, dest_file, file_system):
        """
        SCP file to remote device.

        Return (status, msg)
        status = boolean
        msg = details on what happened
        """
        return self._xfer_file(
            source_file=source_file,
            dest_file=dest_file,
            file_system=file_system,
            TransferClass=FileTransfer,
        )

    def _xfer_file(
        self,
        source_file=None,
        source_config=None,
        dest_file=None,
        file_system=None,
        TransferClass=FileTransfer,
    ):
        """Transfer file to remote device.

        By default, this will use Secure Copy if self.inline_transfer is set, then will use
        Netmiko InlineTransfer method to transfer inline using either SSH or telnet (plus TCL
        onbox).

        Return (status, msg)
        status = boolean
        msg = details on what happened
        """
        if not source_file and not source_config:
            raise ValueError("File source not specified for transfer.")
        if not dest_file or not file_system:
            raise ValueError("Destination file or file system not specified.")

        if source_file:
            kwargs = dict(
                ssh_conn=self.device,
                source_file=source_file,
                dest_file=dest_file,
                direction="put",
                file_system=file_system,
            )
        elif source_config:
            kwargs = dict(
                ssh_conn=self.device,
                source_config=source_config,
                dest_file=dest_file,
                direction="put",
                file_system=file_system,
            )
        use_scp = True
        if self.inline_transfer:
            use_scp = False

        with TransferClass(**kwargs) as transfer:

            # Check if file already exists and has correct MD5
            if transfer.check_file_exists() and transfer.compare_md5():
                msg = "File already exists and has correct MD5: no SCP needed"
                return (True, msg)
            if not transfer.verify_space_available():
                msg = "Insufficient space available on remote device"
                return (False, msg)

            if use_scp:
                cmd = "ip scp server enable"
                show_cmd = "show running-config | inc {}".format(cmd)
                output = self.device.send_command_expect(show_cmd)
                if cmd not in output:
                    msg = (
                        "SCP file transfers are not enabled. "
                        "Configure 'ip scp server enable' on the device."
                    )
                    raise CommandErrorException(msg)

            # Transfer file
            transfer.transfer_file()

            # Compares MD5 between local-remote files
            if transfer.verify_file():
                msg = "File successfully transferred to remote device"
                return (True, msg)
            else:
                msg = "File transfer to remote device failed"
                return (False, msg)
            return (False, "")

    def _gen_full_path(self, filename, file_system=None):
        """Generate full file path on remote device."""
        if file_system is None:
            return "{}/{}".format(self.dest_file_system, filename)
        else:
            if ":" not in file_system:
                raise ValueError(
                    "Invalid file_system specified: {}".format(file_system)
                )
            return "{}/{}".format(file_system, filename)

    @_file_prompt_quiet
    def _gen_rollback_cfg(self):
        """Save a configuration that can be used for rollback."""
        cfg_file = self._gen_full_path(self.rollback_cfg)
        cmd = "copy running-config {}".format(cfg_file)
        self.device.send_command_expect(cmd)

    def _check_file_exists(self, cfg_file):
        """
        Check that the file exists on remote device using full path.

        cfg_file is full path i.e. flash:/file_name

        For example
        # dir flash:/candidate_config.txt
        Directory of flash:/candidate_config.txt

        33  -rw-        5592  Dec 18 2015 10:50:22 -08:00  candidate_config.txt

        return boolean
        """
        cmd = "dir {}".format(cfg_file)
        success_pattern = "Directory of {}".format(cfg_file)
        output = self.device.send_command_expect(cmd)
        if "Error opening" in output:
            return False
        elif success_pattern in output:
            return True
        return False

    @staticmethod
    def _send_command_postprocess(output):
        """
        Cleanup actions on send_command() for NAPALM getters.

        Remove "Load for five sec; one minute if in output"
        Remove "Time source is"
        """
        output = re.sub(r"^Load for five secs.*$", "", output, flags=re.M)
        output = re.sub(r"^Time source is .*$", "", output, flags=re.M)
        return output.strip()

    def get_optics(self):
        command = "show interfaces transceiver"
        output = self._send_command(command)

        # Check if router supports the command
        if "% Invalid input" in output:
            return {}

        # Formatting data into return data structure
        optics_detail = {}

        try:
            split_output = re.split(r"^---------.*$", output, flags=re.M)[1]
        except IndexError:
            return {}

        split_output = split_output.strip()

        for optics_entry in split_output.splitlines():
            # Example, Te1/0/1      34.6       3.29      -2.0      -3.5
            try:
                split_list = optics_entry.split()
            except ValueError:
                return {}

            int_brief = split_list[0]
            output_power = split_list[3]
            input_power = split_list[4]

            port = canonical_interface_name(int_brief)

            port_detail = {"physical_channels": {"channel": []}}

            # If interface is shutdown it returns "N/A" as output power.
            # Converting that to -100.0 float
            try:
                float(output_power)
            except ValueError:
                output_power = -100.0

            # Defaulting avg, min, max values to -100.0 since device does not
            # return these values
            optic_states = {
                "index": 0,
                "state": {
                    "input_power": {
                        "instant": (float(input_power) if "input_power" else -100.0),
                        "avg": -100.0,
                        "min": -100.0,
                        "max": -100.0,
                    },
                    "output_power": {
                        "instant": (float(output_power) if "output_power" else -100.0),
                        "avg": -100.0,
                        "min": -100.0,
                        "max": -100.0,
                    },
                    "laser_bias_current": {
                        "instant": 0.0,
                        "avg": 0.0,
                        "min": 0.0,
                        "max": 0.0,
                    },
                },
            }

            port_detail["physical_channels"]["channel"].append(optic_states)
            optics_detail[port] = port_detail

        return optics_detail

    def get_lldp_neighbors(self):
        """IOS implementation of get_lldp_neighbors."""

        def _device_id_expand(device_id, local_int_brief):
            """Device id might be abbreviated: try to obtain the full device id."""
            lldp_tmp = self._lldp_detail_parser(local_int_brief)
            device_id_new = lldp_tmp[3][0]
            # Verify abbreviated and full name are consistent
            if device_id_new[:20] == device_id:
                return device_id_new
            else:
                # Else return the original device_id
                return device_id

        lldp = {}
        neighbors_detail = self.get_lldp_neighbors_detail()
        for intf_name, entries in neighbors_detail.items():
            lldp[intf_name] = []
            for lldp_entry in entries:
                hostname = lldp_entry["remote_system_name"]
                # Match IOS behaviour of taking remote chassis ID
                # When lacking a system name (in show lldp neighbors)
                if not hostname:
                    hostname = lldp_entry["remote_chassis_id"]
                lldp_dict = {"port": lldp_entry["remote_port"], "hostname": hostname}
                lldp[intf_name].append(lldp_dict)

        return lldp

    def get_lldp_neighbors_detail(self, interface=""):
        lldp = {}
        lldp_interfaces = []

        if interface:
            command = "show lldp neighbors {} detail".format(interface)
        else:
            command = "show lldp neighbors detail"
        lldp_entries = self._send_command(command)
        lldp_entries = textfsm_extractor(
            self, "show_lldp_neighbors_detail", lldp_entries
        )

        if len(lldp_entries) == 0:
            return {}

        # Older IOS versions don't have 'Local Intf' defined in LLDP detail.
        # We need to get them from the non-detailed command
        # which is in the same sequence as the detailed output
        if not lldp_entries[0]["local_interface"]:
            if interface:
                command = "show lldp neighbors {}".format(interface)
            else:
                command = "show lldp neighbors"
            lldp_brief = self._send_command(command)
            lldp_interfaces = textfsm_extractor(self, "show_lldp_neighbors", lldp_brief)
            lldp_interfaces = [x["local_interface"] for x in lldp_interfaces]
            if len(lldp_interfaces) != len(lldp_entries):
                raise ValueError(
                    "LLDP neighbor count has changed between commands. "
                    "Interface: {}\nEntries: {}".format(lldp_interfaces, lldp_entries)
                )

        for idx, lldp_entry in enumerate(lldp_entries):
            local_intf = lldp_entry.pop("local_interface") or lldp_interfaces[idx]
            # Convert any 'not advertised' to an empty string
            for field in lldp_entry:
                if "not advertised" in lldp_entry[field]:
                    lldp_entry[field] = ""
            # Add field missing on IOS
            lldp_entry["parent_interface"] = ""
            # Translate the capability fields
            lldp_entry["remote_system_capab"] = transform_lldp_capab(
                lldp_entry["remote_system_capab"]
            )
            lldp_entry["remote_system_enable_capab"] = transform_lldp_capab(
                lldp_entry["remote_system_enable_capab"]
            )
            # Turn the interfaces into their long version
            local_intf = canonical_interface_name(local_intf)
            lldp.setdefault(local_intf, [])
            lldp[local_intf].append(lldp_entry)

        return lldp

    @staticmethod
    def parse_uptime(uptime_str):
        """
        Extract the uptime string from the given Cisco IOS Device.

        Return the uptime in seconds as an integer
        """
        # Initialize to zero
        (years, weeks, days, hours, minutes) = (0, 0, 0, 0, 0)

        uptime_str = uptime_str.strip()
        time_list = uptime_str.split(",")
        for element in time_list:
            if re.search("year", element):
                years = int(element.split()[0])
            elif re.search("week", element):
                weeks = int(element.split()[0])
            elif re.search("day", element):
                days = int(element.split()[0])
            elif re.search("hour", element):
                hours = int(element.split()[0])
            elif re.search("minute", element):
                minutes = int(element.split()[0])

        uptime_sec = (
            (years * YEAR_SECONDS)
            + (weeks * WEEK_SECONDS)
            + (days * DAY_SECONDS)
            + (hours * 3600)
            + (minutes * 60)
        )
        return uptime_sec

    def get_facts(self):
        """Return a set of facts from the devices."""
        # default values.
        vendor = "Cisco"
        uptime = -1
        serial_number, fqdn, os_version, hostname, domain_name = ("Unknown",) * 5

        # obtain output from device
        show_ver = self._send_command("show version")
        show_hosts = self._send_command("show hosts")
        show_ip_int_br = self._send_command("show ip interface brief")

        # uptime/serial_number/IOS version
        for line in show_ver.splitlines():
            if " uptime is " in line:
                hostname, uptime_str = line.split(" uptime is ")
                uptime = self.parse_uptime(uptime_str)
                hostname = hostname.strip()

            if "Processor board ID" in line:
                _, serial_number = line.split("Processor board ID ")
                serial_number = serial_number.strip()

            if re.search(r"Cisco IOS Software", line):
                try:
                    _, os_version = line.split("Cisco IOS Software, ")
                except ValueError:
                    # Handle 'Cisco IOS Software [Denali],'
                    _, os_version = re.split(r"Cisco IOS Software \[.*?\], ", line)
            elif re.search(r"IOS \(tm\).+Software", line):
                _, os_version = line.split("IOS (tm) ")

            os_version = os_version.strip()

        # Determine domain_name and fqdn
        for line in show_hosts.splitlines():
            if "Default domain" in line:
                _, domain_name = line.split("Default domain is ")
                domain_name = domain_name.strip()
                break
        if domain_name != "Unknown" and hostname != "Unknown":
            fqdn = "{}.{}".format(hostname, domain_name)

        # model filter
        try:
            match_model = re.search(
                r"Cisco (.+?) .+bytes of", show_ver, flags=re.IGNORECASE
            )
            model = match_model.group(1)
        except AttributeError:
            model = "Unknown"

        # interface_list filter
        interface_list = []
        show_ip_int_br = show_ip_int_br.strip()
        for line in show_ip_int_br.splitlines():
            if "Interface " in line:
                continue
            interface = line.split()[0]
            interface_list.append(interface)

        return {
            "uptime": uptime,
            "vendor": vendor,
            "os_version": py23_compat.text_type(os_version),
            "serial_number": py23_compat.text_type(serial_number),
            "model": py23_compat.text_type(model),
            "hostname": py23_compat.text_type(hostname),
            "fqdn": fqdn,
            "interface_list": interface_list,
        }

    def get_interfaces(self):
        """
        Get interface details.

        last_flapped is not implemented

        Example Output:

        {   u'Vlan1': {   'description': u'N/A',
                      'is_enabled': True,
                      'is_up': True,
                      'last_flapped': -1.0,
                      'mac_address': u'a493.4cc1.67a7',
                      'speed': 100},
        u'Vlan100': {   'description': u'Data Network',
                        'is_enabled': True,
                        'is_up': True,
                        'last_flapped': -1.0,
                        'mac_address': u'a493.4cc1.67a7',
                        'speed': 100},
        u'Vlan200': {   'description': u'Voice Network',
                        'is_enabled': True,
                        'is_up': True,
                        'last_flapped': -1.0,
                        'mac_address': u'a493.4cc1.67a7',
                        'speed': 100}}
        """
        # default values.
        last_flapped = -1.0

        command = "show interfaces"
        output = self._send_command(command)

        interface = description = mac_address = speed = speedformat = ""
        is_enabled = is_up = None

        interface_dict = {}
        for line in output.splitlines():

            interface_regex_1 = r"^(\S+?)\s+is\s+(.+?),\s+line\s+protocol\s+is\s+(\S+)"
            interface_regex_2 = r"^(\S+)\s+is\s+(up|down)"
            for pattern in (interface_regex_1, interface_regex_2):
                interface_match = re.search(pattern, line)
                if interface_match:
                    interface = interface_match.group(1)
                    status = interface_match.group(2)
                    try:
                        protocol = interface_match.group(3)
                    except IndexError:
                        protocol = ""
                    if "admin" in status.lower():
                        is_enabled = False
                    else:
                        is_enabled = True
                    if protocol:
                        is_up = bool("up" in protocol)
                    else:
                        is_up = bool("up" in status)
                    break

            mac_addr_regex = r"^\s+Hardware.+address\s+is\s+({})".format(MAC_REGEX)
            if re.search(mac_addr_regex, line):
                mac_addr_match = re.search(mac_addr_regex, line)
                mac_address = napalm.base.helpers.mac(mac_addr_match.groups()[0])

            descr_regex = r"^\s+Description:\s+(.+?)$"
            if re.search(descr_regex, line):
                descr_match = re.search(descr_regex, line)
                description = descr_match.groups()[0]

            speed_regex = r"^\s+MTU\s+\d+.+BW\s+(\d+)\s+([KMG]?b)"
            if re.search(speed_regex, line):
                speed_match = re.search(speed_regex, line)
                speed = speed_match.groups()[0]
                speedformat = speed_match.groups()[1]
                speed = float(speed)
                if speedformat.startswith("Kb"):
                    speed = speed / 1000.0
                elif speedformat.startswith("Gb"):
                    speed = speed * 1000
                speed = int(round(speed))

                if interface == "":
                    raise ValueError(
                        "Interface attributes were \
                                      found without any known interface"
                    )
                if not isinstance(is_up, bool) or not isinstance(is_enabled, bool):
                    raise ValueError("Did not correctly find the interface status")

                interface_dict[interface] = {
                    "is_enabled": is_enabled,
                    "is_up": is_up,
                    "description": description,
                    "mac_address": mac_address,
                    "last_flapped": last_flapped,
                    "speed": speed,
                }

                interface = description = mac_address = speed = speedformat = ""
                is_enabled = is_up = None

        return interface_dict

    def get_interfaces_ip(self):
        """
        Get interface ip details.

        Returns a dict of dicts

        Example Output:

        {   u'FastEthernet8': {   'ipv4': {   u'10.66.43.169': {   'prefix_length': 22}}},
            u'Loopback555': {   'ipv4': {   u'192.168.1.1': {   'prefix_length': 24}},
                                'ipv6': {   u'1::1': {   'prefix_length': 64},
                                            u'2001:DB8:1::1': {   'prefix_length': 64},
                                            u'2::': {   'prefix_length': 64},
                                            u'FE80::3': {   'prefix_length': 10}}},
            u'Tunnel0': {   'ipv4': {   u'10.63.100.9': {   'prefix_length': 24}}},
            u'Tunnel1': {   'ipv4': {   u'10.63.101.9': {   'prefix_length': 24}}},
            u'Vlan100': {   'ipv4': {   u'10.40.0.1': {   'prefix_length': 24},
                                        u'10.41.0.1': {   'prefix_length': 24},
                                        u'10.65.0.1': {   'prefix_length': 24}}},
            u'Vlan200': {   'ipv4': {   u'10.63.176.57': {   'prefix_length': 29}}}}
        """
        interfaces = {}

        command = "show ip interface"
        show_ip_interface = self._send_command(command)
        command = "show ipv6 interface"
        show_ipv6_interface = self._send_command(command)

        INTERNET_ADDRESS = r"\s+(?:Internet address is|Secondary address)"
        INTERNET_ADDRESS += r" (?P<ip>{})/(?P<prefix>\d+)".format(IPV4_ADDR_REGEX)
        LINK_LOCAL_ADDRESS = (
            r"\s+IPv6 is enabled, link-local address is (?P<ip>[a-fA-F0-9:]+)"
        )
        GLOBAL_ADDRESS = (
            r"\s+(?P<ip>[a-fA-F0-9:]+), subnet is (?:[a-fA-F0-9:]+)/(?P<prefix>\d+)"
        )

        interfaces = {}
        for line in show_ip_interface.splitlines():
            if len(line.strip()) == 0:
                continue
            if line[0] != " ":
                ipv4 = {}
                interface_name = line.split()[0]
            m = re.match(INTERNET_ADDRESS, line)
            if m:
                ip, prefix = m.groups()
                ipv4.update({ip: {"prefix_length": int(prefix)}})
                interfaces[interface_name] = {"ipv4": ipv4}

        if "% Invalid input detected at" not in show_ipv6_interface:
            for line in show_ipv6_interface.splitlines():
                if len(line.strip()) == 0:
                    continue
                if line[0] != " ":
                    ifname = line.split()[0]
                    ipv6 = {}
                    if ifname not in interfaces:
                        interfaces[ifname] = {"ipv6": ipv6}
                    else:
                        interfaces[ifname].update({"ipv6": ipv6})
                m = re.match(LINK_LOCAL_ADDRESS, line)
                if m:
                    ip = m.group(1)
                    ipv6.update({ip: {"prefix_length": 10}})
                m = re.match(GLOBAL_ADDRESS, line)
                if m:
                    ip, prefix = m.groups()
                    ipv6.update({ip: {"prefix_length": int(prefix)}})

        # Interface without ipv6 doesn't appears in show ipv6 interface
        return interfaces

    @staticmethod
    def bgp_time_conversion(bgp_uptime):
        """
        Convert string time to seconds.

        Examples
        00:14:23
        00:13:40
        00:00:21
        00:00:13
        00:00:49
        1d11h
        1d17h
        1w0d
        8w5d
        1y28w
        never
        """
        bgp_uptime = bgp_uptime.strip()
        uptime_letters = set(["w", "h", "d"])

        if "never" in bgp_uptime:
            return -1
        elif ":" in bgp_uptime:
            times = bgp_uptime.split(":")
            times = [int(x) for x in times]
            hours, minutes, seconds = times
            return (hours * 3600) + (minutes * 60) + seconds
        # Check if any letters 'w', 'h', 'd' are in the time string
        elif uptime_letters & set(bgp_uptime):
            form1 = r"(\d+)d(\d+)h"  # 1d17h
            form2 = r"(\d+)w(\d+)d"  # 8w5d
            form3 = r"(\d+)y(\d+)w"  # 1y28w
            match = re.search(form1, bgp_uptime)
            if match:
                days = int(match.group(1))
                hours = int(match.group(2))
                return (days * DAY_SECONDS) + (hours * 3600)
            match = re.search(form2, bgp_uptime)
            if match:
                weeks = int(match.group(1))
                days = int(match.group(2))
                return (weeks * WEEK_SECONDS) + (days * DAY_SECONDS)
            match = re.search(form3, bgp_uptime)
            if match:
                years = int(match.group(1))
                weeks = int(match.group(2))
                return (years * YEAR_SECONDS) + (weeks * WEEK_SECONDS)
        raise ValueError(
            "Unexpected value for BGP uptime string: {}".format(bgp_uptime)
        )

    def get_bgp_neighbors(self):
        """BGP neighbor information.

        Currently no VRF support. Supports both IPv4 and IPv6.
        """
        supported_afi = ["ipv4", "ipv6"]

        bgp_neighbor_data = dict()
        bgp_neighbor_data["global"] = {}

        # get summary output from device
        cmd_bgp_all_sum = "show bgp all summary"
        summary_output = self._send_command(cmd_bgp_all_sum).strip()

        # get neighbor output from device
        neighbor_output = ""
        for afi in supported_afi:
            cmd_bgp_neighbor = "show bgp %s unicast neighbors" % afi
            neighbor_output += self._send_command(cmd_bgp_neighbor).strip()
            # trailing newline required for parsing
            neighbor_output += "\n"

        # Regular expressions used for parsing BGP summary
        parse_summary = {
            "patterns": [
                # For address family: IPv4 Unicast
                {
                    "regexp": re.compile(r"^For address family: (?P<afi>\S+) "),
                    "record": False,
                },
                # Capture router_id and local_as values, e.g.:
                # BGP router identifier 10.0.1.1, local AS number 65000
                {
                    "regexp": re.compile(
                        r"^.* router identifier (?P<router_id>{}), "
                        r"local AS number (?P<local_as>{})".format(
                            IPV4_ADDR_REGEX, ASN_REGEX
                        )
                    ),
                    "record": False,
                },
                # Match neighbor summary row, capturing useful details and
                # discarding the 5 columns that we don't care about, e.g.:
                # Neighbor   V          AS MsgRcvd MsgSent   TblVer  InQ OutQ Up/Down  State/PfxRcd
                # 10.0.0.2   4       65000 1336020 64337701 1011343614    0    0 8w0d         3143
                {
                    "regexp": re.compile(
                        r"^\*?(?P<remote_addr>({})|({}))"
                        r"\s+\d+\s+(?P<remote_as>{})(\s+\S+){{5}}\s+"
                        r"(?P<uptime>(never)|\d+\S+)"
                        r"\s+(?P<accepted_prefixes>\d+)".format(
                            IPV4_ADDR_REGEX, IPV6_ADDR_REGEX, ASN_REGEX
                        )
                    ),
                    "record": True,
                },
                # Same as above, but for peer that are not Established, e.g.:
                # Neighbor      V       AS MsgRcvd MsgSent   TblVer  InQ OutQ Up/Down  State/PfxRcd
                # 192.168.0.2   4    65002       0       0        1    0    0 never    Active
                {
                    "regexp": re.compile(
                        r"^\*?(?P<remote_addr>({})|({}))"
                        r"\s+\d+\s+(?P<remote_as>{})(\s+\S+){{5}}\s+"
                        r"(?P<uptime>(never)|\d+\S+)\s+(?P<state>\D.*)".format(
                            IPV4_ADDR_REGEX, IPV6_ADDR_REGEX, ASN_REGEX
                        )
                    ),
                    "record": True,
                },
                # ipv6 peers often break accross rows because of the longer peer address,
                # match as above, but in separate expressions, e.g.:
                # Neighbor      V       AS MsgRcvd MsgSent   TblVer  InQ OutQ Up/Down  State/PfxRcd
                # 2001:DB8::4
                #               4    65004 9900690  612449 155362939    0    0 26w6d       36391
                {
                    "regexp": re.compile(
                        r"^\*?(?P<remote_addr>({})|({}))".format(
                            IPV4_ADDR_REGEX, IPV6_ADDR_REGEX
                        )
                    ),
                    "record": False,
                },
                {
                    "regexp": re.compile(
                        r"^\s+\d+\s+(?P<remote_as>{})(\s+\S+){{5}}\s+"
                        r"(?P<uptime>(never)|\d+\S+)"
                        r"\s+(?P<accepted_prefixes>\d+)".format(ASN_REGEX)
                    ),
                    "record": True,
                },
                # Same as above, but for peers that are not Established, e.g.:
                # Neighbor      V       AS MsgRcvd MsgSent   TblVer  InQ OutQ Up/Down  State/PfxRcd
                # 2001:DB8::3
                #               4    65003       0       0        1    0    0 never    Idle (Admin)
                {
                    "regexp": re.compile(
                        r"^\s+\d+\s+(?P<remote_as>{})(\s+\S+){{5}}\s+"
                        r"(?P<uptime>(never)|\d+\S+)\s+(?P<state>\D.*)".format(
                            ASN_REGEX
                        )
                    ),
                    "record": True,
                },
            ],
            "no_fill_fields": [
                "accepted_prefixes",
                "state",
                "uptime",
                "remote_as",
                "remote_addr",
            ],
        }

        parse_neighbors = {
            "patterns": [
                # Capture BGP neighbor is 10.0.0.2,  remote AS 65000, internal link
                {
                    "regexp": re.compile(
                        r"^BGP neighbor is (?P<remote_addr>({})|({})),"
                        r"\s+remote AS (?P<remote_as>{}).*".format(
                            IPV4_ADDR_REGEX, IPV6_ADDR_REGEX, ASN_REGEX
                        )
                    ),
                    "record": False,
                },
                # Capture description
                {
                    "regexp": re.compile(r"^\s+Description: (?P<description>.+)"),
                    "record": False,
                },
                # Capture remote_id, e.g.:
                # BGP version 4, remote router ID 10.0.1.2
                {
                    "regexp": re.compile(
                        r"^\s+BGP version \d+, remote router ID "
                        r"(?P<remote_id>{})".format(IPV4_ADDR_REGEX)
                    ),
                    "record": False,
                },
                # Capture state
                {
                    "regexp": re.compile(r"^\s+BGP state = (?P<state>\w+)"),
                    "record": False,
                },
                # Capture AFI and SAFI names, e.g.:
                # For address family: IPv4 Unicast
                {
                    "regexp": re.compile(r"^\s+For address family: (?P<afi>\S+) "),
                    "record": False,
                },
                # Capture current sent and accepted prefixes, e.g.:
                #     Prefixes Current:          637213       3142 (Consumes 377040 bytes)
                {
                    "regexp": re.compile(
                        r"^\s+Prefixes Current:\s+(?P<sent_prefixes>\d+)\s+"
                        r"(?P<accepted_prefixes>\d+).*"
                    ),
                    "record": False,
                },
                # Capture received_prefixes if soft-reconfig is enabled for the peer
                {
                    "regexp": re.compile(
                        r"^\s+Saved (soft-reconfig):.+(?P<received_prefixes>\d+).*"
                    ),
                    "record": True,
                },
                # Otherwise, use the following as an end of row marker
                {
                    "regexp": re.compile(r"^\s+Local Policy Denied Prefixes:.+"),
                    "record": True,
                },
            ],
            # fields that should not be "filled down" across table rows
            "no_fill_fields": [
                "received_prefixes",
                "accepted_prefixes",
                "sent_prefixes",
            ],
        }

        # Parse outputs into a list of dicts
        summary_data = []
        summary_data_entry = {}

        for line in summary_output.splitlines():
            # check for matches against each pattern
            for item in parse_summary["patterns"]:
                match = item["regexp"].match(line)
                if match:
                    # a match was found, so update the temp entry with the match's groupdict
                    summary_data_entry.update(match.groupdict())
                    if item["record"]:
                        # Record indicates the last piece of data has been obtained; move
                        # on to next entry
                        summary_data.append(copy.deepcopy(summary_data_entry))
                        # remove keys that are listed in no_fill_fields before the next pass
                        for field in parse_summary["no_fill_fields"]:
                            try:
                                del summary_data_entry[field]
                            except KeyError:
                                pass
                    break

        neighbor_data = []
        neighbor_data_entry = {}
        for line in neighbor_output.splitlines():
            # check for matches against each pattern
            for item in parse_neighbors["patterns"]:
                match = item["regexp"].match(line)
                if match:
                    # a match was found, so update the temp entry with the match's groupdict
                    neighbor_data_entry.update(match.groupdict())
                    if item["record"]:
                        # Record indicates the last piece of data has been obtained; move
                        # on to next entry
                        neighbor_data.append(copy.deepcopy(neighbor_data_entry))
                        # remove keys that are listed in no_fill_fields before the next pass
                        for field in parse_neighbors["no_fill_fields"]:
                            try:
                                del neighbor_data_entry[field]
                            except KeyError:
                                pass
                    break

        router_id = None

        for entry in summary_data:
            if not router_id:
                router_id = entry["router_id"]
            elif entry["router_id"] != router_id:
                raise ValueError

        # check the router_id looks like an ipv4 address
        router_id = napalm.base.helpers.ip(router_id, version=4)

        # add parsed data to output dict
        bgp_neighbor_data["global"]["router_id"] = router_id
        bgp_neighbor_data["global"]["peers"] = {}
        for entry in summary_data:
            remote_addr = napalm.base.helpers.ip(entry["remote_addr"])
            afi = entry["afi"].lower()
            # check that we're looking at a supported afi
            if afi not in supported_afi:
                continue
            # get neighbor_entry out of neighbor data
            neighbor_entry = None
            for neighbor in neighbor_data:
                if (
                    neighbor["afi"].lower() == afi
                    and napalm.base.helpers.ip(neighbor["remote_addr"]) == remote_addr
                ):
                    neighbor_entry = neighbor
                    break
            # check for proper session data for the afi
            if neighbor_entry is None:
                continue
            elif not isinstance(neighbor_entry, dict):
                raise ValueError(
                    msg="Couldn't find neighbor data for %s in afi %s"
                    % (remote_addr, afi)
                )

            # check for admin down state
            try:
                if "(Admin)" in entry["state"]:
                    is_enabled = False
                else:
                    is_enabled = True
            except KeyError:
                is_enabled = True

            # parse uptime value
            uptime = self.bgp_time_conversion(entry["uptime"])

            # BGP is up if state is Established
            is_up = "Established" in neighbor_entry["state"]

            # check whether session is up for address family and get prefix count
            try:
                accepted_prefixes = int(entry["accepted_prefixes"])
            except (ValueError, KeyError):
                accepted_prefixes = -1

            # Only parse neighbor detailed data if BGP session is-up
            if is_up:
                try:
                    # overide accepted_prefixes with neighbor data if possible (since that's newer)
                    accepted_prefixes = int(neighbor_entry["accepted_prefixes"])
                except (ValueError, KeyError):
                    pass

                # try to get received prefix count, otherwise set to accepted_prefixes
                received_prefixes = neighbor_entry.get(
                    "received_prefixes", accepted_prefixes
                )

                # try to get sent prefix count and convert to int, otherwise set to -1
                sent_prefixes = int(neighbor_entry.get("sent_prefixes", -1))
            else:
                received_prefixes = -1
                sent_prefixes = -1
                uptime = -1

            # get description
            try:
                description = py23_compat.text_type(neighbor_entry["description"])
            except KeyError:
                description = ""

            # check the remote router_id looks like an ipv4 address
            remote_id = napalm.base.helpers.ip(neighbor_entry["remote_id"], version=4)

            if remote_addr not in bgp_neighbor_data["global"]["peers"]:
                bgp_neighbor_data["global"]["peers"][remote_addr] = {
                    "local_as": napalm.base.helpers.as_number(entry["local_as"]),
                    "remote_as": napalm.base.helpers.as_number(entry["remote_as"]),
                    "remote_id": remote_id,
                    "is_up": is_up,
                    "is_enabled": is_enabled,
                    "description": description,
                    "uptime": uptime,
                    "address_family": {
                        afi: {
                            "received_prefixes": received_prefixes,
                            "accepted_prefixes": accepted_prefixes,
                            "sent_prefixes": sent_prefixes,
                        }
                    },
                }
            else:
                # found previous data for matching remote_addr, but for different afi
                existing = bgp_neighbor_data["global"]["peers"][remote_addr]
                assert afi not in existing["address_family"]
                # compare with existing values and croak if they don't match
                assert existing["local_as"] == napalm.base.helpers.as_number(
                    entry["local_as"]
                )
                assert existing["remote_as"] == napalm.base.helpers.as_number(
                    entry["remote_as"]
                )
                assert existing["remote_id"] == remote_id
                assert existing["is_enabled"] == is_enabled
                assert existing["description"] == description
                # merge other values in a sane manner
                existing["is_up"] = existing["is_up"] or is_up
                existing["uptime"] = max(existing["uptime"], uptime)
                existing["address_family"][afi] = {
                    "received_prefixes": received_prefixes,
                    "accepted_prefixes": accepted_prefixes,
                    "sent_prefixes": sent_prefixes,
                }
        return bgp_neighbor_data

    def get_bgp_neighbors_detail(self, neighbor_address=""):
        bgp_detail = defaultdict(lambda: defaultdict(lambda: []))

        raw_bgp_sum = self._send_command("show ip bgp all sum").strip()
        bgp_sum = napalm.base.helpers.textfsm_extractor(
            self, "ip_bgp_all_sum", raw_bgp_sum
        )
        for neigh in bgp_sum:
            if neighbor_address and neighbor_address != neigh["neighbor"]:
                continue
            raw_bgp_neigh = self._send_command(
                "show ip bgp {} neigh {}".format(
                    AFI_COMMAND_MAP[neigh["addr_family"]], neigh["neighbor"]
                )
            )
            bgp_neigh = napalm.base.helpers.textfsm_extractor(
                self, "ip_bgp_neigh", raw_bgp_neigh
            )[0]
            details = {
                "up": neigh["up"] != "never",
                "local_as": napalm.base.helpers.as_number(neigh["local_as"]),
                "remote_as": napalm.base.helpers.as_number(neigh["remote_as"]),
                "router_id": napalm.base.helpers.ip(bgp_neigh["router_id"])
                if bgp_neigh["router_id"]
                else "",
                "local_address": napalm.base.helpers.ip(bgp_neigh["local_address"])
                if bgp_neigh["local_address"]
                else "",
                "local_address_configured": False,
                "local_port": napalm.base.helpers.as_number(bgp_neigh["local_port"])
                if bgp_neigh["local_port"]
                else 0,
                "routing_table": bgp_neigh["vrf"] if bgp_neigh["vrf"] else "global",
                "remote_address": napalm.base.helpers.ip(bgp_neigh["neighbor"]),
                "remote_port": napalm.base.helpers.as_number(bgp_neigh["remote_port"])
                if bgp_neigh["remote_port"]
                else 0,
                "multihop": False,
                "multipath": False,
                "remove_private_as": False,
                "import_policy": "",
                "export_policy": "",
                "input_messages": napalm.base.helpers.as_number(
                    bgp_neigh["msg_total_in"]
                )
                if bgp_neigh["msg_total_in"]
                else 0,
                "output_messages": napalm.base.helpers.as_number(
                    bgp_neigh["msg_total_out"]
                )
                if bgp_neigh["msg_total_out"]
                else 0,
                "input_updates": napalm.base.helpers.as_number(
                    bgp_neigh["msg_update_in"]
                )
                if bgp_neigh["msg_update_in"]
                else 0,
                "output_updates": napalm.base.helpers.as_number(
                    bgp_neigh["msg_update_out"]
                )
                if bgp_neigh["msg_update_out"]
                else 0,
                "messages_queued_out": napalm.base.helpers.as_number(neigh["out_q"]),
                "connection_state": bgp_neigh["bgp_state"],
                "previous_connection_state": "",
                "last_event": "",
                "suppress_4byte_as": (
                    bgp_neigh["four_byte_as"] != "advertised and received"
                    if bgp_neigh["four_byte_as"]
                    else False
                ),
                "local_as_prepend": False,
                "holdtime": napalm.base.helpers.as_number(bgp_neigh["holdtime"])
                if bgp_neigh["holdtime"]
                else 0,
                "configured_holdtime": 0,
                "keepalive": napalm.base.helpers.as_number(bgp_neigh["keepalive"])
                if bgp_neigh["keepalive"]
                else 0,
                "configured_keepalive": 0,
                "active_prefix_count": 0,
                "received_prefix_count": 0,
                "accepted_prefix_count": 0,
                "suppressed_prefix_count": 0,
                "advertised_prefix_count": 0,
                "flap_count": 0,
            }

            bgp_neigh_afi = napalm.base.helpers.textfsm_extractor(
                self, "ip_bgp_neigh_afi", raw_bgp_neigh
            )
            if len(bgp_neigh_afi) > 1:
                bgp_neigh_afi = bgp_neigh_afi[1]
                details.update(
                    {
                        "local_address_configured": bgp_neigh_afi["local_addr_conf"]
                        != "",
                        "multipath": bgp_neigh_afi["multipaths"] != "0",
                        "import_policy": bgp_neigh_afi["policy_in"],
                        "export_policy": bgp_neigh_afi["policy_out"],
                        "last_event": (
                            bgp_neigh_afi["last_event"]
                            if bgp_neigh_afi["last_event"] != "never"
                            else ""
                        ),
                        "active_prefix_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["bestpaths"]
                        ),
                        "received_prefix_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["prefix_curr_in"]
                        )
                        + napalm.base.helpers.as_number(
                            bgp_neigh_afi["rejected_prefix_in"]
                        ),
                        "accepted_prefix_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["prefix_curr_in"]
                        ),
                        "suppressed_prefix_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["rejected_prefix_in"]
                        ),
                        "advertised_prefix_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["prefix_curr_out"]
                        ),
                        "flap_count": napalm.base.helpers.as_number(
                            bgp_neigh_afi["flap_count"]
                        ),
                    }
                )
            else:
                bgp_neigh_afi = bgp_neigh_afi[0]
                details.update(
                    {
                        "import_policy": bgp_neigh_afi["policy_in"],
                        "export_policy": bgp_neigh_afi["policy_out"],
                    }
                )
            bgp_detail[details["routing_table"]][details["remote_as"]].append(details)
        return bgp_detail

    def get_interfaces_counters(self):
        """
        Return interface counters and errors.

        'tx_errors': int,
        'rx_errors': int,
        'tx_discards': int,
        'rx_discards': int,
        'tx_octets': int,
        'rx_octets': int,
        'tx_unicast_packets': int,
        'rx_unicast_packets': int,
        'tx_multicast_packets': int,
        'rx_multicast_packets': int,
        'tx_broadcast_packets': int,
        'rx_broadcast_packets': int,

        Currently doesn't determine output broadcasts, multicasts
        """
        counters = {}
        command = "show interfaces"
        output = self._send_command(command)
        sh_int_sum_cmd = "show interface summary"
        sh_int_sum_cmd_out = self._send_command(sh_int_sum_cmd)

        # Break output into per-interface sections
        interface_strings = re.split(r".* line protocol is .*", output, flags=re.M)
        header_strings = re.findall(r".* line protocol is .*", output, flags=re.M)

        empty = interface_strings.pop(0).strip()
        if empty:
            raise ValueError("Unexpected output from: {}".format(command))

        # Parse out the interface names
        intf = []
        for intf_line in header_strings:
            interface, _ = re.split(r" is .* line protocol is ", intf_line)
            intf.append(interface.strip())

        if len(intf) != len(interface_strings):
            raise ValueError("Unexpected output from: {}".format(command))

        # Re-join interface names with interface strings
        for interface, interface_str in zip(intf, interface_strings):
            counters.setdefault(interface, {})
            for line in interface_str.splitlines():
                if "packets input" in line:
                    # '0 packets input, 0 bytes, 0 no buffer'
                    match = re.search(r"(\d+) packets input.* (\d+) bytes", line)
                    counters[interface]["rx_unicast_packets"] = int(match.group(1))
                    counters[interface]["rx_octets"] = int(match.group(2))
                elif "broadcast" in line:
                    # 'Received 0 broadcasts (0 multicasts)'
                    # 'Received 264071 broadcasts (39327 IP multicasts)'
                    # 'Received 338 broadcasts, 0 runts, 0 giants, 0 throttles'
                    match = re.search(
                        r"Received (\d+) broadcasts.*(\d+).*multicasts", line
                    )
                    alt_match = re.search(r"Received (\d+) broadcasts.*", line)
                    if match:
                        counters[interface]["rx_broadcast_packets"] = int(
                            match.group(1)
                        )
                        counters[interface]["rx_multicast_packets"] = int(
                            match.group(2)
                        )
                    elif alt_match:
                        counters[interface]["rx_broadcast_packets"] = int(
                            alt_match.group(1)
                        )
                        counters[interface]["rx_multicast_packets"] = -1
                    else:
                        counters[interface]["rx_broadcast_packets"] = -1
                        counters[interface]["rx_multicast_packets"] = -1
                elif "packets output" in line:
                    # '0 packets output, 0 bytes, 0 underruns'
                    match = re.search(r"(\d+) packets output.* (\d+) bytes", line)
                    counters[interface]["tx_unicast_packets"] = int(match.group(1))
                    counters[interface]["tx_octets"] = int(match.group(2))
                    counters[interface]["tx_broadcast_packets"] = -1
                    counters[interface]["tx_multicast_packets"] = -1
                elif "input errors" in line:
                    # '0 input errors, 0 CRC, 0 frame, 0 overrun, 0 ignored'
                    match = re.search(r"(\d+) input errors", line)
                    counters[interface]["rx_errors"] = int(match.group(1))
                    counters[interface]["rx_discards"] = -1
                elif "output errors" in line:
                    # '0 output errors, 0 collisions, 1 interface resets'
                    match = re.search(r"(\d+) output errors", line)
                    counters[interface]["tx_errors"] = int(match.group(1))
                    counters[interface]["tx_discards"] = -1
            for line in sh_int_sum_cmd_out.splitlines():
                if interface in line:
                    # Line is tabular output with columns
                    # Interface  IHQ  IQD  OHQ  OQD  RXBS  RXPS  TXBS  TXPS  TRTL
                    # where columns (excluding interface) are integers
                    regex = (
                        r"\b"
                        + interface
                        + r"\b\s+(\d+)\s+(?P<IQD>\d+)\s+(\d+)"
                        + r"\s+(?P<OQD>\d+)\s+(\d+)\s+(\d+)"
                        + r"\s+(\d+)\s+(\d+)\s+(\d+)"
                    )
                    match = re.search(regex, line)
                    if match:
                        counters[interface]["rx_discards"] = int(match.group("IQD"))
                        counters[interface]["tx_discards"] = int(match.group("OQD"))

        return counters

    def get_environment(self):
        """
        Get environment facts.

        power and fan are currently not implemented
        cpu is using 1-minute average
        cpu hard-coded to cpu0 (i.e. only a single CPU)
        """
        environment = {}
        cpu_cmd = "show proc cpu"
        mem_cmd = "show memory statistics"
        temp_cmd = "show env temperature status"

        output = self._send_command(cpu_cmd)
        environment.setdefault("cpu", {})
        environment["cpu"][0] = {}
        environment["cpu"][0]["%usage"] = 0.0
        for line in output.splitlines():
            if "CPU utilization" in line:
                # CPU utilization for five seconds: 2%/0%; one minute: 2%; five minutes: 1%
                cpu_regex = r"^.*one minute: (\d+)%; five.*$"
                match = re.search(cpu_regex, line)
                environment["cpu"][0]["%usage"] = float(match.group(1))
                break

        output = self._send_command(mem_cmd)
        for line in output.splitlines():
            if "Processor" in line:
                _, _, proc_total_mem, proc_used_mem, _ = line.split()[:5]
            elif "I/O" in line or "io" in line:
                _, _, io_total_mem, io_used_mem, _ = line.split()[:5]
        total_mem = int(proc_total_mem) + int(io_total_mem)
        used_mem = int(proc_used_mem) + int(io_used_mem)
        environment.setdefault("memory", {})
        environment["memory"]["used_ram"] = used_mem
        environment["memory"]["available_ram"] = total_mem

        environment.setdefault("temperature", {})
        re_temp_value = re.compile("(.*) Temperature Value")
        # The 'show env temperature status' is not ubiquitous in Cisco IOS
        output = self._send_command(temp_cmd)
        if "% Invalid" not in output:
            for line in output.splitlines():
                m = re_temp_value.match(line)
                if m is not None:
                    temp_name = m.group(1).lower()
                    temp_value = float(line.split(":")[1].split()[0])
                    env_value = {
                        "is_alert": False,
                        "is_critical": False,
                        "temperature": temp_value,
                    }
                    environment["temperature"][temp_name] = env_value
                elif "Yellow Threshold" in line:
                    system_temp_alert = float(line.split(":")[1].split()[0])
                    if temp_value > system_temp_alert:
                        env_value["is_alert"] = True
                elif "Red Threshold" in line:
                    system_temp_crit = float(line.split(":")[1].split()[0])
                    if temp_value > system_temp_crit:
                        env_value["is_critical"] = True
        else:
            env_value = {"is_alert": False, "is_critical": False, "temperature": -1.0}
            environment["temperature"]["invalid"] = env_value

        # Initialize 'power' and 'fan' to default values (not implemented)
        environment.setdefault("power", {})
        environment["power"]["invalid"] = {
            "status": True,
            "output": -1.0,
            "capacity": -1.0,
        }
        environment.setdefault("fans", {})
        environment["fans"]["invalid"] = {"status": True}

        return environment

    def get_arp_table(self, vrf=""):
        """
        Get arp table information.

        Return a list of dictionaries having the following set of keys:
            * interface (string)
            * mac (string)
            * ip (string)
            * age (float)

        For example::
            [
                {
                    'interface' : 'MgmtEth0/RSP0/CPU0/0',
                    'mac'       : '5c:5e:ab:da:3c:f0',
                    'ip'        : '172.17.17.1',
                    'age'       : 1454496274.84
                },
                {
                    'interface': 'MgmtEth0/RSP0/CPU0/0',
                    'mac'       : '66:0e:94:96:e0:ff',
                    'ip'        : '172.17.17.2',
                    'age'       : 1435641582.49
                }
            ]
        """
        if vrf:
            msg = "VRF support has not been added for this getter on this platform."
            raise NotImplementedError(msg)

        arp_table = []

        command = "show arp | exclude Incomplete"
        output = self._send_command(command)

        # Skip the first line which is a header
        output = output.split("\n")
        output = output[1:]

        for line in output:
            if len(line) == 0:
                return {}
            if len(line.split()) == 5:
                # Static ARP entries have no interface
                # Internet  10.0.0.1                -   0010.2345.1cda  ARPA
                interface = ""
                protocol, address, age, mac, eth_type = line.split()
            elif len(line.split()) == 6:
                protocol, address, age, mac, eth_type, interface = line.split()
            else:
                raise ValueError("Unexpected output from: {}".format(line.split()))

            try:
                if age == "-":
                    age = 0
                age = float(age)
            except ValueError:
                raise ValueError("Unable to convert age value to float: {}".format(age))

            # Validate we matched correctly
            if not re.search(RE_IPADDR, address):
                raise ValueError("Invalid IP Address detected: {}".format(address))
            if not re.search(RE_MAC, mac):
                raise ValueError("Invalid MAC Address detected: {}".format(mac))
            entry = {
                "interface": interface,
                "mac": napalm.base.helpers.mac(mac),
                "ip": address,
                "age": age,
            }
            arp_table.append(entry)
        return arp_table

    def cli(self, commands):
        """
        Execute a list of commands and return the output in a dictionary format using the command
        as the key.

        Example input:
        ['show clock', 'show calendar']

        Output example:
        {   'show calendar': u'22:02:01 UTC Thu Feb 18 2016',
            'show clock': u'*22:01:51.165 UTC Thu Feb 18 2016'}

        """
        cli_output = dict()
        if type(commands) is not list:
            raise TypeError("Please enter a valid list of commands!")

        for command in commands:
            output = self._send_command(command)
            cli_output.setdefault(command, {})
            cli_output[command] = output

        return cli_output

    def get_ntp_peers(self):
        """Implementation of get_ntp_peers for IOS."""
        ntp_stats = self.get_ntp_stats()

        return {
            ntp_peer.get("remote"): {}
            for ntp_peer in ntp_stats
            if ntp_peer.get("remote")
        }

    def get_ntp_servers(self):
        """Implementation of get_ntp_servers for IOS.

        Returns the NTP servers configuration as dictionary.
        The keys of the dictionary represent the IP Addresses of the servers.
        Inner dictionaries do not have yet any available keys.
        Example::
            {
                '192.168.0.1': {},
                '17.72.148.53': {},
                '37.187.56.220': {},
                '162.158.20.18': {}
            }
        """
        ntp_servers = {}
        command = "show run | include ntp server"
        output = self._send_command(command)

        for line in output.splitlines():
            split_line = line.split()
            if "vrf" == split_line[2]:
                ntp_servers[split_line[4]] = {}
            else:
                ntp_servers[split_line[2]] = {}

        return ntp_servers

    def get_ntp_stats(self):
        """Implementation of get_ntp_stats for IOS."""
        ntp_stats = []

        command = "show ntp associations"
        output = self._send_command(command)

        for line in output.splitlines():
            # Skip first two lines and last line of command output
            if line == "" or "address" in line or "sys.peer" in line:
                continue

            if "%NTP is not enabled" in line:
                return []

            elif len(line.split()) == 9:
                address, ref_clock, st, when, poll, reach, delay, offset, disp = (
                    line.split()
                )
                address_regex = re.match(r"(\W*)([0-9.*]*)", address)
            try:
                ntp_stats.append(
                    {
                        "remote": py23_compat.text_type(address_regex.group(2)),
                        "synchronized": ("*" in address_regex.group(1)),
                        "referenceid": py23_compat.text_type(ref_clock),
                        "stratum": int(st),
                        "type": "-",
                        "when": py23_compat.text_type(when),
                        "hostpoll": int(poll),
                        "reachability": int(reach),
                        "delay": float(delay),
                        "offset": float(offset),
                        "jitter": float(disp),
                    }
                )
            except Exception:
                continue

        return ntp_stats

    def get_mac_address_table(self):
        """
        Returns a lists of dictionaries. Each dictionary represents an entry in the MAC Address
        Table, having the following keys
            * mac (string)
            * interface (string)
            * vlan (int)
            * active (boolean)
            * static (boolean)
            * moves (int)
            * last_move (float)

        Format1:
        Destination Address  Address Type  VLAN  Destination Port
        -------------------  ------------  ----  --------------------
        6400.f1cf.2cc6          Dynamic       1     Wlan-GigabitEthernet0

        Cat 6500:
        Legend: * - primary entry
                age - seconds since last seen
                n/a - not available

          vlan   mac address     type    learn     age              ports
        ------+----------------+--------+-----+----------+--------------------------
        *  999  1111.2222.3333   dynamic  Yes          0   Port-channel1
           999  1111.2222.3333   dynamic  Yes          0   Port-channel1

        Cat 4948
        Unicast Entries
         vlan   mac address     type        protocols               port
        -------+---------------+--------+---------------------+--------------------
         999    1111.2222.3333   dynamic ip                    Port-channel1

        Cat 2960
        Mac Address Table
        -------------------------------------------

        Vlan    Mac Address       Type        Ports
        ----    -----------       --------    -----
        All    1111.2222.3333    STATIC      CPU
        """

        RE_MACTABLE_DEFAULT = r"^" + MAC_REGEX
        RE_MACTABLE_6500_1 = r"^\*\s+{}\s+{}\s+".format(
            VLAN_REGEX, MAC_REGEX
        )  # 7 fields
        RE_MACTABLE_6500_2 = r"^{}\s+{}\s+".format(VLAN_REGEX, MAC_REGEX)  # 6 fields
        RE_MACTABLE_6500_3 = r"^\s{51}\S+"  # Fill down prior
        RE_MACTABLE_6500_4 = r"^R\s+{}\s+.*Router".format(
            VLAN_REGEX, MAC_REGEX
        )  # Router field
        RE_MACTABLE_6500_5 = r"^R\s+N/A\s+{}.*Router".format(
            MAC_REGEX
        )  # Router skipped
        RE_MACTABLE_4500_1 = r"^{}\s+{}\s+".format(VLAN_REGEX, MAC_REGEX)  # 5 fields
        RE_MACTABLE_4500_2 = r"^\s{32,34}\S+"  # Fill down prior
        RE_MACTABLE_4500_3 = r"^{}\s+{}\s+".format(
            INT_REGEX, MAC_REGEX
        )  # Matches PHY int
        RE_MACTABLE_2960_1 = r"^All\s+{}".format(MAC_REGEX)
        RE_MACTABLE_GEN_1 = r"^{}\s+{}\s+".format(
            VLAN_REGEX, MAC_REGEX
        )  # 4 fields-2960/4500

        def process_mac_fields(vlan, mac, mac_type, interface):
            """Return proper data for mac address fields."""
            if mac_type.lower() in ["self", "static", "system"]:
                static = True
                if vlan.lower() == "all":
                    vlan = 0
                if (
                    interface.lower() == "cpu"
                    or re.search(r"router", interface.lower())
                    or re.search(r"switch", interface.lower())
                ):
                    interface = ""
            else:
                static = False

            return {
                "mac": napalm.base.helpers.mac(mac),
                "interface": self._canonical_int(interface),
                "vlan": int(vlan),
                "static": static,
                "active": True,
                "moves": -1,
                "last_move": -1.0,
            }

        mac_address_table = []
        command = IOS_COMMANDS["show_mac_address"]
        output = self._send_command(command)

        # Skip the header lines
        output = re.split(r"^----.*", output, flags=re.M)[1:]
        output = "\n".join(output).strip()
        # Strip any leading asterisks
        output = re.sub(r"^\*", "", output, flags=re.M)
        fill_down_vlan = fill_down_mac = fill_down_mac_type = ""
        for line in output.splitlines():
            # Cat6500 one off and 4500 multicast format
            if re.search(RE_MACTABLE_6500_3, line) or re.search(
                RE_MACTABLE_4500_2, line
            ):
                interface = line.strip()
                if "," in interface:
                    interfaces = interface.split(",")
                else:
                    interfaces = [interface]
                for single_interface in interfaces:
                    mac_address_table.append(
                        process_mac_fields(
                            fill_down_vlan,
                            fill_down_mac,
                            fill_down_mac_type,
                            single_interface,
                        )
                    )
                continue
            line = line.strip()
            if line == "":
                continue
            if re.search(r"^---", line):
                # Convert any '---' to VLAN 0
                line = re.sub(r"^---", "0", line, flags=re.M)

            # Format1
            if re.search(RE_MACTABLE_DEFAULT, line):
                if len(line.split()) == 4:
                    mac, mac_type, vlan, interface = line.split()
                    mac_address_table.append(
                        process_mac_fields(vlan, mac, mac_type, interface)
                    )
                else:
                    raise ValueError("Unexpected output from: {}".format(line.split()))
            # Cat6500 format
            elif (
                re.search(RE_MACTABLE_6500_1, line)
                or re.search(RE_MACTABLE_6500_2, line)
            ) and len(line.split()) >= 6:
                if len(line.split()) == 7:
                    _, vlan, mac, mac_type, _, _, interface = line.split()
                elif len(line.split()) == 6:
                    vlan, mac, mac_type, _, _, interface = line.split()
                if "," in interface:
                    interfaces = interface.split(",")
                    fill_down_vlan = vlan
                    fill_down_mac = mac
                    fill_down_mac_type = mac_type
                    for single_interface in interfaces:
                        mac_address_table.append(
                            process_mac_fields(vlan, mac, mac_type, single_interface)
                        )
                else:
                    mac_address_table.append(
                        process_mac_fields(vlan, mac, mac_type, interface)
                    )
            # Cat4500 format
            elif re.search(RE_MACTABLE_4500_1, line) and len(line.split()) == 5:
                vlan, mac, mac_type, _, interface = line.split()
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface)
                )
            # Cat4500 w/PHY interface in Mac Table. Vlan will be -1.
            elif re.search(RE_MACTABLE_4500_3, line) and len(line.split()) == 5:
                interface, mac, mac_type, _, _ = line.split()
                interface = canonical_interface_name(interface)
                vlan = "-1"
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface)
                )
            # Cat2960 format - ignore extra header line
            elif re.search(r"^Vlan\s+Mac Address\s+", line):
                continue
            # Cat2960 format (Cat4500 format multicast entries)
            elif (
                re.search(RE_MACTABLE_2960_1, line)
                or re.search(RE_MACTABLE_GEN_1, line)
            ) and len(line.split()) == 4:
                vlan, mac, mac_type, interface = line.split()
                if "," in interface:
                    interfaces = interface.split(",")
                    fill_down_vlan = vlan
                    fill_down_mac = mac
                    fill_down_mac_type = mac_type
                    for single_interface in interfaces:
                        mac_address_table.append(
                            process_mac_fields(vlan, mac, mac_type, single_interface)
                        )
                else:
                    mac_address_table.append(
                        process_mac_fields(vlan, mac, mac_type, interface)
                    )
            # 4500 in case of unused Vlan 1.
            elif re.search(RE_MACTABLE_4500_1, line) and len(line.split()) == 3:
                vlan, mac, mac_type = line.split()
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface="")
                )
            # 4500 w/PHY interface in Multicast table. Vlan will be -1.
            elif re.search(RE_MACTABLE_4500_3, line) and len(line.split()) == 4:
                vlan, mac, mac_type, interface = line.split()
                vlan = "-1"
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface)
                )
            elif re.search(RE_MACTABLE_6500_4, line) and len(line.split()) == 7:
                line = re.sub(r"^R\s+", "", line)
                vlan, mac, mac_type, _, _, interface = line.split()
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface)
                )
                continue
            elif re.search(RE_MACTABLE_6500_5, line):
                line = re.sub(r"^R\s+", "", line)
                vlan, mac, mac_type, _, _, interface = line.split()
                # Convert 'N/A' VLAN to to 0
                vlan = re.sub(r"N/A", "0", vlan)
                mac_address_table.append(
                    process_mac_fields(vlan, mac, mac_type, interface)
                )
                continue
            elif re.search(r"Total Mac Addresses", line):
                continue
            elif re.search(r"Multicast Entries", line):
                continue
            elif re.search(r"vlan.*mac.*address.*type.*", line):
                continue
            else:
                raise ValueError("Unexpected output from: {}".format(repr(line)))

        return mac_address_table

    def get_probes_config(self):
        probes = {}
        probes_regex = (
            r"ip\s+sla\s+(?P<id>\d+)\n"
            r"\s+(?P<probe_type>\S+)\s+(?P<probe_args>.*\n).*"
            r"\s+tag\s+(?P<name>\S+)\n.*"
            r"\s+history\s+buckets-kept\s+(?P<probe_count>\d+)\n.*"
            r"\s+frequency\s+(?P<interval>\d+)$"
        )
        probe_args = {
            "icmp-echo": r"^(?P<target>\S+)\s+source-(?:ip|interface)\s+(?P<source>\S+)$"
        }
        probe_type_map = {"icmp-echo": "icmp-ping"}
        command = "show run | include ip sla [0-9]"
        output = self._send_command(command)
        for match in re.finditer(probes_regex, output, re.M):
            probe = match.groupdict()
            if probe["probe_type"] not in probe_args:
                # Probe type not supported yet
                continue
            probe_args_match = re.match(
                probe_args[probe["probe_type"]], probe["probe_args"]
            )
            probe_data = probe_args_match.groupdict()
            probes[probe["id"]] = {
                probe["name"]: {
                    "probe_type": probe_type_map[probe["probe_type"]],
                    "target": probe_data["target"],
                    "source": probe_data["source"],
                    "probe_count": int(probe["probe_count"]),
                    "test_interval": int(probe["interval"]),
                }
            }

        return probes

    def get_snmp_information(self):
        """
        Returns a dict of dicts

        Example Output:

        {   'chassis_id': u'Asset Tag 54670',
        'community': {   u'private': {   'acl': u'12', 'mode': u'rw'},
                         u'public': {   'acl': u'11', 'mode': u'ro'},
                         u'public_named_acl': {   'acl': u'ALLOW-SNMP-ACL',
                                                  'mode': u'ro'},
                         u'public_no_acl': {   'acl': u'N/A', 'mode': u'ro'}},
        'contact': u'Joe Smith',
        'location': u'123 Anytown USA Rack 404'}

        """
        # default values
        snmp_dict = {
            "chassis_id": "unknown",
            "community": {},
            "contact": "unknown",
            "location": "unknown",
        }
        command = "show run | include snmp-server"
        output = self._send_command(command)
        for line in output.splitlines():
            fields = line.split()
            if "snmp-server community" in line:
                name = fields[2]
                if "community" not in snmp_dict.keys():
                    snmp_dict.update({"community": {}})
                snmp_dict["community"].update({name: {}})
                try:
                    snmp_dict["community"][name].update({"mode": fields[3].lower()})
                except IndexError:
                    snmp_dict["community"][name].update({"mode": "N/A"})
                try:
                    snmp_dict["community"][name].update({"acl": fields[4]})
                except IndexError:
                    snmp_dict["community"][name].update({"acl": "N/A"})
            elif "snmp-server location" in line:
                snmp_dict["location"] = " ".join(fields[2:])
            elif "snmp-server contact" in line:
                snmp_dict["contact"] = " ".join(fields[2:])
            elif "snmp-server chassis-id" in line:
                snmp_dict["chassis_id"] = " ".join(fields[2:])
        # If SNMP Chassis wasn't found; obtain using direct command
        if snmp_dict["chassis_id"] == "unknown":
            command = "show snmp chassis"
            snmp_chassis = self._send_command(command)
            snmp_dict["chassis_id"] = snmp_chassis
        return snmp_dict

    def get_users(self):
        """
        Returns a dictionary with the configured users.
        The keys of the main dictionary represents the username.
        The values represent the details of the user,
        represented by the following keys:

            * level (int)
            * password (str)
            * sshkeys (list)

        *Note: sshkeys on ios is the ssh key fingerprint

        The level is an integer between 0 and 15, where 0 is the
        lowest access and 15 represents full access to the device.
        """
        username_regex = (
            r"^username\s+(?P<username>\S+)\s+(?:privilege\s+(?P<priv_level>\S+)"
            r"\s+)?(?:secret \d+\s+(?P<pwd_hash>\S+))?$"
        )
        pub_keychain_regex = (
            r"^\s+username\s+(?P<username>\S+)(?P<keys>(?:\n\s+key-hash\s+"
            r"(?P<hash_type>\S+)\s+(?P<hash>\S+)(?:\s+\S+)?)+)$"
        )
        users = {}
        command = "show run | section username"
        output = self._send_command(command)
        for match in re.finditer(username_regex, output, re.M):
            users[match.groupdict()["username"]] = {
                "level": int(match.groupdict()["priv_level"])
                if match.groupdict()["priv_level"]
                else 1,
                "password": match.groupdict()["pwd_hash"]
                if match.groupdict()["pwd_hash"]
                else "",
                "sshkeys": [],
            }
        for match in re.finditer(pub_keychain_regex, output, re.M):
            if match.groupdict()["username"] not in users:
                continue
            users[match.groupdict()["username"]]["sshkeys"] = list(
                map(
                    lambda s: s.strip()[9:],
                    filter(None, match.groupdict()["keys"].splitlines()),
                )
            )
        return users

    def ping(
        self,
        destination,
        source=C.PING_SOURCE,
        ttl=C.PING_TTL,
        timeout=C.PING_TIMEOUT,
        size=C.PING_SIZE,
        count=C.PING_COUNT,
        vrf=C.PING_VRF,
    ):
        """
        Execute ping on the device and returns a dictionary with the result.

        Output dictionary has one of following keys:
            * success
            * error
        In case of success, inner dictionary will have the followin keys:
            * probes_sent (int)
            * packet_loss (int)
            * rtt_min (float)
            * rtt_max (float)
            * rtt_avg (float)
            * rtt_stddev (float)
            * results (list)
        'results' is a list of dictionaries with the following keys:
            * ip_address (str)
            * rtt (float)
        """
        ping_dict = {}
        # vrf needs to be right after the ping command
        if vrf:
            command = "ping vrf {} {}".format(vrf, destination)
        else:
            command = "ping {}".format(destination)
        command += " timeout {}".format(timeout)
        command += " size {}".format(size)
        command += " repeat {}".format(count)
        if source != "":
            command += " source {}".format(source)

        output = self._send_command(command)
        if "%" in output:
            ping_dict["error"] = output
        elif "Sending" in output:
            ping_dict["success"] = {
                "probes_sent": 0,
                "packet_loss": 0,
                "rtt_min": 0.0,
                "rtt_max": 0.0,
                "rtt_avg": 0.0,
                "rtt_stddev": 0.0,
                "results": [],
            }

            for line in output.splitlines():
                if "Success rate is" in line:
                    sent_and_received = re.search(r"\((\d*)/(\d*)\)", line)
                    probes_sent = int(sent_and_received.group(2))
                    probes_received = int(sent_and_received.group(1))
                    ping_dict["success"]["probes_sent"] = probes_sent
                    ping_dict["success"]["packet_loss"] = probes_sent - probes_received
                    # If there were zero valid response packets, we are done
                    if "Success rate is 0 " in line:
                        break

                    min_avg_max = re.search(r"(\d*)/(\d*)/(\d*)", line)
                    ping_dict["success"].update(
                        {
                            "rtt_min": float(min_avg_max.group(1)),
                            "rtt_avg": float(min_avg_max.group(2)),
                            "rtt_max": float(min_avg_max.group(3)),
                        }
                    )
                    results_array = []
                    for i in range(probes_received):
                        results_array.append(
                            {
                                "ip_address": py23_compat.text_type(destination),
                                "rtt": 0.0,
                            }
                        )
                    ping_dict["success"].update({"results": results_array})

        return ping_dict

    def traceroute(
        self,
        destination,
        source=C.TRACEROUTE_SOURCE,
        ttl=C.TRACEROUTE_TTL,
        timeout=C.TRACEROUTE_TIMEOUT,
        vrf=C.TRACEROUTE_VRF,
    ):
        """
        Executes traceroute on the device and returns a dictionary with the result.

        :param destination: Host or IP Address of the destination
        :param source (optional): Use a specific IP Address to execute the traceroute
        :param ttl (optional): Maimum number of hops -> int (0-255)
        :param timeout (optional): Number of seconds to wait for response -> int (1-3600)

        Output dictionary has one of the following keys:

            * success
            * error

        In case of success, the keys of the dictionary represent the hop ID, while values are
        dictionaries containing the probes results:
            * rtt (float)
            * ip_address (str)
            * host_name (str)
        """

        # vrf needs to be right after the traceroute command
        if vrf:
            command = "traceroute vrf {} {}".format(vrf, destination)
        else:
            command = "traceroute {}".format(destination)
        if source:
            command += " source {}".format(source)
        if ttl:
            if isinstance(ttl, int) and 0 <= timeout <= 255:
                command += " ttl 0 {}".format(str(ttl))
        if timeout:
            # Timeout should be an integer between 1 and 3600
            if isinstance(timeout, int) and 1 <= timeout <= 3600:
                command += " timeout {}".format(str(timeout))

        # Calculation to leave enough time for traceroute to complete assumes send_command
        # delay of .2 seconds.
        max_loops = (5 * ttl * timeout) + 150
        if max_loops < 500:  # Make sure max_loops isn't set artificially low
            max_loops = 500
        output = self.device.send_command(command, max_loops=max_loops)

        # Prepare return dict
        traceroute_dict = dict()
        if re.search("Unrecognized host or address", output):
            traceroute_dict["error"] = "unknown host %s" % destination
            return traceroute_dict
        else:
            traceroute_dict["success"] = dict()

        results = dict()
        # Find all hops
        hops = re.findall(r"\n\s+[0-9]{1,3}\s", output)
        for hop in hops:
            # Search for hop in the output
            hop_match = re.search(hop, output)
            # Find the start index for hop
            start_index = hop_match.start()
            # If this is last hop
            if hops.index(hop) + 1 == len(hops):
                # Set the stop index for hop to len of output
                stop_index = len(output)
            # else, find the start index for next hop
            else:
                next_hop_match = re.search(hops[hops.index(hop) + 1], output)
                stop_index = next_hop_match.start()
                # Now you have the start and stop index for each hop
                # and you can parse the probes
            # Set the hop_variable, and remove spaces between msec for easier matching
            hop_string = output[start_index:stop_index].replace(" msec", "msec")
            hop_list = hop_string.split()
            current_hop = int(hop_list.pop(0))
            # Prepare dictionary for each hop (assuming there are 3 probes in each hop)
            results[current_hop] = dict()
            results[current_hop]["probes"] = dict()
            results[current_hop]["probes"][1] = {
                "rtt": float(),
                "ip_address": "",
                "host_name": "",
            }
            results[current_hop]["probes"][2] = {
                "rtt": float(),
                "ip_address": "",
                "host_name": "",
            }
            results[current_hop]["probes"][3] = {
                "rtt": float(),
                "ip_address": "",
                "host_name": "",
            }
            current_probe = 1
            ip_address = ""
            host_name = ""
            while hop_list:
                current_element = hop_list.pop(0)
                # If current_element is * move index in dictionary to next probe
                if current_element == "*":
                    current_probe += 1
                # If current_element contains msec record the entry for probe
                elif "msec" in current_element:
                    ip_address = py23_compat.text_type(ip_address)
                    host_name = py23_compat.text_type(host_name)
                    rtt = float(current_element.replace("msec", ""))
                    results[current_hop]["probes"][current_probe][
                        "ip_address"
                    ] = ip_address
                    results[current_hop]["probes"][current_probe][
                        "host_name"
                    ] = host_name
                    results[current_hop]["probes"][current_probe]["rtt"] = rtt
                    # After recording the entry move the index to next probe
                    current_probe += 1
                # If element contains '(' and ')', the output format is 'FQDN (IP_ADDRESS)'
                # Save the IP address
                elif "(" in current_element:
                    ip_address = current_element.replace("(", "").replace(")", "")
                # Save the probe's ip_address and host_name
                else:
                    host_name = current_element
                    ip_address = current_element

        traceroute_dict["success"] = results
        return traceroute_dict

    def get_network_instances(self, name=""):

        instances = {}
        sh_vrf_detail = self._send_command("show vrf detail")
        show_ip_int_br = self._send_command("show ip interface brief")

        # retrieve all interfaces for the default VRF
        interface_dict = {}
        show_ip_int_br = show_ip_int_br.strip()
        for line in show_ip_int_br.splitlines():
            if "Interface " in line:
                continue
            interface = line.split()[0]
            interface_dict[interface] = {}

        instances["default"] = {
            "name": "default",
            "type": "DEFAULT_INSTANCE",
            "state": {"route_distinguisher": ""},
            "interfaces": {"interface": interface_dict},
        }

        for vrf in sh_vrf_detail.split("\n\n"):

            first_part = vrf.split("Address family")[0]

            # retrieve the name of the VRF and the Route Distinguisher
            vrf_name, RD = re.match(r"^VRF (\S+).*RD (.*);", first_part).groups()
            if RD == "<not set>":
                RD = ""

            # retrieve the interfaces of the VRF
            if_regex = re.match(r".*Interfaces:(.*)", first_part, re.DOTALL)
            if "No interfaces" in first_part:
                interfaces = {}
            else:
                interfaces = {itf: {} for itf in if_regex.group(1).split()}

            instances[vrf_name] = {
                "name": vrf_name,
                "type": "L3VRF",
                "state": {"route_distinguisher": RD},
                "interfaces": {"interface": interfaces},
            }
        return instances if not name else instances[name]

    def get_config(self, retrieve="all"):
        """Implementation of get_config for IOS.

        Returns the startup or/and running configuration as dictionary.
        The keys of the dictionary represent the type of configuration
        (startup or running). The candidate is always empty string,
        since IOS does not support candidate configuration.
        """

        configs = {"startup": "", "running": "", "candidate": ""}

        if retrieve in ("startup", "all"):
            command = "show startup-config"
            output = self._send_command(command)
            configs["startup"] = output

        if retrieve in ("running", "all"):
            command = "show running-config"
            output = self._send_command(command)
            configs["running"] = output

        return configs

    def get_ipv6_neighbors_table(self):
        """
        Get IPv6 neighbors table information.
        Return a list of dictionaries having the following set of keys:
            * interface (string)
            * mac (string)
            * ip (string)
            * age (float) in seconds
            * state (string)
        For example::
            [
                {
                    'interface' : 'MgmtEth0/RSP0/CPU0/0',
                    'mac'       : '5c:5e:ab:da:3c:f0',
                    'ip'        : '2001:db8:1:1::1',
                    'age'       : 1454496274.84,
                    'state'     : 'REACH'
                },
                {
                    'interface': 'MgmtEth0/RSP0/CPU0/0',
                    'mac'       : '66:0e:94:96:e0:ff',
                    'ip'        : '2001:db8:1:1::2',
                    'age'       : 1435641582.49,
                    'state'     : 'STALE'
                }
            ]
        """

        ipv6_neighbors_table = []
        command = "show ipv6 neighbors"
        output = self._send_command(command)

        ipv6_neighbors = ""
        fields = re.split(r"^IPv6\s+Address.*Interface$", output, flags=(re.M | re.I))
        if len(fields) == 2:
            ipv6_neighbors = fields[1].strip()
        for entry in ipv6_neighbors.splitlines():
            # typical format of an entry in the IOS IPv6 neighbors table:
            # 2002:FFFF:233::1 0 2894.0fed.be30  REACH Fa3/1/2.233
            ip, age, mac, state, interface = entry.split()
            mac = "" if mac == "-" else napalm.base.helpers.mac(mac)
            ip = napalm.base.helpers.ip(ip)
            ipv6_neighbors_table.append(
                {
                    "interface": interface,
                    "mac": mac,
                    "ip": ip,
                    "age": float(age),
                    "state": state,
                }
            )
        return ipv6_neighbors_table

    @property
    def dest_file_system(self):
        # The self.device check ensures napalm has an open connection
        if self.device and self._dest_file_system is None:
            self._dest_file_system = self._discover_file_system()
        return self._dest_file_system

    ### Start of source code by Antoine Fourmy
    def get_vrf(self, vrf):

        regular_expressions = {
                    # we use .*? instead of .* to make the regex "non greedy"
                    'Export RT': re.compile('.*Export VPN route-target communities(.*?)[No|Import]', re.DOTALL),
                    'Import RT': re.compile('.*Import VPN route-target communities(.*?)[No|Import]', re.DOTALL),
                    'Export RM': re.compile('.*Export route-map:(.*?)Route', re.DOTALL),
                    'Import RM': re.compile('.*Import route-map:(.*?)No', re.DOTALL),
                    }

        command = 'show vrf detail {}'.format(vrf)
        output = self._send_command(command)

        vrf_data = {}
        vrf = output

        sections = vrf.split('Address family ')

        # retrieve the name and the RD
        name, RD = re.match(r'.*VRF (\S+) \(.*RD (.*);', sections[0], re.DOTALL).groups()
        # retrieve the list of interfaces of the VRF
        if_regex = re.match(r'.*Interfaces:(.*)', sections[0], re.DOTALL)
        interfaces = '' if 'No interfaces' in sections[0] else if_regex.group(1)
        vrf_data[name] = {'RD': RD, 'interfaces': set(interfaces.split())}

        matches = {}
        for section in sections[1:]:
            afi_match = re.match(r'^(\w+\s\w+).*', section, re.DOTALL)
            if afi_match:
                afi = afi_match.group(1)
                vrf_data[name][afi] = {}
                for regex_name, regex in regular_expressions.items():
                    match = re.match(regex, section)
                    result = set(match.group(1).split()) if match else set()
                    if regex_name in ('Export RT', 'Import RT'):
                        # the regex catches RT:x:y, we remove the 'RT:' part
                        result = {r[3:] for r in result}
                    vrf_data[name][afi][regex_name] = result

        return vrf_data

    def get_bgp_vpnv4_vrf(self, vrf):

        command = 'show ip bgp vpnv4 vrf {} detail'.format(vrf)
        output = self._send_command(command)

        result = {}

        for entry in output.split('BGP routing table')[1:]:
            ip = re.match('.*\d+:\d+:(.*?)/\d{1,2},', entry).group(1)
            RT = re.match('.*Extended Community: (.*?)[Originator|mpls]', entry, re.DOTALL)
            community = re.match('.*Community: (\d+:\d+)', entry, re.DOTALL)
            result[ip] = {}
            if RT:
                result[ip]['RT'] = {rt[3:] for rt in RT.group(1).split()}
            if community:
                result[ip]['community'] = {c for c in community.group(1).split()}
            for parameter in ('Origin', 'metric', 'localpref'):
                match = re.match('.*{} (.*?), .*'.format(parameter), entry, re.DOTALL)
                result[ip][parameter.lower()] = match.group(1) if match else -1

        return result

    ### End of source code by Antoine Fourmy

    ### Start of source code by Tomas Kubina
    @staticmethod
    def parse_bfd_uptime(uptime_str):
        """
        Extract the uptime string from the given Cisco IOS Device.
        Return the uptime in seconds as an integer
        """

        # Initialize to zero
        (years, weeks, days, hours, minutes, seconds) = (0, 0, 0, 0, 0, 0)

        uptime_str = uptime_str.strip()
        if ':' in uptime_str:
            hours = int(uptime_str.split(':')[0])
            minutes = int(uptime_str.split(':')[1])
            seconds = int(uptime_str.split(':')[2])
        else:
            if re.search("y", uptime_str):
                years = int(uptime_str.split('y')[0])
            elif re.search("w", uptime_str):
                weeks = int(uptime_str.split('w')[0])
            elif re.search("d", uptime_str):
                days = int(uptime_str.split('d')[0])
            elif re.search("h", uptime_str):
                hours = int(uptime_str.split('h')[0])
            elif re.search("m", uptime_str):
                minutes = int(uptime_str.split('m')[0])
            elif re.search("s", uptime_str):
                seconds = int(uptime_str.split('s')[0])

        uptime_sec = (years * YEAR_SECONDS) + (weeks * WEEK_SECONDS) + (days * DAY_SECONDS) + \
                     (hours * 3600) + (minutes * 60) + seconds
        return uptime_sec

    def get_redundancy_info(self):
        """ Return show redundancy output """

        show_redu_info = {}
        show_redu_info['available_system_uptime'] = 'unknown'
        show_redu_info['configured_redundancy_mode'] = 'unknown'
        show_redu_info['operating_redundancy_mode'] = 'unknown'
        show_redu_info['communications'] = 'unknown'
        show_redu_info['active_re'] = {'slot' : 'unkown'}
        show_redu_info['backup_re'] = {'slot' : 'unkown'}

        show_redu = self._send_command("show redundancy")
        for line in show_redu.splitlines():
            if 'Available system uptime' in line:
                show_redu_info['available_system_uptime'] = self.parse_uptime(line.split('= ')[1])
            elif 'Configured Redundancy Mode' in line:
                show_redu_info['configured_redundancy_mode'] = line.split('= ')[1]
            elif 'Operating Redundancy Mode' in line:
                show_redu_info['operating_redundancy_mode'] = line.split('= ')[1]
            elif 'Communications' in line:
                show_redu_info['communications'] = line.split('= ')[1]
            else:
                pass
        try:
            match_current_processor = re.compile(r'^Current\ Processor(.*)^Peer\ ', re.M|re.DOTALL)
            curret_proccessor_info = match_current_processor.search(show_redu)
            current_processor = curret_proccessor_info.group(1)
        except AttributeError:
            current_processor = ''

        for line in current_processor.splitlines():
            if 'Active Location' in line:
                show_redu_info['active_re']['slot'] = int(line.split('= ')[1].split()[1])
            elif 'Current Software state' in line:
                show_redu_info['active_re']['current_software_state'] = line.split('= ')[1]
            elif 'Uptime in current state' in line:
                show_redu_info['active_re']['uptime_in_current_state'] = self.parse_uptime(line.split('= ')[1])
            elif 'Image Version' in line:
                show_redu_info['active_re']['image_version'] = line.split('= ')[1]
            elif 'BOOT =' in line:
                show_redu_info['active_re']['boot'] = line.split('= ')[1]
            elif 'CONFIG_FILE' in line:
                show_redu_info['active_re']['config_file'] = line.split('= ')[1]
            elif 'BOOTLDR =' in line:
                show_redu_info['active_re']['bootldr'] = line.split('= ')[1]
            elif 'Configuration register' in line:
                show_redu_info['active_re']['configuration_register'] = line.split('= ')[1]
            else:
                continue
        try:
            match_peer_processor = re.compile(r'^Peer\ Processor(.*)', re.M|re.DOTALL)
            peer_proccessor_info = match_peer_processor.search(show_redu)
            peer_processor = peer_proccessor_info.group(1)
        except AttributeError:
            peer_processor = ''

        for line in peer_processor.splitlines():
            if 'Standby Location' in line:
                show_redu_info['backup_re']['slot'] = int(line.split('= ')[1].split()[1])
            elif 'Current Software state' in line:
                show_redu_info['backup_re']['current_software_state'] = line.split('= ')[1]
            elif 'Uptime in current state' in line:
                show_redu_info['backup_re']['uptime_in_current_state'] = self.parse_uptime(line.split('= ')[1])
            elif 'Image Version' in line:
                show_redu_info['backup_re']['image_version'] = line.split('= ')[1]
            elif 'BOOT =' in line:
                show_redu_info['backup_re']['boot'] = line.split('= ')[1]
            elif 'CONFIG_FILE' in line:
                show_redu_info['backup_re']['config_file'] = line.split('= ')[1]
            elif 'BOOTLDR =' in line:
                show_redu_info['backup_re']['bootldr'] = line.split('= ')[1]
            elif 'Configuration register' in line:
                show_redu_info['backup_re']['configuration_register'] = line.split('= ')[1]
            else:
                pass
        return show_redu_info

    def get_card_type_info(self):
        """ Return list of installed cards with corresponding slots """

        card_type_info = {}

        facts = self.get_facts()
        model = facts['model']

        if 'ASR10' in model:
            show_cards = self._send_command("show platform")
            try:
                match_card_list = re.compile(r'^Slot(.*)Slot', re.M|re.DOTALL)
                match_card_info = match_card_list.search(show_cards)
                card_list = match_card_info.group(1)
            except AttributeError:
                card_list = ''

            for line in card_list.splitlines():
                if 'Type' in line:
                    continue
                elif '--' in line:
                    continue
                else:
                    card_line = line.strip()
                    card_line = card_line.replace(',', ' ')
                    while '  ' in card_line:
                        card_line = card_line.replace('  ', ' ')
                    card_info = card_line.split()
                    if card_info != []:
                        card_type_info[str(card_info[0])] = {'type' : card_info[1], 'state' : card_info[2]}
                    else:
                        pass

        elif 'CISCO7609-S' in model:
            show_cards = self._send_command("show module")

            try:
                match_slot_list = re.compile(r'Ports(.*)MAC', re.M|re.DOTALL)
                match_slot_info = match_slot_list.search(show_cards)
                slot_list = match_slot_info.group(1)
            except AttributeError:
                slot_list = ''

            for line in slot_list.splitlines():
                if 'Mod' in line:
                    continue
                elif '--' in line:
                    continue
                else:
                    try:
                        match_slot_id = re.search(r'(^\ +[0-9]+)', line)
                        slot_id = match_slot_id.group(1)

                        match_card_type = re.search(r'\ +([\w\-]+)\ +[\w]+$', line)
                        card_type = match_card_type.group(1)

                        card_type_info[str(slot_id)] = {'type' : card_type, 'state' : 'unknown'}
                    except AttributeError:
                        pass

            try:
                match_slot_list = re.compile(r'MAC(.*)Sub-Module', re.M|re.DOTALL)
                match_slot_info = match_slot_list.search(show_cards)
                slot_list = match_slot_info.group(1)
            except AttributeError:
                slot_list = ''

            for line in slot_list.splitlines():
                if 'Mod' in line:
                    continue
                elif '--' in line:
                    continue
                else:
                    try:
                        match_slot_id = re.search(r'(^\ +[0-9]+)', line)
                        slot_id = match_slot_id.group(1)

                        match_slot_state = re.search(r'\ ([\w]+)$', line)
                        slot_state = match_slot_state.group(1)

                        card_type_info[str(slot_id)]['state'] = slot_state
                    except AttributeError:
                        pass

            try:
                match_card_list = re.compile(r'Sub-Module(.*)Online', re.M|re.DOTALL)
                match_card_info = match_card_list.search(show_cards)
                card_list = match_card_info.group(1)
            except AttributeError:
                card_list = ''

            for line in card_list.splitlines():
                if 'Model' in line:
                    continue
                elif '--' in line:
                    continue
                else:
                    try:
                        match_card_slot = re.search(r'([0-9]+\/[0-9])', line)
                        card_slot = match_card_slot.group(1)
                        match_card_type = re.search(r'(SPA[\w\-]+)\ ', line)
                        card_type = match_card_type.group(1)
                        match_card_state = re.search(r'\ ([\w]+)$', line)
                        card_state = match_card_state.group(1)

                        card_type_info[str(card_slot)] = {'type' : card_type, 'state' : card_state}
                    except AttributeError:
                        pass
        else:
            pass

        return card_type_info

    def get_asr1k_slot_memory_info(self):
        """ Returns memory status for all slots of ASR1K platform"""

        asr1k_memory_detail = {}

        show_platform_sw_status = self._send_command("show platform software status control-processor brief")
        try:
            match_mem_table_exp = re.compile(r'Memory\s\(kB\)(.*)CPU\sUtilization', re.M|re.DOTALL)
            match_mem_table = match_mem_table_exp.search(show_platform_sw_status)
            mem_table = match_mem_table.group(1)
        except AttributeError:
            mem_table = ''

        mem_table = mem_table.strip()
        for line in mem_table.splitlines():
            if 'Slot' in line:
                continue
            else:
                try:
                    match_slot_info = re.search(r'^\s+(\w+)\s+(\w+)\s+([0-9]+)\s+([0-9]+)\s+\([0-9]+\%\)\s+([0-9]+)\s+\([0-9]+\%\)\s+([0-9]+)\s+\([0-9]+\%\)',line)
                    asr1k_memory_detail[match_slot_info.group(1)] = {'status': match_slot_info.group(2),
                                                                     'total': match_slot_info.group(3), 
                                                                     'used': match_slot_info.group(4),
                                                                     'free': match_slot_info.group(5),
                                                                     'commited': match_slot_info.group(6)}
                except AttributeError:
                    continue

        return asr1k_memory_detail

    def get_isis_neighbors_detail(self):
        """ Returns list of ISIS neighbors with details """

        isis_neighbors = {}

        show_isis_nei_det = self._send_command("show isis neighbors detail")
        try:
            show_isis_nei_det = show_isis_nei_det.split('Circuit Id\n')[1]
        except IndexError:
            return isis_neighbors 

        isis_neighbor_info = ''

        for line in show_isis_nei_det.splitlines():
            if line[0:1] == '':
                continue
            elif line[0:1] == ' ':
                if 'Area Address' in line:
                    area_id = line.split(':')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['area'] = area_id.strip()
                if 'SNPA' in line:
                    snpa = line.split(':')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['snpa'] = snpa.strip()
                if 'State Changed' in line:
                    state_changed = line.split('Changed:')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['state_changed'] = self.parse_bfd_uptime(str(state_changed.strip()))
                if 'Format' in line:
                    _format = line.split(':')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['format'] = _format.strip()
                if 'Remote TID' in line:
                    r_tid = line.split(':')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['remote_tid'] = r_tid.strip()
                if 'Local TID' in line:
                    l_tid = line.split(':')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['local_tid'] = l_tid.strip()
                if 'Remote BFD Support' in line:
                    r_bfd = line.split('Support:')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['remote_bfd_support'] = r_bfd.strip()
                if 'BFD enabled' in line:
                    bfd = line.split('enabled:')[1]
                    isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]]['bfd_enabled'] = bfd.strip()
            else:
                # we have ISIS neighbor line
                isis_neighbor_info = line.split()
                if str(isis_neighbor_info[0]) not in isis_neighbors.keys():
                    isis_neighbors[str(isis_neighbor_info[0])] = {}
                isis_neighbors[str(isis_neighbor_info[0])][isis_neighbor_info[2]] = {'level': isis_neighbor_info[1],
                                                                                     'ip_address': isis_neighbor_info[3],
                                                                                     'state': isis_neighbor_info[4],
                                                                                     'holdtime': isis_neighbor_info[5],
                                                                                     'circuit_id': isis_neighbor_info[6]}

        return isis_neighbors

    def get_isis_topology(self):
        """ Returns ISIS topology info """

        isis_topo = {}
        isis_node_name = ''
        isis_node_metric = ''

        show_isis_topo = self._send_command("show isis topology")
        try:
            show_isis_topo = show_isis_topo.split('SNPA')[1]
        except IndexError:
            return isis_topo

        for line in show_isis_topo.splitlines():
            if line[0:1] == '':
                continue
            elif line[0:1] == ' ':
                isis_path_info = line.split()
                try:
                    match_snpa = re.search(r'\ ([\*\w]+\ [\w\-]+|[\w\.\*]+)$', line)
                    isis_snpa = match_snpa.group(1)
                except AttributeError:
                    isis_snpa = ''

                isis_topo[isis_node_name].append({'metric': isis_node_metric,
                                                  'next_hop': isis_path_info[0],
                                                  'interface': isis_path_info[1],
                                                  'snpa': isis_snpa})
            else:
                # we have ISIS router
                isis_path_info = line.split()
                line = line.strip()
                try:
                    match_snpa = re.search(r'\ ([\*\w]+\ [\w\-]+|[\w\.\*]+)$', line)
                    isis_snpa = match_snpa.group(1)
                except AttributeError:
                    isis_snpa = ''

                isis_node_name = isis_path_info[0]
                isis_node_metric = isis_path_info[1]

                if isis_node_metric == '--' or isis_node_metric == '**':
                    continue
                
                isis_topo[str(isis_node_name)] = [{'metric': isis_node_metric,
                                                   'next_hop': isis_path_info[2],
                                                   'interface': isis_path_info[3],
                                                   'snpa': isis_snpa}]
        return isis_topo

    def get_bfd_neighbors_detail(self):
        """ Returns list of BFD neighbors with details """

        bfd_neighbors = {}

        show_bfd_nei_det = self._send_command("show bfd neighbors details")
        show_bfd_nei_det = show_bfd_nei_det.split('NeighAddr')

        for neighbor in show_bfd_nei_det:
            neighbor_all_info = neighbor.splitlines()
            try:
                if 'State' not in neighbor_all_info[0]:
                    continue
            except IndexError:
                continue

            neighbor_info = neighbor_all_info[1].split()
            bfd_neighbors[str(neighbor_info[0])] = {'LD': neighbor_info[1].split('/')[0].strip(),
                                                    'RD': neighbor_info[1].split('/')[1].strip(),
                                                    'state': neighbor_info[3],
                                                    'interface': neighbor_info[4]}
            bfd_neighbors[str(neighbor_info[0])]['echo_mode'] = 'unknown'
            bfd_neighbors[str(neighbor_info[0])]['echo_interval'] = 0 

            for line in neighbor_all_info:
                if 'Session Host' in line:
                    bfd_neighbors[str(neighbor_info[0])]['session_host'] = line.split(':')[1].strip()
                elif 'Registered protocols' in line:
                    bfd_neighbors[str(neighbor_info[0])]['registered_protocols'] = line.split(':')[1].strip().split()
                elif 'Uptime' in line:
                    bfd_neighbors[str(neighbor_info[0])]['uptime'] = self.parse_bfd_uptime(str(line.split(':')[1].strip()))
                elif 'Session state is UP' in line:
                    if 'not using echo function' in line:
                        bfd_neighbors[str(neighbor_info[0])]['echo_mode'] = 'inactive'
                        bfd_neighbors[str(neighbor_info[0])]['echo_interval'] = 0 
                    elif 'using echo function with' in line:
                        bfd_neighbors[str(neighbor_info[0])]['echo_mode'] = 'active'
                        echo_interval = re.search(r'([0-9]+)\s+ms', line)
                        bfd_neighbors[str(neighbor_info[0])]['echo_interval'] = echo_interval.group(1)
                    else:
                        pass
                else:
                    continue

        return bfd_neighbors

    def get_ldp_igp_sync(self):
        """ Returns sync status between LDP and IGP """

        ldp_igp_sync_status = {}

        show_mpls_ldp_igp_sync = self._send_command("show mpls ldp igp sync")

        for line in show_mpls_ldp_igp_sync.splitlines():
            if re.search(r'\:$', line):
                interface = str(line.strip())
                ldp_igp_sync_status[interface] = {}
            else:
                if 'Synchronization not enabled' in line:
                    ldp_igp_sync_status[interface] = {'ldp_igp_sync_enabled':'no'}
                    ldp_igp_sync_status[interface]['sync_achieved'] = 'no'
                    continue
                elif 'Sync status' in line:
                    ldp_igp_sync_status[interface] = {'ldp_igp_sync_enabled':'yes'}
                    if 'sync achieved' in line:
                        ldp_igp_sync_status[interface]['sync_achieved'] = 'yes'
                    else:
                        ldp_igp_sync_status[interface]['sync_achieved'] = 'no'
                    
        return ldp_igp_sync_status

    def get_ldp_neighbors(self):
        """ Return LDP neighbor info list """
    
        ldp_neighbors = {}

        show_mpls_ldp_neigh = self._send_command("show mpls ldp neighbor")
        show_mpls_ldp_neigh = show_mpls_ldp_neigh.split('Peer LDP Ident')
        for peer in show_mpls_ldp_neigh:
            if 'LDP' not in peer:
                continue
            try:
                peer_ip = re.search(r':\ (.+);', peer)
                ldp_neighbors[str(peer_ip.group(1))] = {}
                ldp_neighbors[str(peer_ip.group(1))]['discovery_sources'] = []
            except AttributeError:
                continue

            for line in peer.splitlines():
                if 'State' in line:
                    try:
                        peer_state = re.search(r'State:\ (\w+);', peer)
                        ldp_neighbors[str(peer_ip.group(1))]['state'] = peer_state.group(1)
                    except AttributeError:
                        continue
                if 'Up time' in line:
                    ldp_neighbors[str(peer_ip.group(1))]['uptime'] = self.parse_bfd_uptime(str(line.split(':')[1].strip()))
            
            try:
                match_peer_prefixes = re.compile(r'Addresses bound to peer LDP Ident:(.*)', re.M|re.DOTALL)
                peer_prefixes_list = match_peer_prefixes.search(peer)
                peer_prefixes = peer_prefixes_list.group(1)
                ldp_neighbors[str(peer_ip.group(1))]['addresses'] = peer_prefixes.split()
            except AttributeError:
                continue

            try:
                match_discovery_sources = re.compile(r'LDP discovery sources:(.*)Addresses bound to peer LDP Ident:', re.M|re.DOTALL)
                discovery_sources_list = match_discovery_sources.search(peer)
                discovery_sources = discovery_sources_list.group(1)
                for line in discovery_sources.splitlines():
                    if line == '':
                        pass
                    elif line == '        ':
                        pass
                    else:
                        ldp_neighbors[str(peer_ip.group(1))]['discovery_sources'].append(line.strip().split()[0].strip(','))
            except AttributeError:
                continue

        return ldp_neighbors

    def get_mpls_l2transport_summary(self):
        """ Return summary of l2 transport connections"""

        l2transport_summary = {}

        command = "show mpls l2transport summary" 
        show_l2_sum = self._send_command(command)
        show_l2_sum = show_l2_sum.strip().split('Destination')

        for peer in show_l2_sum:
            for line in peer.splitlines():
                if 'address' in line:
                    try:
                        match_dst_address = re.search(r'address:\s+(.*)\,', line)
                        dst_address = str(match_dst_address.group(1))
                        l2transport_summary[dst_address] = {}
                    except AttributeError:
                        continue
                if 'unknown' in line:
                    try:
                        match_unknow = re.search(r'([0-9]+)\s+unknown', line)
                        l2transport_summary[dst_address]['unknown'] = int(match_unknow.group(1)) 

                        match_up = re.search(r'([0-9]+)\s+up', line)
                        l2transport_summary[dst_address]['up'] = int(match_up.group(1)) 

                        match_down = re.search(r'([0-9]+)\s+down', line)
                        l2transport_summary[dst_address]['down'] = int(match_down.group(1)) 

                        match_adm_down = re.search(r'([0-9]+)\s+admin\ down', line)
                        l2transport_summary[dst_address]['admin_down'] = int(match_adm_down.group(1)) 

                        match_recovering = re.search(r'([0-9]+)\s+recovering', line)
                        l2transport_summary[dst_address]['recovering'] = int(match_recovering.group(1)) 

                        match_standby = re.search(r'([0-9]+)\s+standby', line)
                        l2transport_summary[dst_address]['standby'] = int(match_standby.group(1))

                        match_hotstandby = re.search(r'([0-9]+)\s+hotstandby', line)
                        l2transport_summary[dst_address]['hotstandby'] = int(match_hotstandby.group(1)) 
                    except AttributeError:
                        continue
                if 'active' in line:
                    try:
                        match_interface = re.search(r'\s([\w\.\/]+)$', line)
                        interface = str(match_interface.group(1))
                        match_active = re.search(r'\s+([0-9]+)\s+', line)
                        l2transport_summary[dst_address][interface] = {'active': int(match_active.group(1))}
                    except AttributeError:
                        continue
        return l2transport_summary

    def get_mpls_te_tunnels_brief(self):
        """ Returns summart of TE tunnels """

        te_tunnels_summary = {}

        command = "show mpls traffic-eng tunnels brief"
        show_te_tunnels_brief = self._send_command(command)

        try:
            show_te_tunnels_brief = show_te_tunnels_brief.strip().split('STATE/PROT')[1].strip()
        except IndexError:
            return te_tunnels_summary

        for line in show_te_tunnels_brief.splitlines():
            try:
                te_tunnel = line.strip()
                split_tunnel_data = re.search(r'([\w\-\_\.\/\(\)\W\s]+)\s+([0-9]+\.[0-9]+\.[0-9]+\.[0-9]+)\s+([\w\/\-]+)\s+([\w\/\-]+)\s+([\w\/\-]+)', te_tunnel)
                tunnel_name = str(split_tunnel_data.group(1).strip())
                te_tunnels_summary[tunnel_name] = {}
                te_tunnels_summary[tunnel_name]['destination'] = str(split_tunnel_data.group(2))
                te_tunnels_summary[tunnel_name]['up_if'] = str(split_tunnel_data.group(3))
                te_tunnels_summary[tunnel_name]['down_if'] = str(split_tunnel_data.group(4))
                te_tunnels_summary[tunnel_name]['state_prot'] = str(split_tunnel_data.group(5))
            except AttributeError:
                continue

        return te_tunnels_summary

    @staticmethod
    def _parse_ip_route_summary_output(output):
        """ Routing table parsing function """

        ip_route_sum = {}

        for line in output.splitlines():
            match_source_info = re.search(r'([\w\s]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)\s+([0-9]+)', line)
            if match_source_info:
                ip_route_sum[match_source_info.group(1).strip()] = {'networks': match_source_info.group(2),
                                                                    'subnets': match_source_info.group(3),
                                                                    'replicates': match_source_info.group(4),
                                                                    'overhead': match_source_info.group(5),
                                                                    'memory_bytes': match_source_info.group(6)
                                                                    }
        return ip_route_sum

    def get_ip_route_summary(self):
        """ Returns summary of global routing table """

        command = "show ip route summary"
        show_ip_route_summary = self._send_command(command)

        show_ip_route_summary = show_ip_route_summary.strip()

        return self._parse_ip_route_summary_output(show_ip_route_summary)

    def get_ip_route_summary_vrf(self, vrf_name):
        """ Returns summary of vrf routing table """

        command = "show ip route vrf " + vrf_name + " summary"
        show_ip_route_vrf_summary = self._send_command(command)

        show_ip_route_vrf_summary = show_ip_route_vrf_summary.strip()

        return self. _parse_ip_route_summary_output(show_ip_route_vrf_summary)

    @staticmethod
    def _parse_ip_cef_output(output):
        """ IP CEF output parsing function"""

        ip_cef = {}

        output = output.split('Interface')
        if len(output) > 1:
            output = output[1].strip()
            for line in output.splitlines():
                prefix_info = line.split()
                ip_cef[prefix_info[0]] = {'next_hop': prefix_info[1]}
                if len(prefix_info) == 3:
                    ip_cef[prefix_info[0]]['interface'] = prefix_info[2]

        return ip_cef

    def get_ip_cef(self):
        """ Return IP CEF in global context """

        command = "show ip cef"
        show_ip_cef = self._send_command(command)

        show_ip_cef = show_ip_cef.strip()

        return self. _parse_ip_cef_output(show_ip_cef)

    def get_ip_cef_vrf(self, vrf_name):
        """ Return IP CEF in vrf context """

        command = "show ip cef vrf " + vrf_name
        show_ip_cef_vrf = self._send_command(command)

        show_ip_cef_vrf = show_ip_cef_vrf.strip()

        return self._parse_ip_cef_output(show_ip_cef_vrf)

    def get_interfaces_rates(self):
        """ Returns input/output rate for interfaces """

        interface_rates = {}

        command = "show interfaces"
        show_interfaces = self._send_command(command)
        show_interfaces = show_interfaces.strip()

        interfaces_data = re.split(r'.* line protocol is .*', show_interfaces, flags=re.M)
        interfaces_name = re.findall(r'.* line protocol is .*', show_interfaces, flags=re.M)
        del interfaces_data[0]

        for interface, int_data in zip(interfaces_name, interfaces_data):
            try:
                interface_name = interface.split()[0]
                interface_rates[interface_name] = {}
            except IndexError:
                continue

            try:
                match_input_rate = re.compile(r'input\s+rate\s+([0-9]+)\s+[\w\/]+\,\s+([0-9]+)', re.M|re.DOTALL)
                input_rate_data = match_input_rate.search(int_data)
                match_output_rate = re.compile(r'output\s+rate\s+([0-9]+)\s+[\w\/]+\,\s+([0-9]+)', re.M|re.DOTALL)
                output_rate_data = match_output_rate.search(int_data)
                interface_rates[interface_name] = {'input_rate': {'bps': int(input_rate_data.group(1)) , 'pps': int(input_rate_data.group(2))},
                                                'output_rate': {'bps': int(output_rate_data.group(1)) , 'pps': int(output_rate_data.group(2))}
                                                }
            except AttributeError:
                continue
        return interface_rates

    def get_xconnect_all(self):
        """ Returns list of all xconnects """
        xconnect = []

        command = "show xconnect all"
        show_xconnect_all = self._send_command(command)
        show_xconnect_all = show_xconnect_all.strip()

        for line in show_xconnect_all.splitlines():
            try:
                match_xconnect_info = re.search(r'([\w\-]+)\s(\w+)\s([\W\w]+)\s+(UP|DN|AD|IA|SB|HS|RV|NH|--)\s([\w\W]+)\s+(UP|DN|AD|IA|SB|HS|RV|NH|--)', line)
                xconnect.append({'xc_state': [match_xconnect_info.group(1).strip(), match_xconnect_info.group(2).strip()],
                                'segment_1': match_xconnect_info.group(3).strip(),
                                'segment_1_state': match_xconnect_info.group(4).strip(),
                                'segment_2': match_xconnect_info.group(5).strip(),
                                'segment_2_state': match_xconnect_info.group(6).strip()})
            except AttributeError:
                continue
        
        return xconnect

    def get_bgp_all_summary(self):
        """ Returns bgp neighbors list with summary details """
        bgp_neighbors = {}

        command = "show bgp all summary"
        show_bgp_all_summary = self._send_command(command)
        show_bgp_all_summary = show_bgp_all_summary.strip()

        afi_data = re.split(r'For address family:',show_bgp_all_summary, flags=re.M)
        afi_name = re.findall(r'For address family\:\s+([\w\s]+)$', show_bgp_all_summary, flags=re.M)
        is_v6 = 0

        del afi_data[0]

        for name, data in zip(afi_name, afi_data):
            bgp_neighbors[name] = {}
            for line in data.splitlines():
                try:
                    match_neighbor_info = re.search(r'(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})\s+4\s+(\d+)\s+\d+\s+\d+\s+\d+\s+\d+\s+\d+\s+([\w\:]+)\s+([\d\w\W]+)', line)
                    if match_neighbor_info:
                        neighbor_ip = str(match_neighbor_info.group(1))

                        if re.search(r'(\d+)', match_neighbor_info.group(4)):
                            state = 'Established'
                            pfx_received = int(match_neighbor_info.group(4))
                        if re.search(r'([a-zA-Z]+)', match_neighbor_info.group(4)):
                            state = str(match_neighbor_info.group(4))
                            pfx_received = 0

                        bgp_neighbors[str(name)][neighbor_ip] = {'as': str(match_neighbor_info.group(2)),
                                                                'up/down': self.parse_bfd_uptime(str(match_neighbor_info.group(3))),
                                                                'state': state,
                                                                'pfx_rcv': pfx_received}
                    match_ipv6_neighbor = re.compile(r'^\*?({})'.format(IPV6_ADDR_REGEX))
                    match_neighbor_info = match_ipv6_neighbor.search(line)
                    if match_neighbor_info:
                        is_v6 = 1
                        neighbor_ipv6 = str(match_neighbor_info.group(1))
                    if is_v6 == 1:
                        is_v6 = 0
                        match_neighbor_info = re.search(r'\s+4\s+(\d+)\s+\d+\s+\d+\s+\d+\s+\d+\s+\d+\s+([\w\:]+)\s+([\d\w\W]+)', line)
                        if match_neighbor_info:
                            
                            if re.search(r'(\d+)', match_neighbor_info.group(3)):
                                state = 'Established'
                                pfx_received = int(match_neighbor_info.group(3))
                            if re.search(r'([a-zA-Z]+)', match_neighbor_info.group(3)):
                                state = str(match_neighbor_info.group(3))
                                pfx_received = 0


                            bgp_neighbors[str(name)][neighbor_ipv6] = {'as': str(match_neighbor_info.group(1)),
                                                                       'up/down': self.parse_bfd_uptime(str(match_neighbor_info.group(2))),
                                                                       'state': state,
                                                                       'pfx_rcv': pfx_received}

                except AttributeError:
                    continue

        return bgp_neighbors

    @staticmethod
    def _parse_pim_neighbors_output(output):
        """ PIM neighbor parsing function """

        pim_neighbors = {}

        for line in output.splitlines():
            try:
                match_neigh = re.search(r'^([0-9]+\.[0-9]+\.[0-9]+\.[0-9]+)', line)
                neighbor_ip = match_neigh.group(1)
                neighbor_info = line.split()
                uptime = neighbor_info[2].split('/')[0]
                expiration = neighbor_info[2].split('/')[1]
                match_neigh_mode = re.search(r'\/\s+(.*)$', line)
                # neigh_mode = match_neigh_mode.group(1)
                pim_neighbors[str(neighbor_ip)] = {'interface': neighbor_info[1],
                                                   'uptime': IOSDriver.parse_bfd_uptime(str(uptime)),
                                                   'expiration': IOSDriver.parse_bfd_uptime(str(expiration)),
                                                   'version': neighbor_info[3].split('v')[1],
                                                   'dr_priority': neighbor_info[4],
                                                   'mode': 'unknown'}
            except AttributeError:
                continue

        return pim_neighbors

    def get_pim_neighbors(self):
        """ Return PIM neighbors in global context """

        command = "show ip pim neighbor"
        show_pim_neigh = self._send_command(command)

        show_pim_neigh = show_pim_neigh.strip()

        return self._parse_pim_neighbors_output(show_pim_neigh)

    def get_pim_neighbors_vrf(self, vrf_name):
        """ Return PIM neighbors in vrf context """

        command = "show ip pim vrf " + vrf_name + " neighbor" 
        show_pim_neigh = self._send_command(command)

        show_pim_neigh = show_pim_neigh.strip()

        return self._parse_pim_neighbors_output(show_pim_neigh)

    @staticmethod
    def _parse_mroute_output(output):
        """ mroute parsing function """

        mroutes = {}

        try:
            match_mcast_entry = re.compile(r'\n\(', re.M|re.DOTALL)
            mcast_entries = match_mcast_entry.split(output)
        except AttributeError:
            pass

        for entry in mcast_entries:
            try:
                match_mroute_entry = re.compile(r'(.*)\)\,', re.M|re.DOTALL)
                mcast_pair = match_mroute_entry.search(entry)
                mcast_pair = mcast_pair.group(1).split(',')
                mroute_address = mcast_pair[1].strip()
                if not mroutes.has_key(mroute_address):
                    mroutes[mroute_address] = {}
                source = mcast_pair[0].strip()
                mroutes[mroute_address][source] = {}

                match_mroute_timers = re.compile(r'\)\,\s+([\w\/\:]+)\,\s+', re.M|re.DOTALL)
                mroute_timers = match_mroute_timers.search(entry)
                if mroute_timers:
                    timers = mroute_timers.group(1).strip().split('/')
                    mroutes[mroute_address][source]['uptime'] = IOSDriver.parse_bfd_uptime(str(timers[0]))
                    if ':' in timers[1]:
                        mroutes[mroute_address][source]['expires'] = IOSDriver.parse_bfd_uptime(str(timers[1]))
                    else:
                        mroutes[mroute_address][source]['expires'] = timers[1]

                match_mroute_rp = re.compile(r'RP\s+([\w\.]+)\,', re.M|re.DOTALL)
                mroute_rp = match_mroute_rp.search(entry)
                if mroute_rp:
                    rp = mroute_rp.group(1).strip()
                    mroutes[mroute_address][source]['rp'] = rp

                match_mroute_flags = re.compile(r'flags\:\s+(\w+)$', re.M|re.DOTALL)
                mroute_flags = match_mroute_flags.search(entry)
                if mroute_flags:
                    flags = mroute_flags.group(1).strip()
                    mroutes[mroute_address][source]['flags'] = flags

                match_in_int = re.compile(r'Incoming interface\:\s+([\w\/\.\W]+)Outgoing\ interface\ list', re.M|re.DOTALL)
                in_int = match_in_int.search(entry)
                if in_int:
                    in_int_info = {}

                    in_int = in_int.group(1).strip()

                    in_int_det = re.search(r'^([\w\/\.]+)\,\s+RPF\ nbr\s+([0-9\.]+)[\,\s]*', in_int)
                    if in_int_det:
                        in_int_info['name'] = in_int_det.group(1)
                        in_int_info['rpf'] = in_int_det.group(2)

                    in_int_mdt = re.search(r'MDT\:([\w\W]+)', in_int)
                    if in_int_mdt:
                        mdt_add = in_int_mdt.group(1).split('/')[0].strip('[')
                        mdt_add = mdt_add.strip(']').split(',')

                        mdt_timer = in_int_mdt.group(1).split('/')[1]

                        in_int_info['mdt'] = {'source': mdt_add[0], 'mcast_group': mdt_add[1], 'timer': IOSDriver.parse_bfd_uptime(str(mdt_timer))}

                    mroutes[mroute_address][source]['incoming_interface'] = in_int_info

                match_out_int = re.compile(r'Outgoing interface list\:\s+(.*)$', re.M|re.DOTALL)
                out_int = match_out_int.search(entry)
                if out_int:
                    out_int_info = []

                    out_ints_temp = []
                    out_ints = out_int.group(1).strip().split('\n')
                    for interface in out_ints:
                        out_ints_temp.append(interface.strip())

                    out_ints = out_ints_temp

                    for line in out_ints:
                        out_int = {}
                        out_int_det = re.search(r'^([\w\/\.]+)\,\s+([\w\/]+)\,\s+([\w\/\:]+)', line)
                        if out_int_det:
                            out_int['name'] = out_int_det.group(1)
                            out_int['state'] = out_int_det.group(2)
                            out_int['uptime'] = IOSDriver.parse_bfd_uptime(str(out_int_det.group(3).split('/')[0]))
                            out_int['expires'] = IOSDriver.parse_bfd_uptime(str(out_int_det.group(3).split('/')[1]))

                        out_int_info.append(out_int)
                    mroutes[mroute_address][source]['outgoing_interfaces'] = out_int_info

            except AttributeError:
                continue

        return mroutes

    def get_ip_mroute(self):
        
        command = "show ip mroute"
        show_ip_mroute = self._send_command(command)

        show_ip_mroute = show_ip_mroute.strip()

        return self._parse_mroute_output(show_ip_mroute)

    def get_ip_mroute_vrf(self, vrf_name):
        
        command = "show ip mroute vrf " + vrf_name
        show_ip_mroute_vrf = self._send_command(command)

        show_ip_mroute_vrf = show_ip_mroute_vrf.strip()

        return self._parse_mroute_output(show_ip_mroute_vrf)

    @staticmethod
    def _parse_mroute_active_output(output):
        
        mroute_active = {}

        try:
            match_mcast_entry = re.compile(r'Group\:\s+', re.M|re.DOTALL)
            mcast_entries = match_mcast_entry.split(output)
        except AttributeError:
            pass

        for entry in mcast_entries:
            try:
                match_group = re.search(r'([0-9\.]+)\,', entry)
                if match_group:
                    group = match_group.group(1).strip()

                    mroute_active[group] = {}

                    for line in entry.splitlines():
                        if 'Source:' in line:
                            source = line.split()[1].strip()
                        if 'RP-tree' in line:
                            source = '*'
                        if 'Rate' in line:
                            rates = line.split('Rate: ')[1].split(',')
                            rates_info = {}

                            sec_rates = re.search(r'([0-9]+)\s+\w+\/([0-9]+).*', rates[0])
                            sec30_rates = re.search(r'([0-9]+)\s+kbps', rates[1])
                            life_avg_rates = re.search(r'([0-9]+)\s+kbps', rates[2])

                            rates_info['1_sec'] = {'pps': sec_rates.group(1), 'kbps': sec_rates.group(2)}
                            rates_info['30_sec'] = {'kbps': sec30_rates.group(1)}
                            rates_info['life_avg'] = {'kbps': life_avg_rates.group(1)}

                            mroute_active[group][source] = rates_info

            except AttributeError:
                continue

        return mroute_active

    def get_ip_mroute_active(self):
        
        command = "show ip mroute active"
        show_ip_mroute_active = self._send_command(command)

        show_ip_mroute_active = show_ip_mroute_active.strip()

        return self._parse_mroute_active_output(show_ip_mroute_active)

    def get_ip_mroute_active_vrf(self, vrf_name):
        
        command = "show ip mroute vrf " + vrf_name + " active"
        show_ip_mroute_vrf_active = self._send_command(command)

        show_ip_mroute_vrf_active = show_ip_mroute_vrf_active.strip()

        return self._parse_mroute_active_output(show_ip_mroute_vrf_active)

    @staticmethod
    def _parse_mfib_output(output):
        
        mfib = {}

        try:
            match_mcast_entry = re.compile(r'\(', re.M|re.DOTALL)
            mcast_entries = match_mcast_entry.split(output)
        except AttributeError:
            pass

        for entry in mcast_entries:
            try:
                match_mroute_entry = re.compile(r'(.*)\)\s+', re.M|re.DOTALL)
                mcast_pair = match_mroute_entry.search(entry)
                mcast_pair = mcast_pair.group(1).split(',')
                mroute_address = mcast_pair[1].strip()
                if not mfib.has_key(mroute_address):
                    mfib[mroute_address] = {}

                source = mcast_pair[0].strip()
                mfib[mroute_address][source] = {}

                match_mroute_flags = re.compile(r'Flags\:\s+([\w\s]+)$', re.M|re.DOTALL)
                mroute_flags = match_mroute_flags.search(entry)
                if mroute_flags:
                    flags = mroute_flags.group(1).strip()
                    mfib[mroute_address][source]['flags'] = flags.split()

                match_sw_fw = re.compile(r'SW\sForwarding\:\s+([0-9\/]+)\,', re.M|re.DOTALL)
                sw_fw = match_sw_fw.search(entry)
                if sw_fw:
                    sw_fwd = sw_fw.group(1).split('/')
                    mfib[mroute_address][source]['sw_forwarding'] = {'pkt_count': sw_fwd[0],
                                                                     'pps': sw_fwd[1],
                                                                     'avg_pkt_size': sw_fwd[2],
                                                                     'kbps': sw_fwd[3]
                                                                    }

                match_hw_fw = re.compile(r'HW\sForwarding\:\s+([0-9\/]+)\,', re.M|re.DOTALL)
                hw_fw = match_hw_fw.search(entry)
                if hw_fw:
                    hw_fwd = hw_fw.group(1).split('/')
                    mfib[mroute_address][source]['hw_forwarding'] = {'pkt_count': hw_fwd[0],
                                                                     'pps': hw_fwd[1],
                                                                     'avg_pkt_size': hw_fwd[2],
                                                                     'kbps': hw_fwd[3]
                                                                    }

                match_interfaces = re.compile(r'HW\sForwarding\:[\ \w\/\,\:]+\n(.*)\n\s+Pkts', re.M|re.DOTALL)
                interfaces = match_interfaces.search(entry)

                line_id = 1
                mfib[mroute_address][source]['outgoing_interfaces'] = []
                for line in interfaces.group(1).splitlines():
                    match_flags = re.split(r'Flags:\s+', line)
                    if len(match_flags) > 1:
                        flags = match_flags[1].split()
                        interface = match_flags[0].strip().split(',')
                        if line_id == 1:
                            if len(interface) == 1:
                                mfib[mroute_address][source]['incoming_interface'] = {'name': interface[0].strip(),
                                                                                      'flags': flags}
                            if len(interface) == 2:
                                mfib[mroute_address][source]['incoming_interface'] = {'name': interface[0].strip(),
                                                                                      'mdt': interface[1].strip(),
                                                                                      'flags': flags}
                        else:
                            if len(interface) == 1:
                                out_int_info = {'name': interface[0].strip(),
                                                'flags': flags}
                            if len(interface) == 2:
                                out_int_info = {'name': interface[0].strip(),
                                                'mdt': interface[1].strip(),
                                                'flags': flags}
                            mfib[mroute_address][source]['outgoing_interfaces'].append(out_int_info)
                    line_id += 1
                
            except AttributeError:
                continue

        return mfib

    def get_ip_mfib(self):
        
        command = "show ip mfib"
        show_ip_mfib = self._send_command(command)

        show_ip_mfib = show_ip_mfib.strip()

        return self._parse_mfib_output(show_ip_mfib)

    def get_ip_mfib_vrf(self, vrf_name):
        
        command = "show ip mfib vrf " + vrf_name
        show_ip_mfib_vrf = self._send_command(command)

        show_ip_mfib_vrf = show_ip_mfib_vrf.strip()

        return self._parse_mfib_output(show_ip_mfib_vrf)

    @staticmethod
    def _parse_mfib_active_output(output):
        
        mfib_active = {}

        try:
            match_mcast_entry = re.compile(r'Group\:\s+', re.M|re.DOTALL)
            mcast_entries = match_mcast_entry.split(output)
        except AttributeError:
            pass


        for entry in mcast_entries:
            try:
                match_group = re.search(r'([0-9]+\.[0-9]+\.[0-9]+\.[0-9]+)\n', entry)
                if match_group:
                    group = match_group.group(1).strip()

                    mfib_active[group] = {}

                    for line in entry.splitlines():
                        if 'Source:' in line:
                            source = line.split()[1].strip()
                            mfib_active[group][source] = {}
                        if 'RP-tree' in line:
                            source = '*'
                            mfib_active[group][source] = {}
                        if 'SW Rate' in line:
                            rates = line.split('SW Rate: ')[1].split(',')[0]
                            rates_info = {}

                            sec_rates = re.search(r'([0-9]+)\s+\w+\/([0-9]+).*', rates)
                            rates_info['1_sec'] = {'pps': sec_rates.group(1), 'kbps': sec_rates.group(2)}
                            mfib_active[group][source]['sw_rates'] = rates_info          
                        if 'HW Rate' in line:
                            rates = line.split('HW Rate: ')[1]
                            rates_info = {}

                            sec_rates = re.search(r'([0-9]+)\s+\w+\/([0-9]+).*', rates)
                            rates_info['1_sec'] = {'pps': sec_rates.group(1), 'kbps': sec_rates.group(2)}
                            mfib_active[group][source]['hw_rates'] = rates_info            
            except AttributeError:
                continue

        return mfib_active

    def get_ip_mfib_active(self):
        
        command = "show ip mfib active"
        show_ip_mfib_active = self._send_command(command)

        show_ip_mfib_active = show_ip_mfib_active.strip()

        return self._parse_mfib_active_output(show_ip_mfib_active)

    def get_ip_mfib_active_vrf(self, vrf_name):
        
        command = "show ip mfib vrf " + vrf_name + " active"
        show_ip_mfib_active_vrf = self._send_command(command)

        show_ip_mfib_active_vrf = show_ip_mfib_active_vrf.strip()

        return self._parse_mfib_active_output(show_ip_mfib_active_vrf)
    
    ### End of source code by Tomas Kubina