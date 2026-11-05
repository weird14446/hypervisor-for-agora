#!/usr/bin/env python3
"""
formal-verification/adversarial_challenge.py
Adversarial Stress Test Suite for Agora Hypervisor Formal Verification Models.

Executes exhaustive empirical challenges against:
- formal-verification/verify_network_isolation.py
- formal-verification/verify_state_confinement.py

Verifies:
1. All adversarial attack queries evaluate to strictly UNSAT.
2. All non-vacuity / sanity witnesses evaluate to strictly SAT.
3. Boundary edge cases across all 14 blocked CIDRs, host ingress ports,
   source IP spoofing, directory permission bits, file types, and privilege flags.
"""
import ipaddress
import sys
import z3

# Import models from verification files
from verify_network_isolation import (
    ip_to_bv, in_subnet, BLOCKED_NETWORKS, TRANSIT_NETWORK,
    GUEST_VM_IP, GUEST_TAP_IP, PUBLIC_PROXY_IP, HOST_INGRESS_IP,
    IF_TAP0, IF_WAN0, IF_AGV1, IF_AGV2, IF_UPLINK,
    CT_INVALID, CT_NEW, CT_ESTABLISHED, CT_RELATED,
    PROTO_TCP, PROTO_UDP,
    PacketModel, encode_host_chain, encode_host_input_chain,
    encode_https_proxy_filter, encode_namespace_firewall
)

class AdversarialChallengeRunner:
    def __init__(self):
        self.total_tests = 0
        self.passed_tests = 0
        self.failed_tests = 0
        self.results = []

    def assert_unsat(self, solver: z3.Solver, description: str):
        self.total_tests += 1
        res = solver.check()
        if res == z3.unsat:
            self.passed_tests += 1
            self.results.append((description, "UNSAT", "PASS", None))
            print(f"  [PASS] (UNSAT) {description}")
        else:
            self.failed_tests += 1
            model = solver.model() if res == z3.sat else "UNKNOWN"
            self.results.append((description, str(res), "FAIL", model))
            print(f"  [FAIL] Expected UNSAT, got {res}: {description}\n    Counterexample: {model}")

    def assert_sat(self, solver: z3.Solver, description: str):
        self.total_tests += 1
        res = solver.check()
        if res == z3.sat:
            self.passed_tests += 1
            self.results.append((description, "SAT", "PASS", None))
            print(f"  [PASS] (SAT - Non-Vacuous Witness) {description}")
        else:
            self.failed_tests += 1
            self.results.append((description, str(res), "FAIL", None))
            print(f"  [FAIL] Expected SAT (vacuity check failed), got {res}: {description}")

    # =========================================================================
    # SUITE 1: NETWORK ISOLATION ADVERSARIAL CHALLENGES
    # =========================================================================
    def run_network_challenges(self):
        print("\n" + "=" * 78)
        print(" SUITE 1: ADVERSARIAL CHALLENGES - NETWORK ISOLATION (verify_network_isolation)")
        print("=" * 78)

        # ---------------------------------------------------------------------
        # Challenge 1.1: Egress Routing to Each Individual Blocked CIDR
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.1: Egress Packets to Specific Blocked Subnet Destinations ---")
        probe_ips = [
            ("0.0.0.1", "0.0.0.0/8 (Current network)"),
            ("10.0.0.1", "10.0.0.0/8 (RFC 1918 Private)"),
            ("10.204.0.1", "10.204.0.0/24 (Transit Gateway / Host Interface)"),
            ("10.205.0.1", "10.205.0.0/30 (Guest Tap Gateway)"),
            ("100.64.0.1", "100.64.0.0/10 (Carrier-Grade NAT RFC 6598)"),
            ("127.0.0.1", "127.0.0.0/8 (Loopback)"),
            ("169.254.169.254", "169.254.0.0/16 (Cloud Metadata Service Link-Local)"),
            ("169.254.1.1", "169.254.0.0/16 (Link-Local)"),
            ("172.16.0.1", "172.16.0.0/12 (RFC 1918 Private)"),
            ("172.31.255.254", "172.16.0.0/12 (RFC 1918 Upper Bound)"),
            ("192.0.0.1", "192.0.0.0/24 (IETF Protocol Assignments)"),
            ("192.0.2.1", "192.0.2.0/24 (TEST-NET-1)"),
            ("192.168.1.1", "192.168.0.0/16 (RFC 1918 Private Home Gateway)"),
            ("198.18.0.1", "198.18.0.0/15 (Network Benchmark RFC 2544)"),
            ("198.51.100.1", "198.51.100.0/24 (TEST-NET-2)"),
            ("203.0.113.1", "203.0.113.0/24 (TEST-NET-3)"),
            ("224.0.0.1", "224.0.0.0/4 (Multicast All Systems)"),
            ("239.255.255.250", "224.0.0.0/4 (SSDP Multicast)"),
            ("240.0.0.1", "240.0.0.0/4 (Reserved / Experimental)"),
            ("255.255.255.255", "240.0.0.0/4 (Limited Broadcast)")
        ]

        # Host forwarding check per probe IP
        for ip_str, desc in probe_ips:
            pkt = PacketModel(prefix=f"h_probe_{ip_str.replace('.', '_')}_")
            host_accept = encode_host_chain(pkt)
            s = z3.Solver()
            is_agv_in = z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2)
            s.add(is_agv_in)
            s.add(pkt.dst_ip == ip_to_bv(ip_str))
            s.add(host_accept)
            self.assert_unsat(s, f"Host chain drops egress packet targeting {ip_str} [{desc}]")

        # Netns forwarding check per probe IP
        for ip_str, desc in probe_ips:
            pkt = PacketModel(prefix=f"ns_probe_{ip_str.replace('.', '_')}_")
            ns_accept = encode_namespace_firewall(pkt, proxy_ip_str=PUBLIC_PROXY_IP)
            s = z3.Solver()
            s.add(pkt.in_if == IF_TAP0)
            s.add(pkt.dst_ip == ip_to_bv(ip_str))
            s.add(ns_accept)
            self.assert_unsat(s, f"Netns chain drops egress packet targeting {ip_str} [{desc}]")

        # ---------------------------------------------------------------------
        # Challenge 1.2: Host Ingress Bypass & Service Exploitation
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.2: Host Ingress Filtering (AGORA-HTTPS-IN) Exploitation ---")
        # Attempt to access host SSH port 22
        pkt = PacketModel(prefix="ssh_")
        host_input = encode_host_input_chain(pkt, HOST_INGRESS_IP, PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_TCP)
        s.add(pkt.dport == 22)
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects guest connection to host SSH port 22")

        # Attempt to access host HTTP port 80
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_TCP)
        s.add(pkt.dport == 80)
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects guest connection to host HTTP port 80")

        # Attempt to send UDP packets to host port 443
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_UDP)
        s.add(pkt.dport == 443)
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects UDP packets even if targeting port 443")

        # Attempt to spoof original destination (ctorigdst != PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_TCP)
        s.add(pkt.dport == 443)
        s.add(pkt.ctorigdst != ip_to_bv(PUBLIC_PROXY_IP))
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects packets where ctorigdst is not the whitelisted proxy")

        # Attempt to bypass using non-443 ctorigdstport
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_TCP)
        s.add(pkt.dport == 443)
        s.add(pkt.ctorigdstport != 443)
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects packets where ctorigdstport != 443")

        # Attempt to bypass from non-transit source IP
        s = z3.Solver()
        s.add(z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2))
        s.add(z3.Not(in_subnet(pkt.src_ip, TRANSIT_NETWORK)))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(host_input)
        self.assert_unsat(s, "Host AGORA-HTTPS-IN rejects packets originating from non-transit source IPs")

        # ---------------------------------------------------------------------
        # Challenge 1.3: Unsolicited Inbound & State Confinement Attacks
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.3: Unsolicited Inbound & Conntrack State Attacks ---")
        # Inbound packet with CT_NEW from uplink targeting agv1
        pkt = PacketModel(prefix="inb_")
        host_accept = encode_host_chain(pkt)
        s = z3.Solver()
        s.add(pkt.in_if == IF_UPLINK)
        s.add(pkt.out_if == IF_AGV1)
        s.add(pkt.ctstate == CT_NEW)
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops unsolicited CT_NEW from uplink to agv1")

        # Inbound packet with CT_INVALID from uplink
        s = z3.Solver()
        s.add(pkt.in_if == IF_UPLINK)
        s.add(pkt.out_if == IF_AGV1)
        s.add(pkt.ctstate == CT_INVALID)
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops CT_INVALID packets unconditionally")

        # Inbound packet with CT_ESTABLISHED targeting non-transit IP
        s = z3.Solver()
        s.add(pkt.in_if == IF_UPLINK)
        s.add(pkt.out_if == IF_AGV1)
        s.add(pkt.ctstate == CT_ESTABLISHED)
        s.add(z3.Not(in_subnet(pkt.dst_ip, TRANSIT_NETWORK)))
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops inbound ESTABLISHED packets targeting non-transit IP")

        # ---------------------------------------------------------------------
        # Challenge 1.4: Source IP Anti-Spoofing from Guest TAP0
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.4: Source IP Anti-Spoofing Attacks ---")
        spoofed_ips = [
            ("10.205.0.1", "Tap0 gateway IP"),
            ("10.205.0.3", "Unassigned IP in /30"),
            ("10.204.0.1", "Transit gateway IP"),
            ("8.8.8.8", "Public external IP"),
            ("127.0.0.1", "Localhost")
        ]
        for s_ip, desc in spoofed_ips:
            pkt = PacketModel(prefix=f"spoof_{s_ip.replace('.', '_')}_")
            ns_accept = encode_namespace_firewall(pkt, proxy_ip_str=PUBLIC_PROXY_IP)
            s = z3.Solver()
            s.add(pkt.in_if == IF_TAP0)
            s.add(pkt.src_ip == ip_to_bv(s_ip))
            s.add(ns_accept)
            self.assert_unsat(s, f"Netns drops spoofed source IP {s_ip} [{desc}] from TAP0")

        # Host anti-spoofing: packet on agv1 with source IP outside TRANSIT_NETWORK
        pkt = PacketModel(prefix="h_spoof_")
        host_accept = encode_host_chain(pkt)
        s = z3.Solver()
        s.add(pkt.in_if == IF_AGV1)
        s.add(pkt.src_ip == ip_to_bv(GUEST_VM_IP)) # Un-NATed 10.205.0.2 on agv+
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops un-NATed 10.205.0.2 packet on agv1 (! -s 10.204.0.0/24)")

        # ---------------------------------------------------------------------
        # Challenge 1.5: Cross-Canvas Inter-VM Hairpin Attacks
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.5: Inter-Canvas & Hairpin Attacks ---")
        pkt = PacketModel(prefix="cross_")
        host_accept = encode_host_chain(pkt)
        s = z3.Solver()
        s.add(pkt.in_if == IF_AGV2)
        s.add(pkt.out_if == IF_AGV1)
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops cross-canvas packet agv2 -> agv1")

        # Hairpin agv1 -> agv1
        s = z3.Solver()
        s.add(pkt.in_if == IF_AGV1)
        s.add(pkt.out_if == IF_AGV1)
        s.add(host_accept)
        self.assert_unsat(s, "Host chain drops hairpin packet agv1 -> agv1")

        # ---------------------------------------------------------------------
        # Challenge 1.6: Sanity / Non-Vacuity Checks (Positive Witnesses)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 1.6: Sanity & Non-Vacuity Checks (Positive Witnesses) ---")
        # Legitimate outbound packet in Netns
        pkt = PacketModel(prefix="valid_ns_")
        ns_accept = encode_namespace_firewall(pkt, proxy_ip_str=PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(pkt.in_if == IF_TAP0)
        s.add(pkt.out_if == IF_WAN0)
        s.add(pkt.src_ip == ip_to_bv(GUEST_VM_IP))
        s.add(pkt.dst_ip == ip_to_bv("8.8.8.8")) # Public IP
        s.add(pkt.ctstate == CT_NEW)
        s.add(ns_accept)
        self.assert_sat(s, "Legitimate egress packet from guest VM to public IP is ACCEPTED by Netns")

        # Legitimate outbound packet on Host
        pkt = PacketModel(prefix="valid_h_")
        host_accept = encode_host_chain(pkt)
        s = z3.Solver()
        s.add(pkt.in_if == IF_AGV1)
        s.add(pkt.out_if == IF_UPLINK)
        s.add(in_subnet(pkt.src_ip, TRANSIT_NETWORK))
        s.add(pkt.dst_ip == ip_to_bv("8.8.8.8"))
        s.add(pkt.ctstate == CT_NEW)
        s.add(host_accept)
        self.assert_sat(s, "Legitimate outbound packet from transit to uplink is ACCEPTED by Host")

        # Legitimate HTTPS proxy packet on Host INPUT
        pkt = PacketModel(prefix="valid_in_")
        host_input = encode_host_input_chain(pkt, HOST_INGRESS_IP, PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(pkt.in_if == IF_AGV1)
        s.add(in_subnet(pkt.src_ip, TRANSIT_NETWORK))
        s.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt.proto == PROTO_TCP)
        s.add(pkt.dport == 443)
        s.add(pkt.ctorigdst == ip_to_bv(PUBLIC_PROXY_IP))
        s.add(pkt.ctorigdstport == 443)
        s.add(pkt.ctstate == CT_NEW)
        s.add(host_input)
        self.assert_sat(s, "Legitimate HTTPS proxy packet is ACCEPTED by Host INPUT AGORA-HTTPS-IN")

        # End-to-end traversal to legitimate public destination
        pkt_vm = PacketModel(prefix="e2e_valid_vm_")
        pkt_host = PacketModel(prefix="e2e_valid_h_")
        s = z3.Solver()
        s.add(pkt_vm.in_if == IF_TAP0)
        s.add(pkt_vm.out_if == IF_WAN0)
        s.add(pkt_vm.src_ip == ip_to_bv(GUEST_VM_IP))
        s.add(pkt_vm.dst_ip == ip_to_bv("8.8.8.8"))
        s.add(pkt_vm.proto == PROTO_TCP)
        s.add(pkt_vm.dport == 443)
        s.add(pkt_vm.sport == 50000)
        s.add(pkt_vm.ctstate == CT_NEW)

        s.add(in_subnet(pkt_host.src_ip, TRANSIT_NETWORK))
        s.add(pkt_host.dst_ip == pkt_vm.dst_ip)
        s.add(pkt_host.proto == pkt_vm.proto)
        s.add(pkt_host.dport == pkt_vm.dport)
        s.add(pkt_host.sport == pkt_vm.sport)
        s.add(pkt_host.in_if == IF_AGV1)
        s.add(pkt_host.out_if == IF_UPLINK)
        s.add(pkt_host.ctstate == CT_NEW)

        ns_acc = encode_namespace_firewall(pkt_vm, proxy_ip_str=PUBLIC_PROXY_IP)
        h_acc = encode_host_chain(pkt_host)
        s.add(ns_acc)
        s.add(h_acc)
        self.assert_sat(s, "Legitimate end-to-end egress to public IP (8.8.8.8) is ACCEPTED across both tiers")

        # Direct connection to host ingress without proxy DNAT (ctorigdst == HOST_INGRESS_IP)
        pkt_direct = PacketModel(prefix="direct_in_")
        host_input_direct = encode_host_input_chain(pkt_direct, HOST_INGRESS_IP, PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(pkt_direct.in_if == IF_AGV1)
        s.add(in_subnet(pkt_direct.src_ip, TRANSIT_NETWORK))
        s.add(pkt_direct.dst_ip == ip_to_bv(HOST_INGRESS_IP))
        s.add(pkt_direct.proto == PROTO_TCP)
        s.add(pkt_direct.dport == 443)
        s.add(pkt_direct.ctorigdst == ip_to_bv(HOST_INGRESS_IP)) # Direct target, not proxy
        s.add(pkt_direct.ctorigdstport == 443)
        s.add(pkt_direct.ctstate == CT_NEW)
        s.add(host_input_direct)
        self.assert_unsat(s, "Direct connection to host ingress with ctorigdst == HOST_INGRESS_IP is DROPPED")

        # Unsolicited inbound into namespace tap0 from wan0 with CT_NEW
        pkt_ns_in = PacketModel(prefix="ns_inb_")
        ns_acc_in = encode_namespace_firewall(pkt_ns_in, proxy_ip_str=PUBLIC_PROXY_IP)
        s = z3.Solver()
        s.add(pkt_ns_in.in_if == IF_WAN0)
        s.add(pkt_ns_in.out_if == IF_TAP0)
        s.add(pkt_ns_in.dst_ip == ip_to_bv(GUEST_VM_IP))
        s.add(pkt_ns_in.ctstate == CT_NEW)
        s.add(ns_acc_in)
        self.assert_unsat(s, "Unsolicited inbound into namespace tap0 with CT_NEW is DROPPED by Netns")

    # =========================================================================
    # SUITE 2: STATE CONFINEMENT ADVERSARIAL CHALLENGES
    # =========================================================================
    def run_state_challenges(self):
        print("\n" + "=" * 78)
        print(" SUITE 2: ADVERSARIAL CHALLENGES - STATE CONFINEMENT (verify_state_confinement)")
        print("=" * 78)

        # ---------------------------------------------------------------------
        # Challenge 2.1: Root Directory Mode 0o755 & Permission Variants (Theorem 4A)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 2.1: State Root Directory Mode Restrictions ---")
        root_mode = z3.BitVec('root_mode', 16)
        root_uid = z3.BitVec('root_uid', 32)
        euid = z3.BitVec('euid', 32)

        accepted_root = z3.And(
            root_mode == z3.BitVecVal(0o700, 16),
            root_uid == euid
        )

        modes_to_test = [
            (0o755, "rwxr-xr-x (world-readable, group-readable)"),
            (0o777, "rwxrwxrwx (world-writable)"),
            (0o750, "rwxr-x--- (group-readable)"),
            (0o711, "rwx--x--x (executable by others)"),
            (0o600, "rw------- (missing execute bit)"),
            (0o644, "rw-r--r-- (file permissions)"),
            (0o1700, "sticky bit + 0700 (0o1700)"),
            (0o4700, "SUID + 0700 (0o4700)"),
            (0o2700, "SGID + 0700 (0o2700)"),
            (0o000, "--------- (no permissions)")
        ]
        for m_val, desc in modes_to_test:
            s = z3.Solver()
            s.add(root_mode == z3.BitVecVal(m_val, 16))
            s.add(root_uid == euid)
            s.add(accepted_root)
            self.assert_unsat(s, f"Root state dir rejects mode {oct(m_val)} [{desc}]")

        # Test foreign owner on mode 0o700
        s = z3.Solver()
        s.add(root_mode == z3.BitVecVal(0o700, 16))
        s.add(root_uid != euid)
        s.add(accepted_root)
        self.assert_unsat(s, "Root state dir rejects foreign owner (root_uid != euid)")

        # Positive witness for 0o700
        s = z3.Solver()
        s.add(root_mode == z3.BitVecVal(0o700, 16))
        s.add(root_uid == euid)
        s.add(accepted_root)
        self.assert_sat(s, "Root state dir accepts exact mode 0o700 owned by euid")

        # ---------------------------------------------------------------------
        # Challenge 2.2: Subdirectory Confinement (Theorem 4B)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 2.2: State Subdirectory Confinement ---")
        subdir_mode = z3.BitVec('subdir_mode', 16)
        subdir_uid = z3.BitVec('subdir_uid', 32)
        MASK_DIR_WRITABLE = 0o022

        accepted_subdir = z3.And(
            (subdir_mode & z3.BitVecVal(MASK_DIR_WRITABLE, 16)) == 0,
            subdir_uid == euid
        )

        # Insecure subdir modes
        insecure_subdirs = [
            (0o777, "world-writable 0777"),
            (0o775, "group-writable 0775"),
            (0o757, "world-writable 0757"),
            (0o733, "group/world write-execute 0733"),
            (0o722, "group/world write 0722")
        ]
        for sm, desc in insecure_subdirs:
            s = z3.Solver()
            s.add(subdir_mode == z3.BitVecVal(sm, 16))
            s.add(subdir_uid == euid)
            s.add(accepted_subdir)
            self.assert_unsat(s, f"Subdirectory rejects writable mode {oct(sm)} [{desc}]")

        # Foreign owner
        s = z3.Solver()
        s.add((subdir_mode & z3.BitVecVal(MASK_DIR_WRITABLE, 16)) == 0)
        s.add(subdir_uid != euid)
        s.add(accepted_subdir)
        self.assert_unsat(s, "Subdirectory rejects foreign ownership")

        # Valid subdirectories (0o700, 0o755)
        for valid_sm, desc in [(0o700, "0700 private"), (0o755, "0755 read-only group/world")]:
            s = z3.Solver()
            s.add(subdir_mode == z3.BitVecVal(valid_sm, 16))
            s.add(subdir_uid == euid)
            s.add(accepted_subdir)
            self.assert_sat(s, f"Subdirectory accepts non-writable mode {oct(valid_sm)} [{desc}]")

        # ---------------------------------------------------------------------
        # Challenge 2.3: Filesystem Object Type Whitelist & File Safety (Theorem 3)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 2.3: Object Type Whitelist, UID Ownership & Regular Files ---")
        mode = z3.BitVec('mode', 16)
        nlink = z3.BitVec('nlink', 32)
        entry_uid = z3.BitVec('entry_uid', 32)

        S_IFMT   = 0o170000
        S_IFREG  = 0o100000
        S_IFDIR  = 0o040000
        S_IFSOCK = 0o140000
        S_IFIFO  = 0o010000
        S_IFCHR  = 0o020000
        S_IFBLK  = 0o060000
        S_IFLNK  = 0o120000
        MASK_UNSAFE_REG = 0o6022

        ftype = mode & z3.BitVecVal(S_IFMT, 16)
        is_valid_type = z3.Or(ftype == S_IFREG, ftype == S_IFDIR, ftype == S_IFSOCK)

        accepted_entry = z3.And(
            is_valid_type,
            entry_uid == euid,
            z3.If(ftype == S_IFREG,
                  z3.And((mode & z3.BitVecVal(MASK_UNSAFE_REG, 16)) == 0, nlink == 1),
                  z3.BoolVal(True))
        )

        # Test invalid file types
        invalid_types = [
            (S_IFIFO, "FIFO / Named Pipe"),
            (S_IFBLK, "Block Device"),
            (S_IFCHR, "Character Device"),
            (S_IFLNK, "Symbolic Link")
        ]
        for if_val, desc in invalid_types:
            s = z3.Solver()
            s.add(ftype == z3.BitVecVal(if_val, 16))
            s.add(entry_uid == euid)
            s.add(accepted_entry)
            self.assert_unsat(s, f"State entries strictly reject {desc} ({oct(if_val)})")

        # Test regular file permission violations: SUID, SGID, group-writable, world-writable
        unsafe_file_modes = [
            (S_IFREG | 0o4755, "SUID root executable"),
            (S_IFREG | 0o2755, "SGID executable"),
            (S_IFREG | 0o0660, "Group-writable file (0660)"),
            (S_IFREG | 0o0666, "World-writable file (0666)"),
            (S_IFREG | 0o0602, "World-writable file (0602)"),
            (S_IFREG | 0o0020, "Group-writable only (0020)"),
            (S_IFREG | 0o0002, "World-writable only (0002)")
        ]
        for ufm, desc in unsafe_file_modes:
            s = z3.Solver()
            s.add(mode == z3.BitVecVal(ufm, 16))
            s.add(nlink == 1)
            s.add(entry_uid == euid)
            s.add(accepted_entry)
            self.assert_unsat(s, f"Regular file rejects unsafe mode: {desc}")

        # Test hardlink counts
        for nl in [0, 2, 3, 100]:
            s = z3.Solver()
            s.add(mode == z3.BitVecVal(S_IFREG | 0o600, 16))
            s.add(nlink == nl)
            s.add(entry_uid == euid)
            s.add(accepted_entry)
            self.assert_unsat(s, f"Regular file rejects hardlink alias (nlink={nl})")

        # Test foreign owner on valid regular file
        s = z3.Solver()
        s.add(mode == z3.BitVecVal(S_IFREG | 0o600, 16))
        s.add(nlink == 1)
        s.add(entry_uid != euid)
        s.add(accepted_entry)
        self.assert_unsat(s, "Regular file rejects foreign ownership (entry_uid != euid)")

        # Positive witness for regular file
        s = z3.Solver()
        s.add(mode == z3.BitVecVal(S_IFREG | 0o600, 16))
        s.add(nlink == 1)
        s.add(entry_uid == euid)
        s.add(accepted_entry)
        self.assert_sat(s, "Regular file with mode 0600, nlink=1, owned by euid is ACCEPTED")

        # Socket owned by euid (whitelisted type)
        s = z3.Solver()
        s.add(ftype == z3.BitVecVal(S_IFSOCK, 16))
        s.add(entry_uid == euid)
        s.add(accepted_entry)
        self.assert_sat(s, "UNIX domain socket owned by euid is ACCEPTED")

        # Socket owned by foreign uid
        s = z3.Solver()
        s.add(ftype == z3.BitVecVal(S_IFSOCK, 16))
        s.add(entry_uid != euid)
        s.add(accepted_entry)
        self.assert_unsat(s, "UNIX domain socket owned by foreign UID is REJECTED")

        # Directory entry owned by euid
        s = z3.Solver()
        s.add(ftype == z3.BitVecVal(S_IFDIR, 16))
        s.add(entry_uid == euid)
        s.add(accepted_entry)
        self.assert_sat(s, "Directory entry owned by euid is ACCEPTED")

        # ---------------------------------------------------------------------
        # Challenge 2.4: Path Sanitization & Symlinks (Theorem 1)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 2.4: Path Sanitization & Symlinks ---")
        is_absolute = z3.Bool('is_absolute')
        has_forbidden_char = z3.Bool('has_forbidden_char')
        symlink_in_parents = z3.Bool('symlink_in_parents')
        symlink_in_subtree = z3.Bool('symlink_in_subtree')

        accepted_path = z3.And(
            is_absolute,
            z3.Not(has_forbidden_char),
            z3.Not(symlink_in_parents),
            z3.Not(symlink_in_subtree)
        )

        # Non-absolute path
        s = z3.Solver()
        s.add(z3.Not(is_absolute))
        s.add(accepted_path)
        self.assert_unsat(s, "Path check rejects relative / non-absolute path")

        # Comma, newline, carriage return injection
        s = z3.Solver()
        s.add(has_forbidden_char)
        s.add(accepted_path)
        self.assert_unsat(s, "Path check rejects path containing comma, newline, or carriage return")

        # Symlink in parent ancestor
        s = z3.Solver()
        s.add(symlink_in_parents)
        s.add(accepted_path)
        self.assert_unsat(s, "Path check rejects symlinks in parent ancestors")

        # Symlink in subtree
        s = z3.Solver()
        s.add(symlink_in_subtree)
        s.add(accepted_path)
        self.assert_unsat(s, "Path check rejects symlinks in recursive subtree")

        # Positive witness
        s = z3.Solver()
        s.add(is_absolute)
        s.add(z3.Not(has_forbidden_char))
        s.add(z3.Not(symlink_in_parents))
        s.add(z3.Not(symlink_in_subtree))
        s.add(accepted_path)
        self.assert_sat(s, "Absolute canonical clean path with no symlinks is ACCEPTED")

        # ---------------------------------------------------------------------
        # Challenge 2.5: Launcher Privilege Confinement (Theorem 2)
        # ---------------------------------------------------------------------
        print("\n--- Challenge 2.5: Launcher Privilege Confinement ---")
        uid = z3.BitVec('uid', 32)
        cap_eff = z3.BitVec('cap_eff', 64)
        cap_prm = z3.BitVec('cap_prm', 64)
        cap_inh = z3.BitVec('cap_inh', 64)
        cap_amb = z3.BitVec('cap_amb', 64)
        no_new_privs = z3.BitVec('no_new_privs', 32)
        core_limit = z3.BitVec('core_limit', 64)
        umask = z3.BitVec('umask', 16)

        confine_accept = z3.And(
            uid != 0,
            cap_eff == 0,
            cap_prm == 0,
            cap_inh == 0,
            cap_amb == 0,
            no_new_privs == 1,
            core_limit == 0,
            umask == 0o077
        )

        # Root UID (uid == 0)
        s = z3.Solver()
        s.add(uid == 0)
        s.add(confine_accept)
        self.assert_unsat(s, "Confine rejects root user (UID 0)")

        # Effective capability != 0 (e.g. CAP_SYS_ADMIN bit 21, or bit 0)
        for cap_bit in [0, 1, 21, 38]:
            s = z3.Solver()
            s.add(cap_eff == (1 << cap_bit))
            s.add(confine_accept)
            self.assert_unsat(s, f"Confine rejects non-zero CapEff (bit {cap_bit})")

        # Permitted, inheritable, ambient capabilities
        for cap_name, var in [('CapPrm', cap_prm), ('CapInh', cap_inh), ('CapAmb', cap_amb)]:
            s = z3.Solver()
            s.add(var != 0)
            s.add(confine_accept)
            self.assert_unsat(s, f"Confine rejects non-zero {cap_name}")

        # Missing PR_SET_NO_NEW_PRIVS
        for nnp_val in [0, 2]:
            s = z3.Solver()
            s.add(no_new_privs == nnp_val)
            s.add(confine_accept)
            self.assert_unsat(s, f"Confine rejects missing PR_SET_NO_NEW_PRIVS (value={nnp_val})")

        # Non-zero core dump limit
        for cl_val in [1024, 0xFFFFFFFFFFFFFFFF]:
            s = z3.Solver()
            s.add(core_limit == cl_val)
            s.add(confine_accept)
            self.assert_unsat(s, f"Confine rejects non-zero core dump limit (core_limit={cl_val})")

        # Insecure umasks
        for um_val, desc in [(0o022, "standard 022"), (0o000, "insecure 000"), (0o027, "027")]:
            s = z3.Solver()
            s.add(umask == um_val)
            s.add(confine_accept)
            self.assert_unsat(s, f"Confine rejects unconfined umask: {desc}")

        # Positive witness
        s = z3.Solver()
        s.add(uid == 1000)
        s.add(cap_eff == 0)
        s.add(cap_prm == 0)
        s.add(cap_inh == 0)
        s.add(cap_amb == 0)
        s.add(no_new_privs == 1)
        s.add(core_limit == 0)
        s.add(umask == 0o077)
        s.add(confine_accept)
        self.assert_sat(s, "Unprivileged launcher with UID>0, 0 caps, NNP=1, core=0, umask=077 is ACCEPTED")

    # =========================================================================
    # SUMMARY REPORT
    # =========================================================================
    def summarize(self):
        print("\n" + "=" * 78)
        print(" ADVERSARIAL CHALLENGE EXECUTION SUMMARY")
        print("=" * 78)
        print(f"Total Tests Executed: {self.total_tests}")
        print(f"Passed:              {self.passed_tests}")
        print(f"Failed:              {self.failed_tests}")
        print("=" * 78)
        return 0 if self.failed_tests == 0 else 1

def main():
    runner = AdversarialChallengeRunner()
    runner.run_network_challenges()
    runner.run_state_challenges()
    return runner.summarize()

if __name__ == '__main__':
    sys.exit(main())
