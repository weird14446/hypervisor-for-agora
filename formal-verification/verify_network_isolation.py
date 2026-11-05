#!/usr/bin/env python3
"""
formal-verification/verify_network_isolation.py
Formal SMT Verification of Agora Hypervisor Network Isolation & Firewall Invariants.

Verifies the mathematical guarantees of the two-tier network architecture in runtime/network.py:
- Tier 1: Host-level iptables (FORWARD, AGORA-RUNTIME, AGORA-HTTPS-IN, AGORA-RUNTIME-NAT)
- Tier 2: Guest-namespace iptables (INPUT, FORWARD, AGORA-HTTPS, NAT)

Theorems Verified via Z3 SMT Solver:
  [Theorem 1] Egress Private Subnet Isolation:
              No packet from any guest VM can reach RFC1918, Link-Local (Cloud Metadata),
              Loopback, or documentation networks.
  [Theorem 2] Cross-Canvas Isolation (Inter-VM Non-Interference):
              No packet originating from Canvas C1 can be forwarded to Canvas C2.
  [Theorem 3] Unsolicited Inbound Confinement:
              No external packet with state NEW can be delivered to any guest VM.
  [Theorem 4] Guest Namespace Anti-Spoofing:
              Packets from tap0 with source IP != 10.205.0.2/32 are unconditionally dropped.
  [Theorem 5] Defense-in-Depth (Autonomous Namespace Confinement):
              Even if the host firewall were absent, the guest namespace firewall independently
              blocks all packets to BLOCKED networks (even with AGORA-HTTPS active).
  [Theorem 6] Host Ingress Confinement & HTTPS Proxy Whitelist Restriction:
              Host INPUT (AGORA-HTTPS-IN) unconditionally drops any packet targeting host
              services on ports other than 443 or non-TCP protocols; namespace AGORA-HTTPS
              strictly whitelists only TCP port 443.
  [Theorem 7] End-to-End Multi-Tier Forwarding & NAT Composition:
              Packets traversing from VM tap0 through namespace NAT and host forwarding/NAT
              can never reach any destination in BLOCKED networks.
"""
import ipaddress
import sys
import z3

# -----------------------------------------------------------------------------
# 1. BitVector IP and Subnet Modeling
# -----------------------------------------------------------------------------
def ip_to_bv(ip_str: str) -> z3.BitVecVal:
    return z3.BitVecVal(int(ipaddress.IPv4Address(ip_str)), 32)

def in_subnet(ip_bv: z3.BitVecRef, net_str: str) -> z3.BoolRef:
    net = ipaddress.IPv4Network(net_str, strict=False)
    net_val = int(net.network_address)
    mask = int(net.netmask)
    return (ip_bv & z3.BitVecVal(mask, 32)) == z3.BitVecVal(net_val, 32)

# Subnets directly extracted from runtime/network.py
BLOCKED_NETWORKS = [
    '0.0.0.0/8', '10.0.0.0/8', '100.64.0.0/10', '127.0.0.0/8',
    '169.254.0.0/16', '172.16.0.0/12', '192.0.0.0/24', '192.0.2.0/24',
    '192.168.0.0/16', '198.18.0.0/15', '198.51.100.0/24', '203.0.113.0/24',
    '224.0.0.0/4', '240.0.0.0/4'
]
TRANSIT_NETWORK = '10.204.0.0/24'
GUEST_TAP_IP = '10.205.0.1'
GUEST_VM_IP = '10.205.0.2'

# Valid globally routable public IPs (RFC 5737 / non-blocked, satisfying is_global == True)
PUBLIC_PROXY_IP = '93.184.216.34'      # Example public HTTPS proxy exception (example.com)
HOST_INGRESS_IP = '198.199.100.5'      # Host public uplink ingress IP

# Interface IDs
IF_TAP0    = 0
IF_WAN0    = 1
IF_AGV1    = 2  # Host veth for Canvas 1
IF_AGV2    = 3  # Host veth for Canvas 2
IF_UPLINK  = 4  # Host uplink interface (e.g. eth0)

# Conntrack states
CT_INVALID     = 0
CT_NEW         = 1
CT_ESTABLISHED = 2
CT_RELATED     = 3

# Protocols
PROTO_TCP = 6
PROTO_UDP = 17

# -----------------------------------------------------------------------------
# 2. Packet Flow Formal Encoding
# -----------------------------------------------------------------------------
class PacketModel:
    def __init__(self, prefix=""):
        self.src_ip = z3.BitVec(f"{prefix}src_ip", 32)
        self.dst_ip = z3.BitVec(f"{prefix}dst_ip", 32)
        self.proto = z3.BitVec(f"{prefix}proto", 8)
        self.dport = z3.BitVec(f"{prefix}dport", 16)
        self.sport = z3.BitVec(f"{prefix}sport", 16)
        self.in_if = z3.BitVec(f"{prefix}in_if", 8)
        self.out_if = z3.BitVec(f"{prefix}out_if", 8)
        self.ctstate = z3.BitVec(f"{prefix}ctstate", 4)
        self.ctorigdst = z3.BitVec(f"{prefix}ctorigdst", 32)
        self.ctorigdstport = z3.BitVec(f"{prefix}ctorigdstport", 16)


def encode_host_chain(pkt: PacketModel) -> z3.BoolRef:
    """
    Encodes the AGORA-RUNTIME forwarding chain on the host filter table.
    Mirrors runtime/network.py: firewall_up() AGORA-RUNTIME chain
    """
    is_agv_in = z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2)
    is_agv_out = z3.Or(pkt.out_if == IF_AGV1, pkt.out_if == IF_AGV2)

    is_blocked_dst = z3.Or(*[in_subnet(pkt.dst_ip, b) for b in BLOCKED_NETWORKS])
    in_transit_src = in_subnet(pkt.src_ip, TRANSIT_NETWORK)
    in_transit_dst = in_subnet(pkt.dst_ip, TRANSIT_NETWORK)

    # AGORA-RUNTIME Forwarding Chain Rules (evaluated sequentially):
    # Rule 1: -m conntrack --ctstate INVALID -j DROP
    r1_drop = (pkt.ctstate == CT_INVALID)

    # Rule 2: -i agv+ ! -s 10.204.0.0/24 -j DROP
    r2_drop = z3.And(is_agv_in, z3.Not(in_transit_src))

    # Rule 3: for network in blocked_networks: -i agv+ -d {network} -j DROP
    r3_drop = z3.And(is_agv_in, is_blocked_dst)

    # Rule 4: -i agv+ -o {uplink} -s {TRANSIT} -m conntrack --ctstate NEW,ESTABLISHED,RELATED -j ACCEPT
    r4_accept = z3.And(
        is_agv_in,
        pkt.out_if == IF_UPLINK,
        in_transit_src,
        z3.Or(pkt.ctstate == CT_NEW, pkt.ctstate == CT_ESTABLISHED, pkt.ctstate == CT_RELATED)
    )

    # Rule 5: -i {uplink} -o agv+ -d {TRANSIT} -m conntrack --ctstate ESTABLISHED,RELATED -j ACCEPT
    r5_accept = z3.And(
        pkt.in_if == IF_UPLINK,
        is_agv_out,
        in_transit_dst,
        z3.Or(pkt.ctstate == CT_ESTABLISHED, pkt.ctstate == CT_RELATED)
    )

    # Overall host forwarding accepted condition
    host_accepted = z3.And(
        z3.Not(r1_drop),
        z3.Not(r2_drop),
        z3.Not(r3_drop),
        z3.Or(
            r4_accept,
            z3.And(z3.Not(r4_accept), r5_accept)
        )
    )
    return host_accepted


def encode_host_input_chain(pkt: PacketModel, ingress_ip_str: str = HOST_INGRESS_IP, proxy_ip_str: str = PUBLIC_PROXY_IP) -> z3.BoolRef:
    """
    Encodes the AGORA-HTTPS-IN chain on host filter INPUT table.
    Mirrors runtime/network.py: firewall_up() AGORA-HTTPS-IN chain:
      -A AGORA-HTTPS-IN -i agv+ -s {TRANSIT} -d {ingress}/32 -p tcp --dport 443
         -m conntrack --ctorigdst {address} --ctorigdstport 443 --ctstate NEW,ESTABLISHED -j ACCEPT
      -A AGORA-HTTPS-IN -j DROP
    """
    is_agv_in = z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2)
    in_transit_src = in_subnet(pkt.src_ip, TRANSIT_NETWORK)
    is_ingress_dst = (pkt.dst_ip == ip_to_bv(ingress_ip_str))
    proxy_bv = ip_to_bv(proxy_ip_str)

    accept_rule = z3.And(
        is_agv_in,
        in_transit_src,
        is_ingress_dst,
        pkt.proto == PROTO_TCP,
        pkt.dport == 443,
        pkt.ctorigdst == proxy_bv,
        pkt.ctorigdstport == 443,
        z3.Or(pkt.ctstate == CT_NEW, pkt.ctstate == CT_ESTABLISHED)
    )
    # Default is DROP
    return accept_rule


def encode_https_proxy_filter(pkt: PacketModel, proxy_ip_str: str = PUBLIC_PROXY_IP) -> z3.BoolRef:
    """
    Encodes the AGORA-HTTPS exception chain in the namespace filter table:
    -A AGORA-HTTPS -i tap0 -o wan0 -s 10.205.0.2/32 -d {proxy}/32 -p tcp --dport 443
       -m conntrack --ctstate NEW,ESTABLISHED -j ACCEPT
    """
    proxy_bv = ip_to_bv(proxy_ip_str)
    rule_match = z3.And(
        pkt.in_if == IF_TAP0,
        pkt.out_if == IF_WAN0,
        pkt.src_ip == ip_to_bv(GUEST_VM_IP),
        pkt.dst_ip == proxy_bv,
        pkt.proto == PROTO_TCP,
        pkt.dport == 443,
        z3.Or(pkt.ctstate == CT_NEW, pkt.ctstate == CT_ESTABLISHED)
    )
    return rule_match


def encode_namespace_firewall(pkt: PacketModel, proxy_ip_str: str = None) -> z3.BoolRef:
    """
    Encodes the per-canvas netns internal iptables rules with AGORA-HTTPS hook.
    Mirrors runtime/network.py: up() and namespace_https()
    """
    # Rule 1: -j AGORA-HTTPS (inserted at rule 1 in FORWARD)
    if proxy_ip_str is not None:
        https_match = encode_https_proxy_filter(pkt, proxy_ip_str)
    else:
        https_match = z3.BoolVal(False)

    # Rule 2: -m conntrack --ctstate INVALID -j DROP
    r1_drop = (pkt.ctstate == CT_INVALID)

    # Rule 3: -i tap0 ! -s 10.205.0.2/32 -j DROP (Anti-spoofing)
    r2_drop = z3.And(pkt.in_if == IF_TAP0, pkt.src_ip != ip_to_bv(GUEST_VM_IP))

    # Rule 4: for network in blocked_networks: -A FORWARD -i tap0 -d {network} -j DROP
    is_blocked_dst = z3.Or(*[in_subnet(pkt.dst_ip, b) for b in BLOCKED_NETWORKS])
    r3_drop = z3.And(pkt.in_if == IF_TAP0, is_blocked_dst)

    # Rule 5: -A FORWARD -i tap0 -o wan0 -s 10.205.0.2/32 -m conntrack --ctstate NEW,EST,REL -j ACCEPT
    r4_accept = z3.And(
        pkt.in_if == IF_TAP0,
        pkt.out_if == IF_WAN0,
        pkt.src_ip == ip_to_bv(GUEST_VM_IP),
        z3.Or(pkt.ctstate == CT_NEW, pkt.ctstate == CT_ESTABLISHED, pkt.ctstate == CT_RELATED)
    )

    # Rule 6: -A FORWARD -i wan0 -o tap0 -d 10.205.0.2/32 -m conntrack --ctstate EST,REL -j ACCEPT
    r5_accept = z3.And(
        pkt.in_if == IF_WAN0,
        pkt.out_if == IF_TAP0,
        pkt.dst_ip == ip_to_bv(GUEST_VM_IP),
        z3.Or(pkt.ctstate == CT_ESTABLISHED, pkt.ctstate == CT_RELATED)
    )

    # Netns acceptance: either matched and accepted by AGORA-HTTPS, or passing FORWARD filter
    ns_accepted = z3.Or(
        https_match,
        z3.And(
            z3.Not(r1_drop),
            z3.Not(r2_drop),
            z3.Not(r3_drop),
            z3.Or(
                r4_accept,
                z3.And(z3.Not(r4_accept), r5_accept)
            )
        )
    )
    return ns_accepted


# -----------------------------------------------------------------------------
# 3. Formal Theorem Proving Suite
# -----------------------------------------------------------------------------
def run_all_theorems():
    print("=" * 72)
    print(" Agora Hypervisor: SMT Formal Network Isolation Verification (Z3) ")
    print("=" * 72)
    pkt = PacketModel()
    host_accept = encode_host_chain(pkt)
    ns_accept = encode_namespace_firewall(pkt, proxy_ip_str=PUBLIC_PROXY_IP)
    all_passed = True

    # -------------------------------------------------------------------------
    # Theorem 1: Egress Private Subnet Isolation
    # -------------------------------------------------------------------------
    print("\n[Theorem 1] Egress Private Subnet Isolation")
    print("  Claim: ∀p, In(p) ∈ {agv+} ∧ Dest(p) ∈ BLOCKED ⇒ ¬HostAccept(p)")
    s1 = z3.Solver()
    is_agv_in = z3.Or(pkt.in_if == IF_AGV1, pkt.in_if == IF_AGV2)
    is_blocked_dst = z3.Or(*[in_subnet(pkt.dst_ip, b) for b in BLOCKED_NETWORKS])
    s1.add(is_agv_in)
    s1.add(is_blocked_dst)
    s1.add(host_accept)
    res1 = s1.check()
    if res1 == z3.unsat:
        print("  Result: UNSAT (Proven) — No packet to RFC1918/Metadata/Loopback can be accepted.")
    else:
        print("  Result: SAT (Violation found!):", s1.model())
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 2: Cross-Canvas Isolation (Inter-VM Non-Interference)
    # -------------------------------------------------------------------------
    print("\n[Theorem 2] Cross-Canvas Isolation (Inter-VM Non-Interference)")
    print("  Claim: ∀p, In(p) = agv1 ∧ Out(p) = agv2 ⇒ ¬HostAccept(p)")
    s2 = z3.Solver()
    s2.add(pkt.in_if == IF_AGV1)
    s2.add(pkt.out_if == IF_AGV2)
    s2.add(host_accept)
    res2 = s2.check()
    if res2 == z3.unsat:
        print("  Result: UNSAT (Proven) — Canvas C1 can never route packets into Canvas C2.")
    else:
        print("  Result: SAT (Violation found!):", s2.model())
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 3: Unsolicited Inbound Confinement
    # -------------------------------------------------------------------------
    print("\n[Theorem 3] Unsolicited Inbound Confinement")
    print("  Claim: ∀p, In(p) = Uplink ∧ Out(p) ∈ {agv+} ∧ State(p) = NEW ⇒ ¬HostAccept(p)")
    s3 = z3.Solver()
    is_agv_out = z3.Or(pkt.out_if == IF_AGV1, pkt.out_if == IF_AGV2)
    s3.add(pkt.in_if == IF_UPLINK)
    s3.add(is_agv_out)
    s3.add(pkt.ctstate == CT_NEW)
    s3.add(host_accept)
    res3 = s3.check()
    if res3 == z3.unsat:
        print("  Result: UNSAT (Proven) — External actors cannot initiate new connections to VMs.")
    else:
        print("  Result: SAT (Violation found!):", s3.model())
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 4: Guest Namespace Anti-Spoofing
    # -------------------------------------------------------------------------
    print("\n[Theorem 4] Guest Namespace Anti-Spoofing")
    print("  Claim: ∀p, In(p) = tap0 ∧ Src(p) ≠ 10.205.0.2 ⇒ ¬NamespaceAccept(p)")
    s4 = z3.Solver()
    s4.add(pkt.in_if == IF_TAP0)
    s4.add(pkt.src_ip != ip_to_bv(GUEST_VM_IP))
    s4.add(ns_accept)
    res4 = s4.check()
    if res4 == z3.unsat:
        print("  Result: UNSAT (Proven) — Any spoofed source IP from guest VM is immediately dropped.")
    else:
        print("  Result: SAT (Violation found!):", s4.model())
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 5: Defense-in-Depth (Autonomous Namespace Confinement)
    # -------------------------------------------------------------------------
    print("\n[Theorem 5] Defense-in-Depth (Autonomous Namespace Confinement)")
    print("  Claim: ∀p, In(p) = tap0 ∧ Dest(p) ∈ BLOCKED ⇒ ¬NamespaceAccept(p)")
    s5 = z3.Solver()
    s5.add(pkt.in_if == IF_TAP0)
    s5.add(is_blocked_dst)
    s5.add(ns_accept)
    res5 = s5.check()
    if res5 == z3.unsat:
        print("  Result: UNSAT (Proven) — Namespace firewall independently stops all egress to BLOCKED subnets.")
    else:
        print("  Result: SAT (Violation found!):", s5.model())
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 6: Host Ingress Confinement & HTTPS Proxy Whitelist Restriction
    # -------------------------------------------------------------------------
    print("\n[Theorem 6] Host Ingress Confinement & HTTPS Proxy Whitelist Restriction")
    print("  Claim 6A (Host Ingress Confinement): ∀p, In(p) ∈ {agv+} ∧ Dest(p) = Ingress ∧ (Dport(p) ≠ 443 ∨ Proto(p) ≠ TCP) ⇒ ¬HostInputAccept(p)")
    print("  Claim 6B (Namespace Whitelist): ∀p, Dest(p) = Proxy ∧ (Dport(p) ≠ 443 ∨ Proto(p) ≠ TCP) ⇒ ¬AgoraHttpsAccept(p)")
    host_input_accept = encode_host_input_chain(pkt, ingress_ip_str=HOST_INGRESS_IP, proxy_ip_str=PUBLIC_PROXY_IP)

    # 6A: Host Ingress Confinement check
    s6a = z3.Solver()
    s6a.add(is_agv_in)
    s6a.add(pkt.dst_ip == ip_to_bv(HOST_INGRESS_IP))
    s6a.add(z3.Or(pkt.dport != 443, pkt.proto != PROTO_TCP))
    s6a.add(host_input_accept)
    res6a = s6a.check()

    # 6B: Namespace HTTPS Whitelist check
    https_match = encode_https_proxy_filter(pkt, proxy_ip_str=PUBLIC_PROXY_IP)
    s6b = z3.Solver()
    s6b.add(pkt.dst_ip == ip_to_bv(PUBLIC_PROXY_IP))
    s6b.add(z3.Or(pkt.dport != 443, pkt.proto != PROTO_TCP))
    s6b.add(https_match)
    res6b = s6b.check()

    if res6a == z3.unsat and res6b == z3.unsat:
        print("  Result: UNSAT (Proven) — Host AGORA-HTTPS-IN strictly rejects non-HTTPS packets to host services; AGORA-HTTPS strictly permits only TCP 443.")
    else:
        print("  Result: SAT (Violation found!): 6A:", res6a, "6B:", res6b)
        all_passed = False

    # -------------------------------------------------------------------------
    # Theorem 7: End-to-End Multi-Tier Forwarding & NAT Composition
    # -------------------------------------------------------------------------
    print("\n[Theorem 7] End-to-End Multi-Tier Forwarding & NAT Composition")
    print("  Claim: ∀p_vm, p_host, (ValidVMOrigin(p_vm) ∧ TransitNAT(p_vm, p_host) ∧ Dest(p_vm) ∈ BLOCKED) ⇒ ¬(NsForwardAccept(p_vm) ∧ HostForwardAccept(p_host))")
    pkt_vm = PacketModel(prefix="vm_")
    pkt_host = PacketModel(prefix="host_")

    s7 = z3.Solver()
    # VM packet arrives on tap0 from valid guest IP
    s7.add(pkt_vm.in_if == IF_TAP0)
    s7.add(pkt_vm.out_if == IF_WAN0)
    s7.add(pkt_vm.src_ip == ip_to_bv(GUEST_VM_IP))

    # Egress NAT relation: namespace NAT rewrites source IP to transit subnet 10.204.0.0/24
    s7.add(in_subnet(pkt_host.src_ip, TRANSIT_NETWORK))
    s7.add(pkt_host.dst_ip == pkt_vm.dst_ip)
    s7.add(pkt_host.proto == pkt_vm.proto)
    s7.add(pkt_host.dport == pkt_vm.dport)
    s7.add(pkt_host.sport == pkt_vm.sport)

    # Host packet arrives on veth (agv1) and targets uplink
    s7.add(pkt_host.in_if == IF_AGV1)
    s7.add(pkt_host.out_if == IF_UPLINK)

    # Destination is any blocked network
    is_blocked_vm_dst = z3.Or(*[in_subnet(pkt_vm.dst_ip, b) for b in BLOCKED_NETWORKS])
    s7.add(is_blocked_vm_dst)

    # Both tiers must accept for end-to-end traversal
    ns_forward_accept = encode_namespace_firewall(pkt_vm, proxy_ip_str=PUBLIC_PROXY_IP)
    host_forward_accept = encode_host_chain(pkt_host)
    s7.add(ns_forward_accept)
    s7.add(host_forward_accept)

    res7 = s7.check()
    if res7 == z3.unsat:
        print("  Result: UNSAT (Proven) — End-to-end multi-tier pipeline guarantees zero leakage of guest traffic into blocked subnets.")
    else:
        print("  Result: SAT (Violation found!):", s7.model())
        all_passed = False

    print("\n" + "=" * 72)
    if all_passed:
        print(" VERIFICATION COMPLETE: ALL 7 THEOREMS MATHEMATICALLY PROVEN (UNSAT) ")
    else:
        print(" VERIFICATION FAILED: Violations detected. ")
    print("=" * 72)
    return 0 if all_passed else 1

if __name__ == '__main__':
    sys.exit(run_all_theorems())
