theory Common_Primitive_Syntax
imports "../Datatype_Selectors"
        IpAddresses
        "../../Simple_Firewall/Primitives/Iface"
        L4_Protocol_Flags Ports Tagged_Packet Conntrack_State
begin

section\<open>Primitive Matchers: Interfaces, IP Space, Layer 4 Ports Matcher\<close>

text\<open>Primitive Match Conditions which only support interfaces, IPv4 addresses,  layer 4 protocols, and layer 4 ports.
\<close>


context
  notes [[typedef_overloaded]]
begin
  datatype 'i common_primitive =
    is_Src: Src (src_sel: "'i::len ipt_iprange") | 
    is_Dst: Dst (dst_sel: "'i::len ipt_iprange") |
    is_Iiface: IIface (iiface_sel: iface) |
    is_Oiface: OIface (oiface_sel: iface) |
    is_Prot: Prot (prot_sel: protocol) | 
    is_Src_Ports: Src_Ports (src_ports_sel: ipt_l4_ports) |
    is_Dst_Ports: Dst_Ports (dst_ports_sel: ipt_l4_ports) |
    is_MultiportPorts: MultiportPorts (multiportports_sel: ipt_l4_ports) |
    is_L4_Flags: L4_Flags (l4_flags_sel: ipt_tcp_flags) |
    is_CT_State: CT_State (ct_state_sel: "ctstate set") |
    is_Extra: Extra (extra_sel: string)
end


lemma wf_disc_sel_common_primitive: 
      "wf_disc_sel (is_Src_Ports, src_ports_sel) Src_Ports"
      "wf_disc_sel (is_Dst_Ports, dst_ports_sel) Dst_Ports"
      "wf_disc_sel (is_Src, src_sel) Src"
      "wf_disc_sel (is_Dst, dst_sel) Dst"
      "wf_disc_sel (is_Iiface, iiface_sel) IIface"
      "wf_disc_sel (is_Oiface, oiface_sel) OIface"
      "wf_disc_sel (is_Prot, prot_sel) Prot"
      "wf_disc_sel (is_L4_Flags, l4_flags_sel) L4_Flags"
      "wf_disc_sel (is_CT_State, ct_state_sel) CT_State"
      "wf_disc_sel (is_Extra, extra_sel) Extra"
      "wf_disc_sel (is_MultiportPorts, multiportports_sel) MultiportPorts"
  by(simp_all add: wf_disc_sel.simps)


  --"Example for a packet again:"
  value "\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'',
          p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
          p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_ACK},
          p_payload = ''GET / HTTP/1.0'',
          p_tag_ctstate = CT_Established\<rparr> :: 32 tagged_packet"




end
