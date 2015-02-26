theory Common_Primitive_Syntax
imports "../Datatype_Selectors" IpAddresses Iface Protocol Ports Simple_Packet
begin

section{*Primitive Matchers: Interfaces, IP Space, Layer 4 Ports Matcher*}

text{*Primitive Match Conditions which only support interfaces, IPv4 addresses,  layer 4 protocols, and layer 4 ports.
*}


datatype_new common_primitive =
  is_Src: Src (src_sel: ipt_ipv4range) | 
  is_Dst: Dst (dst_sel: ipt_ipv4range) |
  is_Iiface: IIface (iiface_sel: iface) |
  is_Oiface: OIface (oiface_sel: iface) |
  is_Prot: Prot (prot_sel: protocol) | 
  is_Src_Ports: Src_Ports (src_ports_sel: ipt_ports) | 
  is_Dst_Ports: Dst_Ports (dst_ports_sel: ipt_ports) | 
  is_Extra: Extra (extra_sel: string)



lemma wf_disc_sel_common_primitive[simp]: 
      "wf_disc_sel (is_Src_Ports, src_ports_sel) Src_Ports"
      "wf_disc_sel (is_Dst_Ports, dst_ports_sel) Dst_Ports"
      "wf_disc_sel (is_Src, src_sel) Src"
      "wf_disc_sel (is_Iiface, iiface_sel) IIface"
      "wf_disc_sel (is_Oiface, oiface_sel) OIface"
      "wf_disc_sel (is_Prot, prot_sel) Prot"
      "wf_disc_sel (is_Extra, extra_sel) Extra"
  by(simp_all add: wf_disc_sel.simps)


(*subsection{*Example Packet*}*)
 (*TODO: unify: packet + *)

  value "\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
         p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"




end
