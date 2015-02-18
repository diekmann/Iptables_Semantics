theory IPPortIfaceSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr" IPSpace_Syntax Protocol Iface Ports Simple_Packet
begin

(*TODO: unify protocol types*)
hide_type(open) ipt_protocol
hide_const(open) ProtAll ProtTCP ProtUDP

section{*Primitive Matchers: Interfaces, IP Space, Layer 4 Ports Matcher*}

text{*Primitive Match Conditions which only support interfaces, IPv4 addresses,  layer 4 protocols, and layer 4 ports.
*}


datatype_new common_primitive = Src ipt_ipv4range | Dst ipt_ipv4range | IIface iface | OIface iface | Prot protocol | 
  is_Src_Ports: Src_Ports (src_ports_sel: ipt_ports) | 
  is_Dst_Ports: Dst_Ports (dst_ports_sel: ipt_ports) | 
  Extra string



lemma wf_disc_sel_common_primitive[simp]: 
      "wf_disc_sel (is_Src_Ports, src_ports_sel) Src_Ports"
      "wf_disc_sel (is_Dst_Ports, dst_ports_sel) Dst_Ports"
  by(simp_all add: wf_disc_sel.simps)


(*subsection{*Example Packet*}*)
 (*TODO: unify: packet + *)

  value "\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotteddecimal (192,168,2,45), p_dst= ipv4addr_of_dotteddecimal (173,194,112,111),
         p_proto=TCP, p_sport=2065, p_dport=80\<rparr>"




end
