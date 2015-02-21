theory IPSpace_Syntax
imports Main String "../Datatype_Selectors" IpAddresses
begin

section{*Primitive Matchers: IP Space Matcher*}

text{*Primitive Match Conditions which only support IPv4 addresses and layer 4 protocols.
Used to partition the IPv4 address space.
*}

(*IPT \<equiv> iptables*)

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP

(*datatype ipt_ports = PortSingle nat | PortRange nat nat | PortMulti "ipt_ports list"*)

datatype_new iptrule_match = 
    is_Src: Src (src_range: ipt_ipv4range)
  | is_Dst: Dst (dst_range: ipt_ipv4range)
  | is_Prot: Prot (prot_sel: ipt_protocol)
  (*| Port ipt_ports*)
  | is_Extra: Extra (extra_sel: string)

(*datatype_compat iptrule_match*)


lemma wf_disc_sel_iptrule_match[simp]: 
      "wf_disc_sel (is_Src, src_range) Src"
      "wf_disc_sel (is_Dst, dst_range) Dst"
      "wf_disc_sel (is_Prot, prot_sel) Prot"
      "wf_disc_sel (is_Extra, extra_sel) Extra"
  by(simp_all add: wf_disc_sel.simps)


subsection{*Example Packet*}
  datatype protPacket = ProtTCP | ProtUDP
  record packet = src_ip :: ipv4addr
                  dst_ip :: ipv4addr
                  prot :: protPacket


hide_const (open) ProtTCP ProtUDP


end
