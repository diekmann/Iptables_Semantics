theory IPPortSpace_Syntax
imports Main String "../Bitmagic/IPv4Addr" IPSpace_Syntax
begin

section{*Primitive Matchers: IP Space and Layer 4 Ports Matcher*}

text{*Primitive Match Conditions which only support IPv4 addresses,  layer 4 protocols, and layer 4 ports.
*}

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP

datatype ipt_ports = PortSingle nat | PortRange nat nat | PortMulti "ipt_ports list"

datatype ipport_rule_match = Src ipt_ipv4range | Dst ipt_ipv4range | Prot ipt_protocol | Src_Port ipt_ports | Dst_Port ipt_ports | Extra string



subsection{*Example Packet*}
  record packet_with_ports = packet +
        src_port :: nat
        dst_port :: nat

  value "\<lparr>src_ip = ipv4addr_of_dotteddecimal (192,168,2,45), dst_ip= ipv4addr_of_dotteddecimal (173,194,112,111),
         prot=protPacket.ProtTCP, src_port=2065, dst_port=80\<rparr>"




fun ports_to_set :: "ipt_ports \<Rightarrow> nat set" where
  "ports_to_set (PortSingle p) = { p }" |
  "ports_to_set (PortRange p1 p2) = {p1 .. p2}" |
  "ports_to_set (PortMulti ps) = (\<Union> p \<in> set ps. ports_to_set p)"

lemma "ports_to_set (PortMulti ps) = \<Union> set [ports_to_set p. p \<leftarrow> ps]" by(simp)


end
