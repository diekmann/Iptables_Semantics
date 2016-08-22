section\<open>toString Functions for Primitives\<close>
theory Primitives_toString
imports "../Common/Lib_Enum_toString"
        "../../IP_Addresses/IP_Address_toString"
        Iface
        L4_Protocol
begin


definition ipv4_cidr_toString :: "(ipv4addr \<times> nat) \<Rightarrow> string" where
  "ipv4_cidr_toString ip_n = (case ip_n of (base, n) \<Rightarrow>  (ipv4addr_toString base @''/''@ string_of_nat n))"
lemma "ipv4_cidr_toString (ipv4addr_of_dotdecimal (192,168,0,1), 22) = ''192.168.0.1/22''" by eval

definition ipv6_cidr_toString :: "(ipv6addr \<times> nat) \<Rightarrow> string" where
  "ipv6_cidr_toString ip_n = (case ip_n of (base, n) \<Rightarrow>  (ipv6addr_toString base @''/''@ string_of_nat n))"
lemma "ipv6_cidr_toString (42540766411282592856906245548098208122, 64) = ''2001:db8::8:800:200c:417a/64''" by eval

definition primitive_protocol_toString :: "primitive_protocol \<Rightarrow> string" where
  "primitive_protocol_toString protid \<equiv> ( 
  if protid = TCP then ''tcp'' else
  if protid = UDP then ''udp'' else
  if protid = ICMP then ''icmp'' else
  if protid = L4_Protocol.SCTP then ''sctp'' else
  if protid = L4_Protocol.IGMP then ''igmp'' else
  if protid = L4_Protocol.GRE then ''gre'' else
  if protid = L4_Protocol.ESP then ''esp'' else
  if protid = L4_Protocol.AH then ''ah'' else
  if protid = L4_Protocol.IPv6ICMP then ''ipv6-icmp'' else
  ''protocolid:''@dec_string_of_word0 protid)"

fun protocol_toString :: "protocol \<Rightarrow> string" where
  "protocol_toString (ProtoAny) = ''all''" |
  "protocol_toString (Proto protid) = primitive_protocol_toString protid"

definition iface_toString :: "string \<Rightarrow> iface \<Rightarrow> string" where
  "iface_toString descr iface = (if iface = ifaceAny then '''' else
      (case iface of (Iface name) \<Rightarrow> descr@name))"
lemma "iface_toString ''in: '' (Iface ''+'') = ''''" by eval
lemma "iface_toString ''in: '' (Iface ''eth0'') = ''in: eth0''" by eval

definition port_toString :: "16 word \<Rightarrow> string" where
  "port_toString p \<equiv> dec_string_of_word0 p"

fun ports_toString :: "string \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> string" where
  "ports_toString descr (s,e) = (if s = 0 \<and> e = max_word then '''' else descr @ (if s=e then port_toString s else port_toString s@'':''@port_toString e))"
lemma "ports_toString ''spt: '' (0,65535) = ''''" by eval
lemma "ports_toString ''spt: '' (1024,2048) = ''spt: 1024:2048''" by eval
lemma "ports_toString ''spt: '' (1024,1024) = ''spt: 1024''" by eval

definition ipv4_cidr_opt_toString :: "string \<Rightarrow> ipv4addr \<times> nat \<Rightarrow> string" where
  "ipv4_cidr_opt_toString descr ip = (if ip = (0,0) then '''' else
      descr@ipv4_cidr_toString ip)"

definition protocol_opt_toString :: "string \<Rightarrow> protocol \<Rightarrow> string" where
  "protocol_opt_toString descr prot = (if prot = ProtoAny then '''' else
      descr@protocol_toString prot)"

end
