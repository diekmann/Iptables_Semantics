theory Common_Primitive_toString
imports 
        "../Common/Lib_toString"
        Common_Primitive_Matcher
begin


section{*Firewall toString Functions*}

definition ipv4_cidr_toString :: "(ipv4addr \<times> nat) \<Rightarrow> string" where
  "ipv4_cidr_toString ip_n = (case ip_n of (base, n) \<Rightarrow> 
      (case dotdecimal_of_ipv4addr base of (a,b,c,d) \<Rightarrow> string_of_nat a @''.''@ string_of_nat b @''.''@ string_of_nat c @''.''@ string_of_nat d
          @''/''@ string_of_nat n))"
lemma "ipv4_cidr_toString (ipv4addr_of_dotdecimal (192,168,0,1), 22) = ''192.168.0.1/22''" by eval

fun protocol_toString :: "protocol \<Rightarrow> string" where
  "protocol_toString (ProtoAny) = ''all''" |
  "protocol_toString (Proto TCP) = ''tcp''" |
  "protocol_toString (Proto UDP) = ''udp''" |
  "protocol_toString (Proto ICMP) = ''icmp''"


fun action_toString :: "action \<Rightarrow> string" where
  "action_toString action.Accept = ''-j ACCEPT''" |
  "action_toString action.Drop = ''-j DROP''" |
  "action_toString action.Reject = ''-j REJECT''" |
  "action_toString (action.Call target) = ''-j ''@target@'' (call)''" |
  "action_toString (action.Goto target) = ''-g ''@target" |
  "action_toString action.Empty = ''''" |
  "action_toString action.Log = ''-j LOG''" |
  "action_toString action.Return = ''-j RETURN''" |
  "action_toString action.Unknown = ''!!!!!!!!!!! UNKNOWN !!!!!!!!!!!''"

definition port_toString :: "16 word \<Rightarrow> string" where
  "port_toString p \<equiv> string_of_nat (unat p)"

definition iface_toString :: "string \<Rightarrow> iface \<Rightarrow> string" where
  "iface_toString descr iface = (if iface = ifaceAny then '''' else
      (case iface of (Iface name) \<Rightarrow> descr@name))"
lemma "iface_toString ''in: '' (Iface ''+'') = ''''" by eval
lemma "iface_toString ''in: '' (Iface ''eth0'') = ''in: eth0''" by eval

fun ports_toString :: "string \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> string" where
  "ports_toString descr (s,e) = (if s = 0 \<and> e = max_word then '''' else descr @ (if s=e then port_toString s else port_toString s@'':''@port_toString e))"
lemma "ports_toString ''spt: '' (0,65535) = ''''" by eval
lemma "ports_toString ''spt: '' (1024,2048) = ''spt: 1024:2048''" by eval
lemma "ports_toString ''spt: '' (1024,1024) = ''spt: 1024''" by eval

fun dotteddecimal_toString :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> string" where
  "dotteddecimal_toString (a,b,c,d) = string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d"

fun common_primitive_toString :: "common_primitive \<Rightarrow> string" where
  "common_primitive_toString (Src (Ip4Addr ip)) = ''-s ''@dotteddecimal_toString ip" |
  "common_primitive_toString (Dst (Ip4Addr ip)) = ''-d ''@dotteddecimal_toString ip" |
  "common_primitive_toString (Src (Ip4AddrNetmask ip n)) = ''-s ''@dotteddecimal_toString ip@''/''@string_of_nat n"  |
  "common_primitive_toString (Dst (Ip4AddrNetmask ip n)) = ''-d ''@dotteddecimal_toString ip@''/''@string_of_nat n"  |
  "common_primitive_toString (Src (Ip4AddrRange ip1 ip2)) = ''-m iprange --src-range ''@dotteddecimal_toString ip1@''-''@dotteddecimal_toString ip2"  |
  "common_primitive_toString (Dst (Ip4AddrRange ip1 ip2)) = ''-m iprange --dst-range ''@dotteddecimal_toString ip1@''-''@dotteddecimal_toString ip2"  |
  "common_primitive_toString (IIface ifce) = iface_toString ''-i '' ifce" |
  "common_primitive_toString (OIface ifce) = iface_toString ''-o '' ifce" |
  "common_primitive_toString (Prot prot) = ''-p ''@protocol_toString prot" |
  "common_primitive_toString (Src_Ports pts) = ''--spts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString (Dst_Ports pts) = ''--dpts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString (CT_State S) = ''-m state --state ''@ctstate_set_toString S" |
  "common_primitive_toString (Extra e) = ''~~''@e@''~~''"


fun common_primitive_match_expr_toString :: "common_primitive match_expr \<Rightarrow> string" where
  "common_primitive_match_expr_toString MatchAny = ''''" |
  "common_primitive_match_expr_toString (Match m) = common_primitive_toString m" |
  "common_primitive_match_expr_toString (MatchAnd m1 m2) = common_primitive_match_expr_toString m1 @'' '' @ common_primitive_match_expr_toString m2" |
  "common_primitive_match_expr_toString (MatchNot (Match m)) = ''! ''@common_primitive_toString m" |
  "common_primitive_match_expr_toString (MatchNot m) = ''NOT (''@common_primitive_match_expr_toString m@'')''"

fun common_primitive_rule_toString :: "common_primitive rule \<Rightarrow> string" where
  "common_primitive_rule_toString (Rule m a) = common_primitive_match_expr_toString m @'' ''@action_toString a"
  

end
