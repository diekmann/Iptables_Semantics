theory Common_Primitive_toString
imports 
        "../Common/Lib_toString"
        "../Bitmagic/Lib_Word_toString"
        Common_Primitive_Matcher
begin


section\<open>Firewall toString Functions\<close>

fun dotteddecimal_toString :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> string" where
  "dotteddecimal_toString (a,b,c,d) = string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d"

definition ipv4addr_toString :: "ipv4addr \<Rightarrow> string" where
  "ipv4addr_toString ip = dotteddecimal_toString (dotdecimal_of_ipv4addr ip)"

(* TODO: does not really set the correct amount of ':'
definition ipv6addr_toString :: "ipv6addr \<Rightarrow> string" where
  "ipv6addr_toString ip = list_separated_toString '':''
      (\<lambda>pt. case pt of None \<Rightarrow> '':''
                    |  Some w \<Rightarrow> hex_string_of_word0 w)
      (ipv6_preferred_to_compressed (int_to_ipv6preferred ip))"

value[code] "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xDB8 0x0 0x0 0x8 0x800 0x200C 0x417A))"
value[code] "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0xFF01 0x0 0x0 0x0 0x0 0x0 0x0 0x101))"
value[code] "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0 0 0 0 0x8 0x800 0x200C 0x417A))"
value[code] "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xDB8 0 0 0 0 0 0))"
value[code] "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0 0 0 0 0 0 0 0))"
*)


text\<open>Generic function. Whenever possible, use IPv4 or IPv6 pretty printing!\<close>
definition ipaddr_generic_toString :: "'i::len word \<Rightarrow> string" where
  "ipaddr_generic_toString ip \<equiv>
    ''[IP address ('' @ string_of_nat (len_of TYPE('i)) @ '' bit): '' @ string_of_nat (unat ip) @ '']''"

lemma "ipaddr_generic_toString (ipv4addr_of_dotdecimal (192,168,0,1)) = ''[IP address (32 bit): 3232235521]''" by eval

definition ipv4_cidr_toString :: "(ipv4addr \<times> nat) \<Rightarrow> string" where
  "ipv4_cidr_toString ip_n = (case ip_n of (base, n) \<Rightarrow>  (ipv4addr_toString base @''/''@ string_of_nat n))"

lemma "ipv4_cidr_toString (ipv4addr_of_dotdecimal (192,168,0,1), 22) = ''192.168.0.1/22''" by eval


fun ipt_ipv4range_toString :: "32 ipt_iprange \<Rightarrow> string" where
  "ipt_ipv4range_toString (IpAddr ip) = ipv4addr_toString ip" |
  "ipt_ipv4range_toString (IpAddrNetmask ip n) = ipv4addr_toString ip@''/''@string_of_nat n"  |
  "ipt_ipv4range_toString (IpAddrRange ip1 ip2) = ipv4addr_toString ip1@''-''@ipv4addr_toString ip2"


fun ipv4addr_wordinterval_toString :: "32 wordinterval \<Rightarrow> string" where
  "ipv4addr_wordinterval_toString (WordInterval s e) = (if s = e then ipv4addr_toString s else ''{''@ipv4addr_toString s@'' .. ''@ipv4addr_toString e@''}'')" |
  "ipv4addr_wordinterval_toString (RangeUnion a b) = ipv4addr_wordinterval_toString a @ '' u ''@ipv4addr_wordinterval_toString b"


definition ipv4addr_wordinterval_pretty_toString :: "32 wordinterval \<Rightarrow> string" where
  "ipv4addr_wordinterval_pretty_toString wi = list_toString ipt_ipv4range_toString (wi_to_ipt_iprange wi)"

lemma "ipv4addr_wordinterval_pretty_toString 
    (RangeUnion (RangeUnion (WordInterval 0x7F000000 0x7FFFFFFF) (WordInterval 0x1020304 0x1020306))
                (WordInterval 0x8080808 0x8080808)) = ''[127.0.0.0/8, 1.2.3.4-1.2.3.6, 8.8.8.8]''" by eval


fun protocol_toString :: "protocol \<Rightarrow> string" where
  "protocol_toString (ProtoAny) = ''all''" |
  "protocol_toString (Proto protid) = ( 
  if protid = TCP then ''tcp'' else
  if protid = UDP then ''udp'' else
  if protid = ICMP then ''icmp'' else
  if protid = SCTP then ''sctp'' else
  ''protocolid:''@string_of_nat (unat protid))"
  


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



fun common_primitive_toString :: "('i::len word \<Rightarrow> string) \<Rightarrow> 'i common_primitive \<Rightarrow> string" where
  "common_primitive_toString ipToStr (Src (IpAddr ip)) = ''-s ''@ipToStr ip" |
  "common_primitive_toString ipToStr (Dst (IpAddr ip)) = ''-d ''@ipToStr ip" |
  "common_primitive_toString ipToStr (Src (IpAddrNetmask ip n)) = ''-s ''@ipToStr ip@''/''@string_of_nat n"  |
  "common_primitive_toString ipToStr (Dst (IpAddrNetmask ip n)) = ''-d ''@ipToStr ip@''/''@string_of_nat n"  |
  "common_primitive_toString ipToStr (Src (IpAddrRange ip1 ip2)) = ''-m iprange --src-range ''@ipToStr ip1@''-''@ipToStr ip2"  |
  "common_primitive_toString ipToStr (Dst (IpAddrRange ip1 ip2)) = ''-m iprange --dst-range ''@ipToStr ip1@''-''@ipToStr ip2"  |
  "common_primitive_toString _ (IIface ifce) = iface_toString ''-i '' ifce" |
  "common_primitive_toString _ (OIface ifce) = iface_toString ''-o '' ifce" |
  "common_primitive_toString _ (Prot prot) = ''-p ''@protocol_toString prot" |
  "common_primitive_toString _ (Src_Ports pts) = ''--spts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString _ (Dst_Ports pts) = ''--dpts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString _ (CT_State S) = ''-m state --state ''@ctstate_set_toString S" |
  "common_primitive_toString _ (L4_Flags (TCP_Flags c m)) = ''--tcp-flags ''@ipt_tcp_flags_toString c@'' ''@ipt_tcp_flags_toString m" |
  "common_primitive_toString _ (Extra e) = ''~~''@e@''~~''"


definition common_primitive_v4_toString :: "32 common_primitive \<Rightarrow> string" where
  "common_primitive_v4_toString \<equiv> common_primitive_toString ipv4addr_toString"

fun common_primitive_match_expr_toString :: "32 common_primitive match_expr \<Rightarrow> string" where
  "common_primitive_match_expr_toString MatchAny = ''''" |
  "common_primitive_match_expr_toString (Match m) = common_primitive_v4_toString m" |
  "common_primitive_match_expr_toString (MatchAnd m1 m2) = common_primitive_match_expr_toString m1 @'' '' @ common_primitive_match_expr_toString m2" |
  "common_primitive_match_expr_toString (MatchNot (Match m)) = ''! ''@common_primitive_v4_toString m" |
  "common_primitive_match_expr_toString (MatchNot m) = ''NOT (''@common_primitive_match_expr_toString m@'')''"

fun common_primitive_rule_toString :: "32 common_primitive rule \<Rightarrow> string" where
  "common_primitive_rule_toString (Rule m a) = common_primitive_match_expr_toString m @'' ''@action_toString a"


end
