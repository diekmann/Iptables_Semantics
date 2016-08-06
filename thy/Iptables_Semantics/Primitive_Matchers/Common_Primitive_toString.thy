theory Common_Primitive_toString
imports "../../Simple_Firewall/Primitives/Primitives_toString"
        Common_Primitive_Matcher
begin


section\<open>Firewall toString Functions\<close>

fun ipt_ipv4range_toString :: "32 ipt_iprange \<Rightarrow> string" where
  "ipt_ipv4range_toString (IpAddr ip) = ipv4addr_toString ip" |
  "ipt_ipv4range_toString (IpAddrNetmask ip n) = ipv4addr_toString ip@''/''@string_of_nat n"  |
  "ipt_ipv4range_toString (IpAddrRange ip1 ip2) = ipv4addr_toString ip1@''-''@ipv4addr_toString ip2"

fun ipt_ipv6range_toString :: "128 ipt_iprange \<Rightarrow> string" where
  "ipt_ipv6range_toString (IpAddr ip) = ipv6addr_toString ip" |
  "ipt_ipv6range_toString (IpAddrNetmask ip n) = ipv6addr_toString ip@''/''@string_of_nat n"  |
  "ipt_ipv6range_toString (IpAddrRange ip1 ip2) = ipv6addr_toString ip1@''-''@ipv6addr_toString ip2"

definition ipv4addr_wordinterval_pretty_toString :: "32 wordinterval \<Rightarrow> string" where
  "ipv4addr_wordinterval_pretty_toString wi = list_toString ipt_ipv4range_toString (wi_to_ipt_iprange wi)"

lemma "ipv4addr_wordinterval_pretty_toString 
    (RangeUnion (RangeUnion (WordInterval 0x7F000000 0x7FFFFFFF) (WordInterval 0x1020304 0x1020306))
                (WordInterval 0x8080808 0x8080808)) = ''[127.0.0.0/8, 1.2.3.4-1.2.3.6, 8.8.8.8]''" by eval
  


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
  "common_primitive_toString _ (Src_Ports (L4Ports prot pts)) = ''-m ''@primitive_protocol_toString prot@'' --spts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString _ (Dst_Ports (L4Ports prot pts)) = ''-m ''@primitive_protocol_toString prot@'' --dpts '' @ list_toString (ports_toString '''') pts" |
  "common_primitive_toString _ (CT_State S) = ''-m state --state ''@ctstate_set_toString S" |
  "common_primitive_toString _ (L4_Flags (TCP_Flags c m)) = ''--tcp-flags ''@ipt_tcp_flags_toString c@'' ''@ipt_tcp_flags_toString m" |
  "common_primitive_toString _ (Extra e) = ''~~''@e@''~~''"


definition common_primitive_ipv4_toString :: "32 common_primitive \<Rightarrow> string" where
  "common_primitive_ipv4_toString \<equiv> common_primitive_toString ipv4addr_toString"

definition common_primitive_ipv6_toString :: "128 common_primitive \<Rightarrow> string" where
  "common_primitive_ipv6_toString \<equiv> common_primitive_toString ipv6addr_toString"


fun common_primitive_match_expr_toString
  :: "('i common_primitive \<Rightarrow> string) \<Rightarrow> 'i common_primitive match_expr \<Rightarrow> string" where
  "common_primitive_match_expr_toString toStr MatchAny = ''''" |
  "common_primitive_match_expr_toString toStr (Match m) = toStr m" |
  "common_primitive_match_expr_toString toStr (MatchAnd m1 m2) =
      common_primitive_match_expr_toString toStr m1 @'' '' @ common_primitive_match_expr_toString toStr m2" |
  "common_primitive_match_expr_toString toStr (MatchNot (Match m)) = ''! ''@toStr m" |
  "common_primitive_match_expr_toString toStr (MatchNot m) = ''NOT (''@common_primitive_match_expr_toString toStr m@'')''"

definition common_primitive_match_expr_ipv4_toString :: "32 common_primitive match_expr \<Rightarrow> string" where
  "common_primitive_match_expr_ipv4_toString \<equiv> common_primitive_match_expr_toString common_primitive_ipv4_toString"

definition common_primitive_match_expr_ipv6_toString :: "128 common_primitive match_expr \<Rightarrow> string" where
  "common_primitive_match_expr_ipv6_toString \<equiv> common_primitive_match_expr_toString common_primitive_ipv6_toString"

fun common_primitive_rule_toString :: "32 common_primitive rule \<Rightarrow> string" where
  "common_primitive_rule_toString (Rule m a) = common_primitive_match_expr_ipv4_toString m @'' ''@action_toString a"


end
