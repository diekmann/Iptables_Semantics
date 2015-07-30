theory Firewall_toString
imports 
        "../Primitive_Matchers/Common_Primitive_Matcher"
        "../Simple_Firewall/SimpleFw_Semantics"
begin


section{*Firewall toString Functions*}

(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"
definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

definition list_toString :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_toString toStr ls = ''[''@ concat (splice (map toStr ls) (replicate (length ls - 1) '', ''))  @'']''"

lemma "list_toString string_of_nat [1,2,3] = ''[1, 2, 3]''" by eval

(*HACK: rewrite quotes such that they are better printable by Isabelle*)
definition quote_rewrite :: "string \<Rightarrow> string" where
  "quote_rewrite \<equiv> map (\<lambda>c. if c = Char Nibble2 Nibble2 then CHR ''~'' else c)"
value "quote_rewrite (''foo''@[Char Nibble2 Nibble2])"

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

fun simple_action_toString :: "simple_action \<Rightarrow> string" where
  "simple_action_toString Accept = ''ACCEPT''" |
  "simple_action_toString Drop = ''DROP''"


fun action_toString :: "action \<Rightarrow> string" where
  "action_toString action.Accept = ''-j ACCEPT''" |
  "action_toString action.Drop = ''-j DROP''" |
  "action_toString action.Reject = ''-j REJECT''" |
  "action_toString (action.Call target) = ''-j ''@target@'' (call)''" |
  "action_toString (action.Goto target) = ''-g ''@target" |
  "action_toString action.Empty = ''''" |
  "action_toString action.Log = ''-j LOG''" |
  "action_toString action.Return = ''-j RETUNRN''" |
  "action_toString action.Unknown = ''!!!!!!!!!!! UNKNOWN !!!!!!!!!!!''"

definition port_toString :: "16 word \<Rightarrow> string" where
  "port_toString p \<equiv> string_of_nat (unat p)"

definition iface_toString :: "string \<Rightarrow> iface \<Rightarrow> string" where
  "iface_toString descr iface = (if iface = ifaceAny then '''' else
      (case iface of (Iface name) \<Rightarrow> descr@name))"
lemma "iface_toString ''in: '' (Iface ''+'') = ''''" by eval
lemma "iface_toString ''in: '' (Iface ''eth0'') = ''in: eth0''" by eval

fun ports_toString :: "string \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> string" where
  "ports_toString descr (s,e) = (if s = 0 \<and> e = max_word then '''' else descr@''(''@port_toString s@'',''@port_toString e@'')'')"
lemma "ports_toString ''spt: '' (0,65535) = ''''" by eval
lemma "ports_toString ''spt: '' (1024,2048) = ''spt: (1024,2048)''" by eval


fun common_primitive_toString :: "common_primitive \<Rightarrow> string" where
  "common_primitive_toString (Src (Ip4Addr (a,b,c,d))) = ''-s ''@string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d" |
  "common_primitive_toString (Dst (Ip4Addr (a,b,c,d))) = ''-d ''@string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d" |
  "common_primitive_toString (Src (Ip4AddrNetmask (a,b,c,d) n)) =
      ''-s ''@string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d@''/''@string_of_nat n"  |
  "common_primitive_toString (Dst (Ip4AddrNetmask (a,b,c,d) n)) =
      ''-d ''@string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d@''/''@string_of_nat n"  |
  "common_primitive_toString (IIface ifce) = iface_toString ''-i '' ifce" |
  "common_primitive_toString (OIface ifce) = iface_toString ''-o '' ifce" |
  "common_primitive_toString (Prot prot) = ''-p ''@protocol_toString prot" |
  "common_primitive_toString (Src_Ports pts) = list_toString (ports_toString ''--spts '') pts" |
  "common_primitive_toString (Dst_Ports pts) = list_toString (ports_toString ''--dpts '') pts" |
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
  

fun simple_rule_toString :: "simple_rule \<Rightarrow> string" where
  "simple_rule_toString (SimpleRule \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> a) = 
      simple_action_toString a @ ''     '' @ 
      protocol_toString p @ ''  --  '' @ 
      ipv4_cidr_toString sip @ ''            '' @
      ipv4_cidr_toString dip @ '' '' @ 
      iface_toString ''in: '' iif @ '' '' @ 
      iface_toString ''out: '' oif @ '' '' @ 
      ports_toString ''sports: '' sps @ '' '' @ 
      ports_toString ''dports: '' dps"


fun simple_rule_iptables_save_toString :: "string \<Rightarrow> simple_rule \<Rightarrow> string" where
  "simple_rule_iptables_save_toString chain (SimpleRule \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> a) = 
    ''-A ''@chain@'' -s '' @ ipv4_cidr_toString sip @ '' '' @
                  ''-d '' @ ipv4_cidr_toString dip @ '' '' @
                  ''-p '' @ protocol_toString p @ '' '' @
                  (if (iface_toString ''in:'' iif)@(iface_toString ''out:'' oif)@
                      (ports_toString ''srcports:'' sps)@(ports_toString ''dstports:'' dps) \<noteq> ''''
                   then ''TODO: more fields to dump'' else '''') @
                  '' -j '' @ simple_action_toString a"


end
