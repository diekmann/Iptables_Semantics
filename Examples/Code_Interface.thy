theory Code_Interface
imports 
"../Call_Return_Unfolding"
"../Primitive_Matchers/Transform"
"../Simple_Firewall/SimpleFw_Compliance"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
begin


section{*Code Interface*}

definition unfold_ruleset_FORWARD :: "common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_FORWARD rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches optimize_primitive_univ (rw_Reject (rm_LogEmpty (((process_call rs)^^10) [Rule MatchAny (Call ''FORWARD'')]))))"

definition unfold_ruleset_INUPUT :: "common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_INUPUT rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches optimize_primitive_univ (rw_Reject (rm_LogEmpty (((process_call rs)^^10) [Rule MatchAny (Call ''INPUT'')]))))"

definition unfold_ruleset_OUTPUT :: "common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_OUTPUT rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches optimize_primitive_univ (rw_Reject (rm_LogEmpty (((process_call rs)^^10) [Rule MatchAny (Call ''OUTPUT'')]))))"


definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
"map_of_string rs = map_of rs"

definition upper_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "upper_closure rs == transform_optimize_dnf_strict (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a upper_closure_matchexpr rs)))"
definition lower_closure :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "lower_closure rs == transform_optimize_dnf_strict (transform_normalize_primitives (transform_optimize_dnf_strict (optimize_matches_a lower_closure_matchexpr rs)))"

(*
definition port_to_nat :: "16 word \<Rightarrow> nat" where
  "port_to_nat p = unat p"
*)



definition bitmask_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "bitmask_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "bitmask_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval


subsection{*toString functions*}
(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"
definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

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

definition port_toString :: "16 word \<Rightarrow> string" where
  "port_toString p \<equiv> string_of_nat (unat p)"

definition iface_toString :: "string \<Rightarrow> iface \<Rightarrow> string" where
  "iface_toString descr iface = (if iface = IfaceAny then '''' else
      (case iface of (Iface name) \<Rightarrow> descr@name))"
lemma "iface_toString ''src: '' (Iface ''+'') = ''''" by eval
lemma "iface_toString ''src: '' (Iface ''eth0'') = ''src: eth0''" by eval

fun ports_toString :: "string \<Rightarrow> (16 word \<times> 16 word) \<Rightarrow> string" where
  "ports_toString descr (s,e) = (if s = 0 \<and> e = max_word then '''' else descr@''(''@port_toString s@'',''@port_toString e@'')'')"
lemma "ports_toString ''src: '' (0,65535) = ''''" by eval
lemma "ports_toString ''src: '' (1024,2048) = ''src: (1024,2048)''" by eval


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
