theory Code_Interface
imports 
  Common_Primitive_toString
  "../Call_Return_Unfolding"
  Transform
  No_Spoof
  "../Simple_Firewall/SimpleFw_Compliance"
  "../Simple_Firewall/SimpleFw_toString"
  "../Simple_Firewall/IPPartitioning"
  "../Semantics_Ternary/Optimizing" (*do we use this?*)
  "../Semantics_Goto"
  "../Simple_Firewall/SimpleFw_toString" (*hmm, here?*)
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Char"
begin

(*Note: common_primitive_match_expr_toString can be really slow*)

section{*Code Interface*}


text{*The parser returns the @{typ "common_primitive ruleset"} not as a map but as an association list.
      This function converts it*}
definition map_of_string :: "(string \<times> common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> common_primitive rule list" where
  "map_of_string rs = map_of rs"


definition check_simple_ruleset :: "common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "check_simple_ruleset rs \<equiv> if simple_ruleset rs then rs else undefined"

text{*repeat the application at most n times (param 1) until it stabilize*}
fun repeat_stabilize :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "repeat_stabilize 0 _ v = v" |
  "repeat_stabilize (Suc n) f v = (let v_new = f v in if v = v_new then v else repeat_stabilize n f v_new)"

lemma "repeat_stabilize n f v = (f^^n) v"
  proof(induction n arbitrary: v)
  case (Suc n)
    have "f v = v \<Longrightarrow> (f^^n) v = v" by(induction n) simp_all
    with Suc show ?case by(simp add: Let_def funpow_swap1)
  qed(simp)

(*TODO replace constant number of process_call with number of chain decls *)

definition unfold_ruleset_CHAIN :: "string \<Rightarrow> action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_CHAIN chain_name default_action rs = check_simple_ruleset
  (repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
    (optimize_matches optimize_primitive_univ
      (rw_Reject (rm_LogEmpty (repeat_stabilize 10000 (process_call rs)
        [Rule MatchAny (Call chain_name), Rule MatchAny default_action]
  )))))"


definition unfold_ruleset_FORWARD :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_FORWARD = unfold_ruleset_CHAIN ''FORWARD''"

definition unfold_ruleset_INPUT :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_INPUT = unfold_ruleset_CHAIN ''INPUT''"

definition unfold_ruleset_OUTPUT :: "action \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive rule list" where
"unfold_ruleset_OUTPUT \<equiv> unfold_ruleset_CHAIN ''OUTPUT''"


lemma "let fw = [''FORWARD'' \<mapsto> []] in
  unfold_ruleset_FORWARD action.Drop fw
  = [Rule MatchAny action.Drop]" by eval


(*
definition port_to_nat :: "16 word \<Rightarrow> nat" where
  "port_to_nat p = unat p"
*)

(* only used for ML code to convert types *)
definition nat_to_16word :: "nat \<Rightarrow> 16 word" where
  "nat_to_16word i \<equiv> of_nat i"

definition integer_to_16word :: "integer \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> nat_to_16word (nat_of_integer i)"


context
begin
  (*cool example*)
  lemma "let fw = [''FORWARD'' \<mapsto> [Rule (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (Call ''foo'')],
                         ''foo'' \<mapsto> [Rule (Match (Src (Ip4AddrNetmask (10,128,0,0) 9))) action.Return,
                                     Rule (Match (Prot (Proto TCP))) action.Accept]
                         ] in
    let simplfw = to_simple_firewall
      (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw)))))
    in map simple_rule_toString simplfw =
    [''ACCEPT     tcp  --  10.0.0.0/9            0.0.0.0/0    '', ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval
  
  (*cooler example*)
  private definition "cool_example \<equiv> (let fw = [''FORWARD'' \<mapsto> [Rule (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (Call ''foo'')],
                         ''foo'' \<mapsto> [Rule (MatchNot (Match (Src (Ip4AddrNetmask (10,0,0,0) 9)))) action.Drop,
                                     Rule (Match (Prot (Proto TCP))) action.Accept]
                         ] in
    to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw))))))"
  lemma " map simple_rule_toString cool_example =
    [''DROP     all  --  10.128.0.0/9            0.0.0.0/0    '', ''ACCEPT     tcp  --  10.0.0.0/8            0.0.0.0/0    '',
    ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']"
  by eval
  
  value[code] "map pretty_wordinterval (getParts cool_example)"
  
  value[code] "map pretty_wordinterval (build_ip_partition parts_connection_ssh cool_example)"
  
  (*it is not minimal if we allow to further compress the node definitions?
  the receiver nodes could be combined to UNIV
  But minimal for a symmetric matrix*)
  value[code] "build_ip_partition_pretty parts_connection_ssh cool_example"
end


context
begin
  (*prob look at dst also*)
  private definition "cool_example2 \<equiv> (let fw =
    [''FORWARD'' \<mapsto> [Rule (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (Call ''foo'')],
     ''foo'' \<mapsto> [Rule (MatchNot (Match (Src (Ip4AddrNetmask (10,0,0,0) 9)))) action.Drop,
                 Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst (Ip4AddrNetmask (10,0,0,42) 32)))) action.Accept]
                         ] in
    to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw))))))"
  value[code] "map simple_rule_toString cool_example2"
  
  value[code] "map pretty_wordinterval (getParts cool_example2)"
  
  value[code] "map pretty_wordinterval (build_ip_partition parts_connection_ssh cool_example2)"
  
  value[code] "build_ip_partition_pretty parts_connection_ssh cool_example2"
  end


definition prefix_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "prefix_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
 lemma "prefix_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval




end
