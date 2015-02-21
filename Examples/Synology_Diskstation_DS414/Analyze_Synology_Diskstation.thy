theory Analyze_Synology_Diskstation
imports iptables_Ln_tuned_parsed"../../Output_Format/IPSpace_Format_Ln" "../../Call_Return_Unfolding" "../../Optimizing"
  "../../Packet_Set"
begin


section{*Example: Synology Diskstation*}

text{*we removed the established,related rule*}

  definition "example_ruleset ==  [''DOS_PROTECT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (Drop)],
''INPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Call (''DOS_PROTECT'')),
(* Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (Match (Extra (''state RELATED,ESTABLISHED'')))))) (Accept), *)
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp dpt:22'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''multiport dports 21,873,5005,5006,80,548,111,2049,892'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtUDP))) (Match (Extra (''multiport dports 123,111,2049,892,5353'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((192,168,0,0)) (16)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Drop),
Rule (MatchAny) (Accept)],
''FORWARD'' \<mapsto> [Rule (MatchAny) (Accept)],
''OUTPUT'' \<mapsto> [Rule (MatchAny) (Accept)]]"

abbreviation MatchAndInfix :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" (infixr "MATCHAND" 65) where "MatchAndInfix m1 m2 \<equiv> MatchAnd m1 m2" (*(infixr "_ MATCHAND _" 65) *)

  definition "example_ruleset_simplified = ((optimize_matches opt_MatchAny_match_expr)^^10) 
    (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call example_ruleset)^^2) [Rule MatchAny (Call ''INPUT'')]))))"
  value(code) "example_ruleset_simplified"

  lemma "good_ruleset example_ruleset_simplified" by eval
  lemma "simple_ruleset example_ruleset_simplified" by eval

  text{*packets from the local lan are allowed (in doubt)*}
  value "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=ipv4addr_of_dotteddecimal (192,168,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        example_ruleset_simplified
        Undecided = Decision FinalAllow"
  lemma "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=ipv4addr_of_dotteddecimal (192,168,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        example_ruleset_simplified
        Undecided = Decision FinalAllow" by eval
  text{*However, they might also be rate-limited, ... (we don't know about icmp)*}
  lemma "approximating_bigstep_fun (simple_matcher, in_doubt_deny) \<lparr>src_ip=ipv4addr_of_dotteddecimal (192,168,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        example_ruleset_simplified
        Undecided = Decision FinalDeny" by eval
  
  text{*But we can guarantee that packets from the outside are blocked!*}
  lemma "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=ipv4addr_of_dotteddecimal (8,8,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        example_ruleset_simplified
        Undecided = Decision FinalDeny" by eval


lemma "wf_unknown_match_tac \<alpha> \<Longrightarrow> approximating_bigstep_fun (simple_matcher, \<alpha>) p example_ruleset_simplified s = approximating_bigstep_fun (simple_matcher, \<alpha>) p (((process_call example_ruleset)^^2) [Rule MatchAny (Call ''INPUT'')]) s"
apply(simp add: example_ruleset_simplified_def)
apply(simp add: optimize_matches_opt_MatchAny_match_expr)
apply(simp add: opt_simple_matcher_correct)
apply(simp add: rw_Reject_fun_semantics)
apply(simp add: rm_LogEmpty_fun_semantics)
done

text{*in doubt allow closure*}
value "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr example_ruleset_simplified))"

text{*in doubt deny closure*}
value "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr example_ruleset_simplified))"


(*<*)
lemma tmp: "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr example_ruleset_simplified)) = 
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) Accept, Rule MatchAny Drop, Rule MatchAny Accept]" by eval
lemma tmp': "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr example_ruleset_simplified)) = 
  [Rule MatchAny Drop, Rule (Match (Prot ProtTCP)) Drop, Rule (Match (Prot ProtTCP)) Drop, Rule (Match (Prot ProtTCP)) Drop, Rule (Match (Prot ProtTCP)) Drop, 
   Rule (Match (Prot ProtUDP)) Drop, Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) Accept, Rule MatchAny Drop,
   Rule MatchAny Accept]" by eval

lemma hlp1: "((-1062666241)::ipv4addr) = 3232301055" by simp
(*>*)

text{*upper closure*}
lemma "rmshadow (simple_matcher, in_doubt_allow) (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr example_ruleset_simplified))) UNIV = 
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) Accept, Rule MatchAny Drop]"
apply(subst tmp)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
apply(intro conjI impI)
apply(rule_tac x="\<lparr>src_ip=ipv4addr_of_dotteddecimal (8,8,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>" in exI)
apply(simp add: ipv4addr_of_dotteddecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)

apply(thin_tac "\<exists>p. ?x p")
apply(rule_tac x="\<lparr>src_ip=ipv4addr_of_dotteddecimal (192,168,99,0), dst_ip=0, prot=protPacket.ProtTCP\<rparr>" in exI)
apply(simp add: ipv4addr_of_dotteddecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)
done


text{*lower closure*}
lemma "rmshadow (simple_matcher, in_doubt_deny) (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr example_ruleset_simplified))) UNIV = 
  [Rule MatchAny Drop]"
apply(subst tmp')
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
done
hide_fact tmp

value "format_Ln_rules_uncompressed [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) Accept, Rule MatchAny Drop]"
(*[Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) Accept, Rule MatchAny Drop]

Chain INPUT (policy ACCEPT)
target     prot opt source               destination
ACCEPT     all  --  192.168.0.0/16       0.0.0.0/0
DROP       all  --  0.0.0.0/0            0.0.0.0/0

Chain FORWARD (policy ACCEPT)
target     prot opt source               destination

Chain OUTPUT (policy ACCEPT)
target     prot opt source               destination


*)



text{*exact*}
(*first rule can be simplified away*)
value "format_Ln_rules_uncompressed example_ruleset_simplified"

value "length (example_ruleset_simplified)"
text{*Wow, normalization has exponential?? blowup!!*}
value "length (normalize_rules_dnf example_ruleset_simplified)"
value "length (format_Ln_rules_uncompressed example_ruleset_simplified)"

thm format_Ln_rules_uncompressed_correct

text{*upper closure*}
value "format_Ln_rules_uncompressed (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr example_ruleset_simplified)))"
lemma "collect_allow_impl_v2 (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr example_ruleset_simplified))) packet_set_UNIV = 
  PacketSet [[(Pos (Src (Ip4AddrNetmask (192, 168, 0, 0) 16)), Pos Accept)]]" by eval

text{*lower closure*}
value "format_Ln_rules_uncompressed (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr example_ruleset_simplified)))"
lemma "collect_allow_impl_v2 (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr example_ruleset_simplified))) packet_set_UNIV =
  packet_set_Empty" by eval


text{*packet set test*}
value(code) "collect_allow_impl_v2 (take 1 example_ruleset_simplified) packet_set_UNIV"


value(code) "collect_allow_impl_v2 (take 2 example_ruleset_simplified) packet_set_UNIV"


end
