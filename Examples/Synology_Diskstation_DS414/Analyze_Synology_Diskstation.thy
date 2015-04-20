theory Analyze_Synology_Diskstation
imports iptables_Ln_tuned_parsed
 "../Code_Interface"
 "../../Semantics_Ternary/Optimizing"
begin


section{*Example: Synology Diskstation*}

text{*we removed the established,related rule*}
  definition "example_ruleset == firewall_chains(''INPUT'' \<mapsto> 
    remove1 (Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (Match (Extra (''state RELATED,ESTABLISHED'')))))) (action.Accept)) (the (firewall_chains ''INPUT'')))"

abbreviation MatchAndInfix :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" (infixr "MATCHAND" 65) where "MatchAndInfix m1 m2 \<equiv> MatchAnd m1 m2" (*(infixr "_ MATCHAND _" 65) *)

  value(code) "unfold_ruleset_INUPUT example_ruleset"

  lemma "good_ruleset (unfold_ruleset_INUPUT example_ruleset)" by eval
  lemma "simple_ruleset (unfold_ruleset_INUPUT example_ruleset)" by eval


  text{*packets from the local lan are allowed (in doubt)*}
  value(code) "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80\<rparr>
        (unfold_ruleset_INUPUT example_ruleset)
        Undecided = Decision FinalAllow"
  text{*However, they might also be rate-limited, ... (we don't know about icmp)*}
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80\<rparr>
        (unfold_ruleset_INUPUT example_ruleset)
        Undecided = Decision FinalDeny" by eval
  
  text{*But we can guarantee that packets from the outside are blocked!*}
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (8,8,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80\<rparr> 
        (unfold_ruleset_INUPUT example_ruleset)
        Undecided = Decision FinalDeny" by eval



text{*in doubt allow closure*}
lemma upper: "upper_closure (unfold_ruleset_INUPUT example_ruleset) =
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop, Rule MatchAny action.Accept]" by eval

text{*in doubt deny closure*}
lemma lower: "lower_closure (unfold_ruleset_INUPUT example_ruleset) =
 [Rule MatchAny action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule MatchAny action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule MatchAny action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop, Rule MatchAny action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop, Rule MatchAny action.Accept]" by eval



text{*upper closure*}
lemma "rmshadow (common_matcher, in_doubt_allow) (upper_closure (unfold_ruleset_INUPUT example_ruleset)) UNIV = 
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop]"
(*<*)apply(subst upper)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
apply(intro conjI impI)
apply(rule_tac x="\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (8,8,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80\<rparr> " in exI)
apply(simp add: ipv4addr_of_dotdecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)
apply(thin_tac "\<exists>p. x p" for x)
apply(rule_tac x="\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80\<rparr> " in exI)
apply(simp add: ipv4addr_of_dotdecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)
done(*>*)


text{*lower closure*}
lemma "rmshadow (common_matcher, in_doubt_deny) (lower_closure (unfold_ruleset_INUPUT example_ruleset)) UNIV =  
  [Rule MatchAny action.Drop]"
apply(subst lower)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
done


value "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INUPUT example_ruleset)))"
value "map simple_rule_toString (to_simple_firewall (lower_closure (unfold_ruleset_INUPUT example_ruleset)))"


value "length (unfold_ruleset_INUPUT example_ruleset)"
text{*Wow, normalization has exponential(?) blowup here.*}
value "length (normalize_rules_dnf (unfold_ruleset_INUPUT example_ruleset))"



subsection{*With parsed ports*}

(*../../importer/main.py --import "../Code_Interface" --parse_ports iptables_Ln_tuned iptables_Ln_tuned_parse_ports.thy*)
value "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INUPUT [''DOS_PROTECT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (action.Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (action.Drop)],
''INPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (Call (''DOS_PROTECT'')),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (Call (''DOS_PROTECT'')),
(*Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (Match (Extra (''state RELATED,ESTABLISHED'')))))) (action.Accept),*)
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (MatchAnd (Match (Dst_Ports ([(22,22)]))) (MatchAny))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto TCP))) (MatchAnd (Match (Dst_Ports ([(21,21),(873,873),(5005,5005),(5006,5006),(80,80),(548,548),(111,111),(2049,2049),(892,892)]))) (MatchAny))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (Proto UDP))) (MatchAnd (Match (Dst_Ports ([(123,123),(111,111),(2049,2049),(892,892),(5353,5353)]))) (MatchAny))))) (action.Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((192,168,0,0)) (16)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (action.Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (action.Drop),
Rule (MatchAny) (action.Accept)],
''FORWARD'' \<mapsto> [Rule (MatchAny) (action.Accept)],
''OUTPUT'' \<mapsto> [Rule (MatchAny) (action.Accept)]])))"

end
