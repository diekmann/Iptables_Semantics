theory Analyze_Ringofsaturn_com
imports
  "../../Call_Return_Unfolding"
  "../../Optimizing"
  "../../Output_Format/IPSpace_Format_Ln"
  "../../Packet_Set"
begin

section{*Example: ringofsaturn.com*}

(* Based on <http://networking.ringofsaturn.com/Unix/iptables.php> *)
(* Archived at <https://archive.today/3c309> *)

text{* We have directly executable approximating semantics: @{thm approximating_semantics_iff_fun}*}
  value(code) "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=0, dst_ip=0, prot=protPacket.ProtTCP\<rparr>
          (process_call [''FORWARD'' \<mapsto> [Rule (Match (Src (Ip4Addr(192,168,0,0) ))) Drop, Rule MatchAny Accept], ''foo'' \<mapsto> []] [Rule MatchAny (Call ''FORWARD'')])
         Undecided"

  definition "example_ruleset == [''FORWARD'' \<mapsto> [Rule (Match (Src ((Ip4AddrNetmask (192,168,0,0) 16)))) (Call ''foo''), Rule MatchAny Drop],
                         ''foo'' \<mapsto> [Rule MatchAny Log, Rule (Match (Extra ''foobar'')) Accept ]]"

  definition "example_ruleset_simplified = rm_LogEmpty (((process_call example_ruleset)^^2) [Rule MatchAny (Call ''FORWARD'')])"
  value "example_ruleset_simplified"

  value "good_ruleset example_ruleset_simplified"
  value "simple_ruleset example_ruleset_simplified"


  lemma "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=ipv4addr_of_dotdecimal (192,168,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        example_ruleset_simplified
        Undecided = Decision FinalAllow" by eval
  hide_const example_ruleset_simplified example_ruleset


subsection{*Example Ruleset 1*}

definition "example_firewall \<equiv> [''STATEFUL'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (Match (Extra ''state RELATED,ESTABLISHED''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (Match (Extra ''state NEW''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP'')] ,
''DUMP'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''LOG flags 0 level 4''))))) (Log),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''LOG flags 0 level 4''))))) (Log),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''reject-with tcp-reset''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Drop)] ,
''INPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''STATEFUL''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (127,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (169,254,0,0) 16))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (172,16,0,0) 12))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (224,0,0,0) 3))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (240,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (160,86,0,0) 16))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 3''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 11''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 0''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 8''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:111''))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:113 reject-with tcp-reset''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:4''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:20''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:21''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:20''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:21''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:22''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:22''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:80''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:80''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:443''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:443''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:520 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpts:137:139 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpts:137:139 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule MatchAny (Accept)] ,
''FORWARD'' \<mapsto> [Rule MatchAny (Accept)] ,
''OUTPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Accept),
Rule MatchAny (Accept)] ]"


definition "simple_example_firewall \<equiv> (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call example_firewall)^^3) [Rule MatchAny (Call ''INPUT'')])))))"

text{*It accepts everything in state RELATED,ESTABLISHED,NEW*}
value(code) "simple_example_firewall"
value "good_ruleset simple_example_firewall"
value "simple_ruleset simple_example_firewall"

lemma "approximating_bigstep_fun (simple_matcher, in_doubt_allow) p simple_example_firewall s = approximating_bigstep_fun (simple_matcher, in_doubt_allow) p (((process_call example_firewall)^^3) [Rule MatchAny (Call ''INPUT'')]) s"
apply(simp add: simple_example_firewall_def)
apply(simp add: optimize_matches_opt_MatchAny_match_expr)
apply(simp add: opt_simple_matcher_correct)
apply(simp add: rw_Reject_fun_semantics wf_in_doubt_allow)
apply(simp add: rm_LogEmpty_fun_semantics)
done

(*Hmm, this ruleset is the Allow-All ruleset!*)
value(code) "((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr simple_example_firewall)"

(*<*)
lemma tmp: "((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr simple_example_firewall) = [Rule MatchAny Accept, Rule MatchAny Accept, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule MatchAny Drop, Rule MatchAny Accept, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8))) Drop,
  Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8))) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) Drop,
  Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16))) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12))) Drop,
  Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3))) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8))) Drop,
  Rule (Match (Src (Ip4AddrNetmask (160, 86, 0, 0) 16))) Accept, Rule MatchAny Drop, Rule MatchAny Accept, Rule MatchAny Accept, Rule MatchAny Accept, Rule MatchAny Accept, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop,
  Rule (Match (Prot ipt_protocol.ProtTCP)) Accept, Rule (Match (Prot ipt_protocol.ProtTCP)) Accept, Rule (Match (Prot ipt_protocol.ProtTCP)) Accept, Rule (Match (Prot ipt_protocol.ProtUDP)) Accept, Rule (Match (Prot ipt_protocol.ProtUDP)) Accept,
  Rule (Match (Prot ipt_protocol.ProtTCP)) Accept, Rule (Match (Prot ipt_protocol.ProtUDP)) Accept, Rule (Match (Prot ipt_protocol.ProtTCP)) Accept, Rule (Match (Prot ipt_protocol.ProtUDP)) Accept, Rule (Match (Prot ipt_protocol.ProtTCP)) Accept,
  Rule (Match (Prot ipt_protocol.ProtUDP)) Accept, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule (MatchNot MatchAny) Drop, Rule MatchAny Drop, Rule MatchAny Accept]" by eval
(*>*)

lemma "rmshadow (simple_matcher, in_doubt_allow) (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr simple_example_firewall)) UNIV = 
      [Rule MatchAny Accept]"
apply(subst tmp)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
done




value(code) "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=0, dst_ip=0, prot=protPacket.ProtTCP\<rparr>
          simple_example_firewall
         Undecided"
value(code) "approximating_bigstep_fun (simple_matcher, in_doubt_allow) \<lparr>src_ip=ipv4addr_of_dotdecimal (192,168,3,5), dst_ip=0, prot=protPacket.ProtTCP\<rparr>
        simple_example_firewall
        Undecided"






text{*We removed the first matches on state*}
definition "example_firewall2 \<equiv> [''STATEFUL'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (Match (Extra ''state RELATED,ESTABLISHED''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (Match (Extra ''state NEW''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP'')] ,
''DUMP'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''LOG flags 0 level 4''))))) (Log),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''LOG flags 0 level 4''))))) (Log),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''reject-with tcp-reset''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Drop)] ,
''INPUT'' \<mapsto> [
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (10,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (127,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (169,254,0,0) 16))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (172,16,0,0) 12))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (224,0,0,0) 3))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (240,0,0,0) 8))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (160,86,0,0) 16))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 3''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 11''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 0''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Extra ''Prot icmp''))  (Match (Extra ''icmptype 8''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:111''))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:113 reject-with tcp-reset''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:4''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:20''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:21''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:20''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:21''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:22''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:22''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:80''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:80''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpt:443''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:443''))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpt:520 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP))  (Match (Extra ''tcp dpts:137:139 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtUDP))  (Match (Extra ''udp dpts:137:139 reject-with icmp-port-unreachable''))))) (Reject),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Call ''DUMP''),
Rule MatchAny (Accept)] ,
''FORWARD'' \<mapsto> [Rule MatchAny (Accept)] ,
''OUTPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Dst (Ip4AddrNetmask (0,0,0,0) 0))) (MatchAnd (Match (Prot ipt_protocol.ProtAll))  (MatchAny)))) (Accept),
Rule MatchAny (Accept)] ]"

definition "simple_example_firewall2 \<equiv> (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call example_firewall2)^^3) [Rule MatchAny (Call ''INPUT'')])))))"

lemma "wf_unknown_match_tac \<alpha> \<Longrightarrow> approximating_bigstep_fun (simple_matcher, \<alpha>) p simple_example_firewall2 s = approximating_bigstep_fun (simple_matcher, \<alpha>) p (((process_call example_firewall2)^^3) [Rule MatchAny (Call ''INPUT'')]) s"
apply(simp add: simple_example_firewall2_def)
apply(simp add: optimize_matches_opt_MatchAny_match_expr)
apply(simp add: opt_simple_matcher_correct)
apply(simp add: rw_Reject_fun_semantics)
apply(simp add: rm_LogEmpty_fun_semantics)
done

value(code) "simple_example_firewall2"
value(code) "zip (upto 0 (int (length simple_example_firewall2))) simple_example_firewall2"
value "good_ruleset simple_example_firewall2"
value "simple_ruleset simple_example_firewall2"

text{*in doubt allow closure*}
value(code) "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr simple_example_firewall2))"

text{*in doubt deny closure*}
value(code) "rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr simple_example_firewall2))"


value(code) "format_Ln_rules_uncompressed (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a upper_closure_matchexpr simple_example_firewall2)))"
value(code) "format_Ln_rules_uncompressed (rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^10) (optimize_matches_a lower_closure_matchexpr simple_example_firewall2)))"
value(code) "format_Ln_rules_uncompressed simple_example_firewall2"

text{*Allowed Packets*}
text{*the first 10 rules basically accept no packets*}
lemma "collect_allow_impl_v2 (take 10 simple_example_firewall2) packet_set_UNIV = packet_set_Empty" by eval


value(code) "allow_set_not_inter simple_example_firewall2"


value(code) "map packet_set_opt (allow_set_not_inter simple_example_firewall2)"



end
