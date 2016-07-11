theory Parser6_Test
imports "../../Primitive_Matchers/Parser6"
begin


text\<open>
Argument 1: the name of the prefix for all constants which will be defined.
Argument 2: The path to the firewall (ip6tables-save). A path is represented as list.
\<close>
parse_ip6tables_save parser_test_firewall =
   ".." ".." ".." ".." ".." "net-network" "configs_synology_diskstation_ds414" "ip6tables-save_jul_2016"


term parser_test_firewall
thm parser_test_firewall_def
thm parser_test_firewall_FORWARD_default_policy_def

value[code] "parser_test_firewall"

lemma "sanity_check_simple_firewall
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                      (map_of parser_test_firewall))))))) = False" by eval

value[code] "map simple_rule_ipv6_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                      (map_of parser_test_firewall)))))))" 
(*33.224s*)

text\<open>here is a minimal example\<close>
value[code] " (unfold_ruleset_FORWARD action.Accept
                      (map_of_string_ipv4
                              [(''FORWARD'', [Rule MatchAny (Call ''CHAIN'')]),
                               (''CHAIN'',
                                [Rule (MatchAnd (Match (Prot (Proto TCP)))
                                        (Match (Src_Ports [(22, 22)])))
                                  Return,
                                 Rule (MatchAnd (Match (Prot (Proto UDP)))
                                        (Match (Dst_Ports [(80,80)])))
                                  Return,
                                 Rule MatchAny action.Drop])
                              ]))"


value[code] "map simple_rule_ipv4_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                      (map_of_string_ipv4 [(''FORWARD'', [Rule MatchAny (Call ''CHAIN'')]),
                               (''CHAIN'',
                                [Rule (MatchAnd (Match (Prot (Proto TCP)))
                                        (Match (Src_Ports [(22, 22)])))
                                  Return,
                                 Rule (MatchAnd (Match (Prot (Proto UDP)))
                                        (Match (Dst_Ports [(80,80)])))
                                  Return,
                                 Rule MatchAny action.Drop])
                              ])))))))" 

lemma "sanity_check_simple_firewall
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                      (map_of_string_ipv4 [(''FORWARD'', [Rule MatchAny (Call ''CHAIN'')]),
                               (''CHAIN'',
                                [Rule (MatchAnd (Match (Prot (Proto TCP)))
                                        (Match (Src_Ports [(22, 22)])))
                                  Return,
                                 Rule (MatchAnd (Match (Prot (Proto UDP)))
                                        (Match (Dst_Ports [(80,80)])))
                                  Return,
                                 Rule MatchAny action.Drop])
                              ]))))))) = False" by eval 

(*

parse_ip6tables_save parser_test_firewall2 =
   ".." ".." ".." ".." ".." "net-network" "configs_chair_for_Network_Architectures_and_Services" 
   "ip6tables-save-2016-06-27_16-29-01"
(*loading file /home/diekmann/git/Iptables_Semantics/thy/Iptables_Semantics/Examples/Parser_Test/../../../../../net-network/configs_chair_for_Network_Architectures_and_Services/ip6tables-save-2016-06-27_16-29-01 
Loaded 6299 lines of the filter table 
Parsed 96 chain declarations 
Parsed 6203 rules 
unfolding (this may take a while) ... 
Simplified term (909.346 seconds) 
checked sanity with sanity_wf_ruleset (951.053 seconds) 
Defining constant `parser_test_firewall2_def' 
Defining constant `parser_test_firewall2_INPUT_default_policy_def' 
Defining constant `parser_test_firewall2_FORWARD_default_policy_def' 
Defining constant `parser_test_firewall2_OUTPUT_default_policy_def'*)

value[code] "map simple_rule_ipv6_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall2_FORWARD_default_policy
                      (map_of parser_test_firewall2)))))))"

*)
end
