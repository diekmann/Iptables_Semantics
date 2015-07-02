theory Parser_Test
imports "../Parser"
begin


text{*
Argument 1: the name of the prefix for all constants which will be defined.
Argument 2: The path to the firewall (iptables-save). A path is represented as list.
*}
local_setup \<open>
  local_setup_parse_iptables_save @{binding parser_test_firewall} ["data" ,"iptables-save"]
 \<close>

text{*The command @{text parse_iptables_save} would provide nicer syntax (but does not support paths at the moment)*}

term parser_test_firewall
thm parser_test_firewall_def
thm parser_test_firewall_FORWARD_default_policy_def

lemma "parser_test_firewall \<equiv>
[(''DOS~Pro-t_ect'',
  [Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst_Ports [(0x16, 0x16)]))) action.Accept,
   Rule (MatchAnd (Match (Prot (Proto TCP))) (MatchAnd (Match (Extra ''-m state --state NEW''))
        (MatchAnd (Match (Dst_Ports [(1, 0xFFFF)])) (Match (Extra ''--tcp-flags FIN,SYN,RST,ACK SYN'')))))
        action.Accept,
   Rule (Match (Prot (Proto UDP))) Return, Rule (Match (Prot (Proto ICMP))) action.Accept]),
(''FORWARD'',
  [Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) action.Drop, Rule (MatchNot (Match (IIface (Iface ''eth+'')))) action.Drop,
   Rule (MatchAnd (Match (Src (Ip4AddrNetmask (100, 0, 0, 0) 24))) (Match (Prot (Proto TCP)))) (Call ''DOS~Pro-t_ect''),
   Rule (MatchNot (Match (Src (Ip4AddrNetmask (131, 159, 0, 0) 16)))) action.Drop,
   Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst_Ports [(0x50, 0x50), (0x1BB, 0x1BB)]))) Return,
   Rule (MatchAnd (Match (Dst (Ip4AddrNetmask (127, 0, 0, 1) 32))) (MatchAnd (Match (OIface (Iface ''eth1.152'')))
        (MatchAnd (Match (Prot (Proto UDP))) (Match (Dst_Ports [(0x11D9, 0x11D9), (0x1388, 0xFFFF)])))))
        action.Accept,
   Rule (MatchAnd (Match (IIface (Iface ''eth0''))) (MatchAnd (Match (Prot (Proto TCP)))
        (Match (Dst_Ports [(0x15, 0x15), (0x369, 0x36A), (0x138D, 0x138D), (0x138E, 0x138E), (0x50, 0x50),
                           (0x224, 0x224), (0x6F, 0x6F), (0x37C, 0x37C), (0x801, 0x801)]))))
        action.Drop,
   Rule MatchAny (Goto ''Terminal'')]),
(''INPUT'', []),
(''OUTPUT'', []),
(''Terminal'',
  [Rule (MatchAnd (Match (Dst (Ip4AddrNetmask (127, 0, 0, 1) 32))) (MatchAnd (Match (Prot (Proto UDP)))
        (Match (Src_Ports [(0x35, 0x35)]))))
        action.Drop,
   Rule (Match (Dst (Ip4AddrNetmask (127, 42, 0, 1) 32))) Reject, Rule MatchAny Reject])]" by eval


value[code] "map (\<lambda>(c,rs). (c, map (common_primitive_rule_toString) rs)) parser_test_firewall"


value[code] "(upper_closure (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                  (map_of_string (Semantics_Goto.rewrite_Goto parser_test_firewall))))"

text{*@{const abstract_for_simple_firewall} requires @{const normalized_nnf_match} primitives, 
      therefore @{const upper_closure} is called first. Afterwards, the match expressions can 
      @{const has_unknowns}, therefore, @{const upper_closure} is called again.*}
value[code] "(optimize_matches abstract_for_simple_firewall
                  (upper_closure (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                    (map_of_string (Semantics_Goto.rewrite_Goto parser_test_firewall)))))"

value[code] "map simple_rule_toString (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                    (map_of_string (Semantics_Goto.rewrite_Goto parser_test_firewall)))))))" 


hide_const parser_test_firewall
           parser_test_firewall_INPUT_default_policy
           parser_test_firewall_FORWARD_default_policy
           parser_test_firewall_OUTPUT_default_policy
hide_fact parser_test_firewall_def
           parser_test_firewall_INPUT_default_policy_def
           parser_test_firewall_FORWARD_default_policy_def
           parser_test_firewall_OUTPUT_default_policy_def



end
