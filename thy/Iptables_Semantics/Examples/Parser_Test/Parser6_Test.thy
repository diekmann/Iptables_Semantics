theory Parser6_Test
imports "../../Primitive_Matchers/Parser6"
begin


text\<open>
Argument 1: the name of the prefix for all constants which will be defined.
Argument 2: The path to the firewall (ip6tables-save). A path is represented as list.
\<close>
parse_ip6tables_save parser6_test_firewall = "data" "ip6tables-save"


term parser6_test_firewall
thm parser6_test_firewall_def
thm parser6_test_firewall_FORWARD_default_policy_def

value[code] "parser6_test_firewall"

lemma "parser6_test_firewall =
[(''FORWARD'',
   [Rule (MatchAnd (Match (Src
            (IpAddrNetmask (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xdb8 0 0 0x8d3 0 0 1)) 128)))
         (MatchAnd (Match (Dst
            (IpAddrNetmask (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xdb8 0 0 0x8d3 0 0 0)) 128)))
         (MatchAnd (Match (IIface (Iface ''eth0'')))
                   (Match (OIface (Iface ''foobar''))))))
     (Call ''gh32_-2qns''),
    Rule (MatchAnd (Match (Extra ''-d ::ffff:127.0.0.1/128'') (*We do not support this IPv6 notation!*))
         (MatchAnd (Match (IIface (Iface ''eth0'')))
                   (Match (OIface (Iface ''foobar'')))))
     (Call ''gh32_-2qns''),
    Rule (MatchAnd (Match (Src (IpAddrNetmask 1 128)))
         (MatchAnd (Match (IIface (Iface ''lo'')))
                   (Match (OIface (Iface ''lo'')))))
     action.Accept,
    Rule (Match (Extra (''--log-prefix '' @ [Char Nibble2 Nibble2] @
                        ''~%&/()=?'' @ [Char Nibble2 Nibble2] @ 
                        '' --log-level 6'')))
     Log,
    Rule (Match (Src (IpAddrNetmask 0 128))) action.Drop]),
  (''INPUT'', []), (''OUTPUT'', []),
  (''gh32_-2qns'',
   [Rule (Match (Src
      (IpAddrNetmask (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xdb8 0x85a3 0x8d3 0x1319 0x8a2e 0x370 0x7344)) 128)))
     Reject,
    Rule MatchAny Empty,
    Rule MatchAny action.Accept])]"
by eval

(*Broken: (IpAddr 0xFFFF0127))  (Match (Extra ''.0.0.1/128'') ! An address must have a word boundary!*)

lemma "sanity_check_simple_firewall
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser6_test_firewall_FORWARD_default_policy
                      (map_of parser6_test_firewall)))))))" by eval

lemma "map simple_rule_ipv6_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser6_test_firewall_FORWARD_default_policy
                      (map_of parser6_test_firewall))))))) =
[''ACCEPT     all  --  2001:db8::8d3:0:0:1/128            2001:db8:0:0:8d3::/128 in: eth0 out: foobar  '',
 ''ACCEPT     all  --  ::/0            ::/0 in: eth0 out: foobar  '',
 ''ACCEPT     all  --  ::1/128            ::/0 in: lo out: lo  '',
 ''DROP     all  --  ::/128            ::/0    '',
 ''DROP     all  --  ::/0            ::/0    '']" by eval 
(*33.224s*)

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
