theory Parser_Test
imports "../../Primitive_Matchers/Parser"
  "../../Simple_Firewall/SimpleFw_toString"
begin


text{*
Argument 1: the name of the prefix for all constants which will be defined.
Argument 2: The path to the firewall (iptables-save). A path is represented as list.
*}
local_setup \<open>
  local_setup_parse_iptables_save "filter" @{binding parser_test_firewall} ["data" ,"iptables-save"]
 \<close>

text{*The command @{text parse_iptables_save} would provide nicer syntax (but does not support paths at the moment)*}

term parser_test_firewall
thm parser_test_firewall_def
thm parser_test_firewall_FORWARD_default_policy_def

value[code] "parser_test_firewall"
lemma "parser_test_firewall \<equiv>
[(''DOS~Pro-t_ect'',
   [Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst_Ports [(0x16, 0x16)]))) action.Accept,
    Rule (MatchAnd (Match (Prot (Proto TCP)))
           (MatchAnd (Match (CT_State {CT_New}))
             (MatchAnd (Match (Dst_Ports [(1, 0xFFFF)]))
               (Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN}))))))
     action.Accept,
    Rule (Match (Prot (Proto UDP))) Return,
    Rule (MatchAnd (Match (Prot (Proto ICMP))) (Match (Extra ''-m icmp --icmp-type 3/4'')))
     action.Accept,
    Rule (MatchAnd (Match (Prot (Proto ICMP)))
           (Match
             (Extra
               [CHR ''-'', CHR ''m'', CHR '' '', CHR ''c'', CHR ''o'', CHR ''m'', CHR ''m'',
                CHR ''e'', CHR ''n'', CHR ''t'', CHR '' '', CHR ''-'', CHR ''-'', CHR ''c'',
                CHR ''o'', CHR ''m'', CHR ''m'', CHR ''e'', CHR ''n'', CHR ''t'', CHR '' '',
                Char Nibble2 Nibble2, CHR ''!'', Char Nibble2 Nibble2])))
     action.Accept,
    Rule (MatchAnd (Match (Prot (Proto ICMP)))
           (Match
             (Extra
               [CHR ''-'', CHR ''m'', CHR '' '', CHR ''c'', CHR ''o'', CHR ''m'', CHR ''m'',
                CHR ''e'', CHR ''n'', CHR ''t'', CHR '' '', CHR ''-'', CHR ''-'', CHR ''c'',
                CHR ''o'', CHR ''m'', CHR ''m'', CHR ''e'', CHR ''n'', CHR ''t'', CHR '' '',
                Char Nibble2 Nibble2, CHR ''h'', CHR ''a'', CHR ''s'', CHR '' '', CHR ''s'',
                CHR ''p'', CHR ''a'', CHR ''c'', CHR ''e'', Char Nibble2 Nibble2])))
     action.Accept,
    Rule (Match (Prot (Proto ICMP))) action.Accept,
    Rule (MatchNot (Match (Prot (Proto ICMP)))) Empty,
    Rule (MatchAnd (MatchNot (Match (Prot (Proto TCP))))
           (MatchNot (Match (Src (Ip4AddrNetmask (131, 159, 0, 0) 16)))))
     Empty,
    Rule (MatchAnd (Match (IIface (Iface ''vocb'')))
           (MatchAnd (Match (Prot (Proto UDP)))
             (MatchAnd (Match (Src_Ports [(0x43, 0x44)])) (Match (Dst_Ports [(0x43, 0x44)])))))
     action.Accept,
    Rule (MatchAnd (Match (IIface (Iface ''vocb'')))
           (MatchAnd (Match (Prot (Proto UDP)))
             (MatchAnd (MatchNot (Match (Src_Ports [(0x43, 0x44)])))
               (MatchNot (Match (Dst_Ports [(0x43, 0x44)]))))))
     action.Accept]),
  (''FORWARD'',
   [Rule (Match
           (Extra
             [CHR ''-'', CHR ''-'', CHR ''l'', CHR ''o'', CHR ''g'', CHR ''-'', CHR ''p'',
              CHR ''r'', CHR ''e'', CHR ''f'', CHR ''i'', CHR ''x'', CHR '' '',
              Char Nibble2 Nibble2, CHR ''!'', CHR ''#'', CHR ''*'', CHR ''~'', CHR ''%'',
              CHR ''&'', CHR ''/'', CHR ''('', CHR '')'', CHR ''='', CHR ''?'',
              Char Nibble2 Nibble2, CHR '' '', CHR ''-'', CHR ''-'', CHR ''l'', CHR ''o'',
              CHR ''g'', CHR ''-'', CHR ''l'', CHR ''e'', CHR ''v'', CHR ''e'', CHR ''l'',
              CHR '' '', CHR ''6'']))
     Log,
    Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) action.Drop,
    Rule (MatchAnd (Match (IIface (Iface ''wlan0'')))
           (MatchAnd (Match (Prot (Proto TCP)))
             (MatchAnd
               (MatchNot
                 (Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN}))))
               (Match (CT_State {CT_New})))))
     action.Drop,
    Rule (MatchAnd (Match (Prot (Proto TCP)))
           (MatchAnd (Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})))
             (Match (Dst_Ports [(0x50, 0x50), (0x1BB, 0x1BB)]))))
     action.Accept,
    Rule (MatchAnd (Match (Prot (Proto TCP)))
           (MatchAnd (Match (CT_State {CT_New}))
             (MatchAnd (Match (Dst_Ports [(1, 0xFFFF)]))
               (Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN}))))))
     action.Accept,
    Rule (Match (Extra ''--ctstate NEW,INVALID'')) action.Drop,
    Rule (MatchAnd (Match (IIface (Iface ''wlan0'')))
           (MatchAnd (Match (Prot (Proto ICMP)))
             (Match (CT_State {CT_Established, CT_New, CT_Related, CT_Untracked}))))
     action.Accept,
    Rule (Match (CT_State {CT_New, CT_Untracked})) action.Accept,
    Rule (Match (CT_State {CT_Established, CT_Related})) action.Accept,
    Rule (MatchNot (Match (IIface (Iface ''eth+'')))) action.Drop,
    Rule (MatchAnd (Match (Src (Ip4AddrNetmask (100, 0, 0, 0) 24))) (Match (Prot (Proto TCP))))
     (Call ''DOS~Pro-t_ect''),
    Rule (MatchNot (Match (Src (Ip4AddrNetmask (131, 159, 0, 0) 16)))) action.Drop,
    Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Src_Ports [(0x50, 0x50), (0x1BB, 0x1BB)])))
     action.Drop,
    Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst_Ports [(0x50, 0x50), (0x1BB, 0x1BB)])))
     action.Drop,
    Rule (MatchAnd (Match (Dst (Ip4AddrNetmask (127, 0, 0, 1) 32)))
           (MatchAnd (Match (OIface (Iface ''eth1.152'')))
             (MatchAnd (Match (Prot (Proto UDP)))
               (Match (Dst_Ports [(0x11D9, 0x11D9), (0x1388, 0xFFFF)])))))
     action.Accept,
    Rule (MatchAnd (Match (IIface (Iface ''eth0'')))
           (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst_Ports [(0x16, 0x16)]))))
     action.Drop,
    Rule (MatchAnd (Match (IIface (Iface ''eth0'')))
           (MatchAnd (Match (Prot (Proto TCP)))
             (Match
               (Dst_Ports
                 [(0x15, 0x15), (0x369, 0x36A), (0x138D, 0x138D), (0x138E, 0x138E), (0x50, 0x50),
                  (0x224, 0x224), (0x6F, 0x6F), (0x37C, 0x37C), (0x801, 0x801)]))))
     action.Drop,
    Rule (Match (Src (Ip4Addr (192, 168, 0, 1)))) (Call ''LOGDROP''),
    Rule (Match (Src (Ip4AddrRange (127, 0, 0, 1) (127, 0, 10, 0)))) Return,
    Rule (MatchNot (Match (Dst (Ip4AddrRange (127, 0, 0, 1) (127, 0, 10, 0))))) Return,
    Rule MatchAny (Goto ''Terminal''), 
    Rule MatchAny (Call ''IPSEC_42'')]),
  (''INPUT'', []),
  (''IPSEC_42'',
 [Rule (MatchAnd (Match (Prot (Proto (OtherProtocol 50)))) (Match (CT_State {CT_New}))) action.Accept,
  Rule (MatchAnd (Match (Prot (Proto (OtherProtocol 47)))) (Match (CT_State {CT_New}))) action.Accept]),
  (''LOGDROP'', [Rule MatchAny Empty, Rule MatchAny action.Drop]),
  (''OUTPUT'', []),
  (''Terminal'',
   [Rule (MatchAnd (Match (Dst (Ip4AddrNetmask (127, 0, 0, 1) 32)))
           (MatchAnd (Match (Prot (Proto UDP))) (Match (Src_Ports [(0x35, 0x35)]))))
     action.Drop,
    Rule (Match (Dst (Ip4AddrNetmask (127, 42, 0, 1) 32))) Reject, Rule MatchAny Reject])]" by eval


(*There is some ~~-m tcp~~  remaining because we cannot parse "-m tcp ! --tcp-flags"*)
value[code] "map (\<lambda>(c,rs). (c, map (common_primitive_rule_toString) rs)) parser_test_firewall"


value[code] "let fw = (upper_closure (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                  (map_of_string (Semantics_Goto.rewrite_Goto parser_test_firewall))))
             in map common_primitive_rule_toString fw"

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


value[code] "(optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD parser_test_firewall_FORWARD_default_policy
                     (map_of_string (Semantics_Goto.rewrite_Goto parser_test_firewall))))))"


hide_const parser_test_firewall
           parser_test_firewall_INPUT_default_policy
           parser_test_firewall_FORWARD_default_policy
           parser_test_firewall_OUTPUT_default_policy
hide_fact parser_test_firewall_def
           parser_test_firewall_INPUT_default_policy_def
           parser_test_firewall_FORWARD_default_policy_def
           parser_test_firewall_OUTPUT_default_policy_def



end
