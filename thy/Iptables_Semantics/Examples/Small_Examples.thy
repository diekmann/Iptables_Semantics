theory Small_Examples
imports "../Primitive_Matchers/Code_Interface"
begin

section\<open>Small Examples\<close>
context
begin
  lemma "let fw = [''FORWARD'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 8))) (Call ''foo'')],
                   ''foo'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,128,0,0)) 9))) action.Return,
                               Rule (Match (Prot (Proto TCP))) action.Accept]
                   ] in
    let simplfw = to_simple_firewall
      (upper_closure (optimize_matches abstract_for_simple_firewall
        (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw)))))
    in map simple_rule_ipv4_toString simplfw =
    [''ACCEPT     tcp  --  10.0.0.0/9            0.0.0.0/0    '',
     ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval
  
  private definition "cool_example \<equiv> (let fw = 
                [''FORWARD'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 8))) (Call ''foo'')],
                 ''foo'' \<mapsto> [Rule (MatchNot (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 9)))) action.Drop,
                             Rule (Match (Prot (Proto TCP))) action.Accept]
                 ] in
    to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                          (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw))))))"
  lemma " map simple_rule_ipv4_toString cool_example =
    [''DROP     all  --  10.128.0.0/9            0.0.0.0/0    '',
     ''ACCEPT     tcp  --  10.0.0.0/8            0.0.0.0/0    '',
     ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']"
  by eval
  
  lemma "map ipv4addr_wordinterval_toString (getParts cool_example) =
    [''{10.128.0.0 .. 10.255.255.255}'',
     ''{10.0.0.0 .. 10.127.255.255}'',
     ''{0.0.0.0 .. 9.255.255.255} u {11.0.0.0 .. 255.255.255.255}'']" by eval
  
  lemma "map ipv4addr_wordinterval_toString (build_ip_partition parts_connection_ssh cool_example) =
    [''{0.0.0.0 .. 9.255.255.255} u {10.128.0.0 .. 255.255.255.255}'',
     ''{10.0.0.0 .. 10.127.255.255}'']" by eval
  
  (*it is not minimal if we allow to further compress the node definitions?
  the receiver nodes could be combined to UNIV
  But minimal for a symmetric matrix*)
  lemma "access_matrix_pretty_ipv4 parts_connection_ssh cool_example =
    ([(''0.0.0.0'', ''{0.0.0.0 .. 9.255.255.255} u {10.128.0.0 .. 255.255.255.255}''),
      (''10.0.0.0'', ''{10.0.0.0 .. 10.127.255.255}'')],
     [(''10.0.0.0'', ''0.0.0.0''),
      (''10.0.0.0'', ''10.0.0.0'')])" by eval
end
context
begin
  (*now with a destination IP*)
  private definition "cool_example2 \<equiv> (let fw =
    [''FORWARD'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 8))) (Call ''foo'')],
     ''foo'' \<mapsto> [Rule (MatchNot (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 9)))) action.Drop,
                 Rule (MatchAnd (Match (Prot (Proto TCP))) (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,42)) 32)))) action.Accept]
                ] in
    to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                          (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw))))))"
  lemma "map simple_rule_ipv4_toString cool_example2 =
    [''DROP     all  --  10.128.0.0/9            0.0.0.0/0    '',
     ''ACCEPT     tcp  --  10.0.0.0/8            10.0.0.42/32    '',
     ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval
  
  (*not minimal*)
  lemma "map ipv4addr_wordinterval_toString (getParts cool_example2) =
    [''{10.128.0.0 .. 10.255.255.255}'', ''10.0.0.42'',
     ''{10.0.0.0 .. 10.0.0.41} u {10.0.0.43 .. 10.127.255.255}'',
     ''{0.0.0.0 .. 9.255.255.255} u {11.0.0.0 .. 255.255.255.255}'']" by eval
  
  lemma "map ipv4addr_wordinterval_toString (build_ip_partition parts_connection_ssh cool_example2) =
    [''{0.0.0.0 .. 9.255.255.255} u {10.128.0.0 .. 255.255.255.255}'', ''10.0.0.42'',
     ''{10.0.0.0 .. 10.0.0.41} u {10.0.0.43 .. 10.127.255.255}'']" by eval
  
  lemma "access_matrix_pretty_ipv4 parts_connection_ssh cool_example2 =
    ([(''0.0.0.0'', ''{0.0.0.0 .. 9.255.255.255} u {10.128.0.0 .. 255.255.255.255}''),
      (''10.0.0.42'', ''10.0.0.42''),
      (''10.0.0.0'', ''{10.0.0.0 .. 10.0.0.41} u {10.0.0.43 .. 10.127.255.255}'')
     ],
     [(''10.0.0.42'', ''10.0.0.42''),
      (''10.0.0.0'', ''10.0.0.42'')
     ])" by eval
  end

end