theory Code_Interface
imports 
  Common_Primitive_toString
  "../../IP_Addresses/IP_Address_Parser"
  "../Call_Return_Unfolding"
  Transform
  No_Spoof
  "../Simple_Firewall/SimpleFw_Compliance"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Simple_Firewall/Service_Matrices"
  "../Semantics_Ternary/Optimizing" (*do we use this?*)
  "../Semantics_Goto"
  "../../Simple_Firewall/SimpleFw_toString" (*hmm, here?*)
  "../../Native_Word/Code_Target_Bits_Int"
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Char"
begin

(*Note: common_primitive_match_expr_toString can be really slow*)

section\<open>Code Interface\<close>

text\<open>HACK: rewrite quotes such that they are better printable by Isabelle\<close>
definition quote_rewrite :: "string \<Rightarrow> string" where
  "quote_rewrite \<equiv> map (\<lambda>c. if c = Char Nibble2 Nibble2 then CHR ''~'' else c)"

lemma "quote_rewrite (''foo''@[Char Nibble2 Nibble2]) = ''foo~''" by eval

text\<open>The parser returns the @{typ "'i::len common_primitive ruleset"} not as a map but as an association list.
      This function converts it\<close>
(*TODO: this is IPv4 only currently*)
definition map_of_string_ipv4 :: "(string \<times> 32 common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> 32 common_primitive rule list" where
  "map_of_string_ipv4 rs = map_of rs"


definition unfold_ruleset_CHAIN_safe :: "string \<Rightarrow> action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i common_primitive rule list option" where
"unfold_ruleset_CHAIN_safe = unfold_optimize_ruleset_CHAIN optimize_primitive_univ"

lemma "(unfold_ruleset_CHAIN_safe chain a rs = Some rs') \<Longrightarrow> simple_ruleset rs'"
  by(simp add: Let_def unfold_ruleset_CHAIN_safe_def unfold_optimize_ruleset_CHAIN_def split: split_if_asm)

(*TODO: This is just for legacy code compatibility. Use the new _safe function instead*)
definition unfold_ruleset_CHAIN :: "string \<Rightarrow> action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i common_primitive rule list" where
  "unfold_ruleset_CHAIN chain default_action rs = the (unfold_ruleset_CHAIN_safe chain default_action rs)"


definition unfold_ruleset_FORWARD :: "action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i::len common_primitive rule list" where
  "unfold_ruleset_FORWARD = unfold_ruleset_CHAIN ''FORWARD''"

definition unfold_ruleset_INPUT :: "action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i::len common_primitive rule list" where
  "unfold_ruleset_INPUT = unfold_ruleset_CHAIN ''INPUT''"

definition unfold_ruleset_OUTPUT :: "action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i::len common_primitive rule list" where
  "unfold_ruleset_OUTPUT \<equiv> unfold_ruleset_CHAIN ''OUTPUT''"


lemma "let fw = [''FORWARD'' \<mapsto> []] in
  unfold_ruleset_FORWARD action.Drop fw
  = [Rule (MatchAny :: 32 common_primitive match_expr) action.Drop]" by eval


(*
definition port_to_nat :: "16 word \<Rightarrow> nat" where
  "port_to_nat p = unat p"
*)

(* only used for ML code to convert types *)
definition nat_to_8word :: "nat \<Rightarrow> 8 word" where
  "nat_to_8word i \<equiv> of_nat i"

definition nat_to_16word :: "nat \<Rightarrow> 16 word" where
  "nat_to_16word i \<equiv> of_nat i"


definition integer_to_16word :: "integer \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> nat_to_16word (nat_of_integer i)"

(*
(*TODO: does this speed things up?*)
lemma [code_unfold]: "nat_to_16word = word_of_int \<circ> int"
  "ipv4addr_of_nat = word_of_int \<circ> int"
  "ipv6addr_of_nat = word_of_int \<circ> int"
  "nat_to_8word = word_of_int \<circ> int"
  by(simp add: fun_eq_iff nat_to_16word_def ipv4addr_of_nat_def ipv6addr_of_nat_def nat_to_8word_def word_of_nat)+
*)
(*
definition integer_to_16word :: "integer \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> word_of_int (int_of_integer i)"

lemma "integer_to_16word (- 1) = 0xFFFF" by eval
*)
(*
definition integer_to_16word :: "int \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> nat_to_16word (nat i)"
*)
(*
definition integer_to_16word :: "int \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> Word.word_of_int i"

*)

text\<open>Example\<close>
context
begin
  (*cool example*)
  lemma "let fw = [''FORWARD'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 8))) (Call ''foo'')],
                   ''foo'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,128,0,0)) 9))) action.Return,
                               Rule (Match (Prot (Proto TCP))) action.Accept]
                   ] in
    let simplfw = to_simple_firewall
      (upper_closure (optimize_matches abstract_for_simple_firewall
        (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw)))))
    in map simple_rule_toString simplfw =
    [''ACCEPT     tcp  --  10.0.0.0/9            0.0.0.0/0    '',
     ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval
  
  (*cooler example*)
  private definition "cool_example \<equiv> (let fw = 
                [''FORWARD'' \<mapsto> [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 8))) (Call ''foo'')],
                 ''foo'' \<mapsto> [Rule (MatchNot (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10,0,0,0)) 9)))) action.Drop,
                             Rule (Match (Prot (Proto TCP))) action.Accept]
                 ] in
    to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                          (upper_closure (packet_assume_new (unfold_ruleset_FORWARD action.Drop fw))))))"
  lemma " map simple_rule_toString cool_example =
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
  lemma "access_matrix_pretty parts_connection_ssh cool_example =
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
  lemma "map simple_rule_toString cool_example2 =
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
  
  lemma "access_matrix_pretty parts_connection_ssh cool_example2 =
    ([(''0.0.0.0'', ''{0.0.0.0 .. 9.255.255.255} u {10.128.0.0 .. 255.255.255.255}''),
      (''10.0.0.42'', ''10.0.0.42''),
      (''10.0.0.0'', ''{10.0.0.0 .. 10.0.0.41} u {10.0.0.43 .. 10.127.255.255}'')
     ],
     [(''10.0.0.42'', ''10.0.0.42''),
      (''10.0.0.0'', ''10.0.0.42'')
     ])" by eval
  end



(*currently unused and unverifed. may be needed for future use*)
definition prefix_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "prefix_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "prefix_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval



end
