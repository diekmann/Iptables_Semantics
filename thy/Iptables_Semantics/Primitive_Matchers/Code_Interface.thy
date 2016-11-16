theory Code_Interface
imports 
  Common_Primitive_toString
  "../../IP_Addresses/IP_Address_Parser"
  "../Call_Return_Unfolding"
  Transform
  No_Spoof
  "../Simple_Firewall/SimpleFw_Compliance"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Simple_Firewall/Service_Matrix"
  "../Semantics_Ternary/Optimizing" (*do we use this?*)
  "../Semantics_Goto"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Native_Word/Code_Target_Bits_Int"
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Char"
begin

(*Note: common_primitive_match_expr_ipv4_toString can be really slow*)

section\<open>Code Interface\<close>

text\<open>HACK: rewrite quotes such that they are better printable by Isabelle\<close>
definition quote_rewrite :: "string \<Rightarrow> string" where
  "quote_rewrite \<equiv> map (\<lambda>c. if c = char_of_nat 34 then CHR ''~'' else c)"

lemma "quote_rewrite (''foo''@[char_of_nat 34]) = ''foo~''" by eval

text\<open>The parser returns the @{typ "'i::len common_primitive ruleset"} not as a map but as an association list.
      This function converts it\<close>

(*this is only to tighten the types*)
definition map_of_string_ipv4
  :: "(string \<times> 32 common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> 32 common_primitive rule list" where
  "map_of_string_ipv4 rs = map_of rs"
definition map_of_string_ipv6
  :: "(string \<times> 128 common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> 128 common_primitive rule list" where
  "map_of_string_ipv6 rs = map_of rs"
definition map_of_string
  :: "(string \<times> 'i common_primitive rule list) list \<Rightarrow> string \<rightharpoonup> 'i common_primitive rule list" where
  "map_of_string rs = map_of rs"


definition unfold_ruleset_CHAIN_safe :: "string \<Rightarrow> action \<Rightarrow> 'i::len common_primitive ruleset \<Rightarrow> 'i common_primitive rule list option" where
"unfold_ruleset_CHAIN_safe = unfold_optimize_ruleset_CHAIN optimize_primitive_univ"

lemma "(unfold_ruleset_CHAIN_safe chain a rs = Some rs') \<Longrightarrow> simple_ruleset rs'"
  by(simp add: Let_def unfold_ruleset_CHAIN_safe_def unfold_optimize_ruleset_CHAIN_def split: if_split_asm)

(*This is just for legacy code compatibility. Use the new _safe function instead*)
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


(* only used for ML/Haskell code to convert types *)
definition nat_to_8word :: "nat \<Rightarrow> 8 word" where
  "nat_to_8word i \<equiv> of_nat i"

definition nat_to_16word :: "nat \<Rightarrow> 16 word" where
  "nat_to_16word i \<equiv> of_nat i"

definition integer_to_16word :: "integer \<Rightarrow> 16 word" where
  "integer_to_16word i \<equiv> nat_to_16word (nat_of_integer i)"




context
begin
  private definition is_pos_Extra :: "'i::len common_primitive negation_type \<Rightarrow> bool" where
    "is_pos_Extra a \<equiv> (case a of Pos (Extra _) \<Rightarrow> True | _ \<Rightarrow> False)"
  private definition get_pos_Extra :: "'i::len common_primitive negation_type \<Rightarrow> string" where
    "get_pos_Extra a \<equiv> (case a of Pos (Extra e) \<Rightarrow> e | _ \<Rightarrow> undefined)"
  
  fun compress_parsed_extra
    :: "'i::len common_primitive negation_type list \<Rightarrow> 'i common_primitive negation_type list" where
    "compress_parsed_extra [] = []" |
    "compress_parsed_extra (a1#a2#as) = (if is_pos_Extra a1 \<and> is_pos_Extra a2
        then compress_parsed_extra (Pos (Extra (get_pos_Extra a1@'' ''@get_pos_Extra a2))#as)
        else a1#compress_parsed_extra (a2#as)
        )" |
    "compress_parsed_extra (a#as) = a#compress_parsed_extra as"
  
  lemma "compress_parsed_extra
    (map Pos [Extra ''-m'', (Extra ''recent'' :: 32 common_primitive),
              Extra ''--update'', Extra ''--seconds'', Extra ''60'',
              IIface (Iface ''foobar''),
              Extra ''--name'', Extra ''DEFAULT'', Extra ''--rsource'']) =
     map Pos [Extra ''-m recent --update --seconds 60'',
              IIface (Iface ''foobar''),
              Extra ''--name DEFAULT --rsource'']" by eval
  
  private lemma eval_ternary_And_Unknown_Unkown:
    "eval_ternary_And TernaryUnknown (eval_ternary_And TernaryUnknown tv) =
        eval_ternary_And TernaryUnknown tv"
    by(cases tv) (simp_all)
  
  private lemma is_pos_Extra_alist_and:
    "is_pos_Extra a \<Longrightarrow> alist_and (a#as) = MatchAnd (Match (Extra (get_pos_Extra a))) (alist_and as)"
    apply(cases a)
     apply(simp_all add: get_pos_Extra_def is_pos_Extra_def)
    apply(rename_tac e)
    by(case_tac e)(simp_all)
  
  private lemma compress_parsed_extra_matchexpr_helper:
    "ternary_ternary_eval (map_match_tac common_matcher p (alist_and (compress_parsed_extra as))) =
         ternary_ternary_eval (map_match_tac common_matcher p (alist_and as))"
   proof(induction as rule: compress_parsed_extra.induct)
   case 1 thus ?case by(simp)
   next
   case (2 a1 a2) thus ?case
     apply(simp add: is_pos_Extra_alist_and)
     apply(cases a1)
      apply(simp_all add: eval_ternary_And_Unknown_Unkown)
     done
   next
   case 3 thus ?case by(simp)
   qed
  
  text\<open>This lemma justifies that it is okay to fold together the parsed unknown tokens\<close>
  lemma compress_parsed_extra_matchexpr:
    "matches (common_matcher, \<alpha>) (alist_and (compress_parsed_extra as)) =
        matches (common_matcher, \<alpha>) (alist_and as)"
    apply(simp add: fun_eq_iff)
    apply(intro allI)
    apply(rule matches_iff_apply_f)
    apply(simp add: compress_parsed_extra_matchexpr_helper)
    done
end




subsection\<open>L4 Ports Parser Helper\<close>

context
begin
  text\<open>Replace all matches on ports with the unspecified @{term 0} protocol with the given @{typ primitive_protocol}.\<close>
  private definition fill_l4_protocol_raw
    :: "primitive_protocol \<Rightarrow> 'i::len common_primitive negation_type list \<Rightarrow> 'i common_primitive negation_type list"
  where
    "fill_l4_protocol_raw protocol \<equiv> NegPos_map
      (\<lambda> m. case m of Src_Ports (L4Ports x pts) \<Rightarrow> if x \<noteq> 0 then undefined else Src_Ports (L4Ports protocol pts)
                   |  Dst_Ports (L4Ports x pts) \<Rightarrow> if x \<noteq> 0 then undefined else Dst_Ports (L4Ports protocol pts)
                   |  Prot _ \<Rightarrow> undefined (*there should be no more match on the protocol if it was parsed from an iptables-save line*)
                   | m \<Rightarrow> m
      )"

  lemma "fill_l4_protocol_raw TCP [Neg (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)), Pos (Src_Ports (L4Ports 0 [(22,22)]))] =
          [Neg (Dst (IpAddrNetmask 0x7F000000 8)), Pos (Src_Ports (L4Ports 6 [(0x16, 0x16)]))]" by eval

  fun fill_l4_protocol
    :: "'i::len common_primitive negation_type list \<Rightarrow> 'i::len common_primitive negation_type list"
  where
    "fill_l4_protocol [] = []" |
    "fill_l4_protocol (Pos (Prot (Proto protocol)) # ms) = Pos (Prot (Proto protocol)) # fill_l4_protocol_raw protocol ms" |
    "fill_l4_protocol (Pos (Src_Ports _) # _) = undefined" | (*need to find proto first*)
    "fill_l4_protocol (Pos (Dst_Ports _) # _) = undefined" |
    "fill_l4_protocol (m # ms) = m # fill_l4_protocol ms"

  lemma "fill_l4_protocol [ Neg (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8))
                                , Neg (Prot (Proto UDP))
                                , Pos (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8))
                                , Pos (Prot (Proto TCP))
                                , Pos (Extra ''foo'')
                                , Pos (Src_Ports (L4Ports 0 [(22,22)]))
                                , Neg (Extra ''Bar'')] =
  [ Neg (Dst (IpAddrNetmask 0x7F000000 8))
  , Neg (Prot (Proto UDP))
  , Pos (Src (IpAddrNetmask 0x7F000000 8))
  , Pos (Prot (Proto TCP))
  , Pos (Extra ''foo'')
  , Pos (Src_Ports (L4Ports TCP [(0x16, 0x16)]))
  , Neg (Extra ''Bar'')]" by eval
end



(*currently unused and unverifed. may be needed for future use*)
definition prefix_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "prefix_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "prefix_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval


end
