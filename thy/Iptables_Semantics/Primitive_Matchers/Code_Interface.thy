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
  "quote_rewrite \<equiv> map (\<lambda>c. if c = Char Nibble2 Nibble2 then CHR ''~'' else c)"

lemma "quote_rewrite (''foo''@[Char Nibble2 Nibble2]) = ''foo~''" by eval

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
  by(simp add: Let_def unfold_ruleset_CHAIN_safe_def unfold_optimize_ruleset_CHAIN_def split: split_if_asm)

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



(*currently unused and unverifed. may be needed for future use*)
definition prefix_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "prefix_to_strange_inverse_cisco_mask n \<equiv> dotdecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "prefix_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "prefix_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval


end
