theory Code_haskell
imports "../Primitive_Matchers/Parser"
  "../Simple_Firewall/SimpleFw_toString"
  "../Semantics_Ternary/Optimizing"
begin

definition word_less_eq :: "('a::len) word \<Rightarrow> ('a::len) word \<Rightarrow> bool" where
  "word_less_eq a b \<equiv> a \<le> b"

definition word_to_nat :: "('a::len) word \<Rightarrow> nat" where
  "word_to_nat = Word.unat"


definition "to_simple_firewall_without_interfaces rs \<equiv>
    to_simple_firewall
    (upper_closure
    (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
    (optimize_matches abstract_for_simple_firewall
    (ctstate_assume_new
    (upper_closure rs)))))"

definition mk_Set :: "'a list \<Rightarrow> 'a set" where
  "mk_Set = set"

export_code Rule
  Match MatchNot MatchAnd MatchAny
  Src Dst IIface OIface Prot Src_Ports Dst_Ports CT_State Extra
  ProtoAny Proto TCP UDP ICMP Iface
  integer_to_16word nat_to_16word Nat word_less_eq word_to_nat
  Ip4AddrNetmask Ip4AddrRange Ip4Addr
  CT_New CT_Established CT_Related CT_Untracked
  Accept Drop Log Reject Call Return Goto Empty Unknown
  dotteddecimal_toString ipv4addr_toString ipv4_cidr_toString action_toString
  common_primitive_toString common_primitive_match_expr_toString
  simple_rule_toString
  Semantics_Goto.rewrite_Goto
  (*parser helpers:*) alist_and' compress_parsed_extra Pos Neg mk_Set
  unfold_ruleset_INPUT unfold_ruleset_FORWARD unfold_ruleset_OUTPUT map_of_string
  upper_closure
  abstract_for_simple_firewall optimize_matches
  ctstate_assume_new
  to_simple_firewall
  to_simple_firewall_without_interfaces
  sanity_wf_ruleset
  in Haskell module_name "Network.IPTables.Generated" file "tmp/"

end