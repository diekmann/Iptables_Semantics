theory Code_haskell
imports "../Primitive_Matchers/Parser"
  "../Simple_Firewall/SimpleFw_toString"
  "../Semantics_Ternary/Optimizing"
begin

export_code Match MatchNot MatchAnd MatchAny
  Src Dst IIface OIface Prot Src_Ports Dst_Ports CT_State Extra
  ProtoAny Proto TCP UDP ICMP
  integer_to_16word
  Ip4AddrNetmask Ip4AddrRange
  CT_New CT_Established CT_Related CT_Untracked
  Accept Drop Log Reject Call Return Goto Empty Unknown
  dotteddecimal_toString ipv4addr_toString ipv4_cidr_toString action_toString
  common_primitive_toString
  simple_rule_toString
  unfold_ruleset_INPUT unfold_ruleset_FORWARD unfold_ruleset_OUTPUT map_of_string
  upper_closure
  ctstate_assume_new
  to_simple_firewall
  in Haskell module_name "Network.IPTables.Generated" file "tmp/"

end