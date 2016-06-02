theory Code_haskell
imports "../Primitive_Matchers/Parser"
  (*
  "../Simple_Firewall/IPPartitioning"*)
  "../Routing/IpRoute_Parser"
begin

definition word_less_eq :: "('a::len) word \<Rightarrow> ('a::len) word \<Rightarrow> bool" where
  "word_less_eq a b \<equiv> a \<le> b"

definition word_to_nat :: "('a::len) word \<Rightarrow> nat" where
  "word_to_nat = Word.unat"


definition mk_Set :: "'a list \<Rightarrow> 'a set" where
  "mk_Set = set"


fun ipassmt_iprange_translate :: "32 ipt_iprange list negation_type \<Rightarrow> (32 word \<times> nat) list" where
  "ipassmt_iprange_translate (Pos ips) = concat (map ipt_iprange_to_cidr ips)" |
  "ipassmt_iprange_translate (Neg ips) = all_but_those_ips (concat (map ipt_iprange_to_cidr ips))"

definition to_ipassmt :: "(iface \<times> 32 ipt_iprange list negation_type) list \<Rightarrow> (iface \<times> (32 word \<times> nat) list) list" where
  "to_ipassmt assmt = map (\<lambda>(ifce, ips). (ifce, ipassmt_iprange_translate ips)) assmt"

export_code Rule
  Match MatchNot MatchAnd MatchAny
  Src Dst IIface OIface Prot Src_Ports Dst_Ports CT_State Extra
  ProtoAny Proto TCP UDP ICMP Iface
  integer_to_16word nat_to_16word Nat word_less_eq word_to_nat
  nat_to_8word
  ipv4addr_of_dotdecimal IpAddrNetmask IpAddrRange IpAddr
  CT_New CT_Established CT_Related CT_Untracked CT_Invalid
  TCP_Flags TCP_SYN TCP_ACK TCP_FIN TCP_RST TCP_URG TCP_PSH
  Accept Drop Log Reject Call Return Goto Empty Unknown
  dotteddecimal_toString ipv4addr_toString ipv4_cidr_toString action_toString
  ipt_ipv4range_toString ipv4addr_toString
  common_primitive_v4_toString common_primitive_match_expr_toString
  simple_rule_toString
  Semantics_Goto.rewrite_Goto_safe
  (*parser helpers:*) alist_and' compress_parsed_extra Pos Neg mk_Set
  unfold_ruleset_CHAIN_safe map_of_string_ipv4
  upper_closure
  abstract_for_simple_firewall optimize_matches
  packet_assume_new
  to_simple_firewall
  to_simple_firewall_without_interfaces
  sanity_wf_ruleset
  (*spoofing:*) ipassmt_generic
  no_spoofing_iface ipassmt_sanity_defined map_of_ipassmt to_ipassmt debug_ipassmt
  Pos Neg
  (*ip partitioning*)
  access_matrix_pretty mk_parts_connection_TCP (*parts_connection_ssh parts_connection_http*)
  (* routing *)
  PrefixMatch routing_action_oiface_update metric_update routing_action_next_hop_update empty_rr_hlp
  in Haskell module_name "Network.IPTables.Generated" file "generated_code/"

end
