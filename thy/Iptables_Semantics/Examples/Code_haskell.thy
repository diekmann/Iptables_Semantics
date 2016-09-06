theory Code_haskell
imports
  "../../Routing/IpRoute_Parser"
  "../Primitive_Matchers/Parser"
begin

definition word_less_eq :: "('a::len) word \<Rightarrow> ('a::len) word \<Rightarrow> bool" where
  "word_less_eq a b \<equiv> a \<le> b"

definition word_to_nat :: "('a::len) word \<Rightarrow> nat" where
  "word_to_nat = Word.unat"


definition mk_Set :: "'a list \<Rightarrow> 'a set" where
  "mk_Set = set"

text\<open>Assumes that you call @{const fill_l4_protocol} after parsing!\<close>
definition mk_L4Ports_pre :: "raw_ports \<Rightarrow> ipt_l4_ports" where
  "mk_L4Ports_pre ports_raw = L4Ports 0 ports_raw"


fun ipassmt_iprange_translate :: "'i::len ipt_iprange list negation_type \<Rightarrow> ('i word \<times> nat) list" where
  "ipassmt_iprange_translate (Pos ips) = concat (map ipt_iprange_to_cidr ips)" |
  "ipassmt_iprange_translate (Neg ips) = all_but_those_ips (concat (map ipt_iprange_to_cidr ips))"

definition to_ipassmt
  :: "(iface \<times> 'i::len ipt_iprange list negation_type) list \<Rightarrow> (iface \<times> ('i word \<times> nat) list) list" where
  "to_ipassmt assmt = map (\<lambda>(ifce, ips). (ifce, ipassmt_iprange_translate ips)) assmt"

export_code Rule
  Match MatchNot MatchAnd MatchAny
  Src Dst IIface OIface Prot Src_Ports Dst_Ports CT_State Extra
  mk_L4Ports_pre
  ProtoAny Proto TCP UDP ICMP L4_Protocol.IPv6ICMP L4_Protocol.SCTP L4_Protocol.GRE
  L4_Protocol.ESP L4_Protocol.AH
  Iface
  integer_to_16word nat_to_16word Nat word_less_eq word_to_nat
  nat_to_8word
  IpAddrNetmask IpAddrRange IpAddr
  CT_New CT_Established CT_Related CT_Untracked CT_Invalid
  TCP_Flags TCP_SYN TCP_ACK TCP_FIN TCP_RST TCP_URG TCP_PSH
  Accept Drop Log Reject Call Return Goto Empty Unknown
  action_toString
  (*IPv4*)
  ipv4addr_of_dotdecimal
  ipt_ipv4range_toString
  common_primitive_ipv4_toString
  common_primitive_match_expr_ipv4_toString
  simple_rule_ipv4_toString
  (*IPv6*)
  mk_ipv6addr IPv6AddrPreferred ipv6preferred_to_int int_to_ipv6preferred
  ipt_ipv6range_toString
  common_primitive_ipv6_toString
  common_primitive_match_expr_ipv6_toString
  simple_rule_ipv6_toString
  (*Goto support*)
  Semantics_Goto.rewrite_Goto_safe
  (*parser helpers:*) alist_and' compress_parsed_extra fill_l4_protocol Pos Neg mk_Set
  unfold_ruleset_CHAIN_safe map_of_string
  upper_closure
  abstract_for_simple_firewall optimize_matches
  packet_assume_new
  to_simple_firewall
  to_simple_firewall_without_interfaces
  sanity_wf_ruleset
  has_default_policy
  (*spoofing:*) ipassmt_generic_ipv4 ipassmt_generic_ipv6
  no_spoofing_iface ipassmt_sanity_defined map_of_ipassmt to_ipassmt
  Pos Neg
  (*debug*)
  simple_fw_valid
  debug_ipassmt_ipv4 debug_ipassmt_ipv6
  (*ip partitioning*)
  access_matrix_pretty_ipv4 access_matrix_pretty_ipv6
  mk_parts_connection_TCP (*parts_connection_ssh parts_connection_http*)
  (* routing *)
  PrefixMatch routing_rule_ext routing_action_ext
  routing_action_oiface_update metric_update routing_action_next_hop_update empty_rr_hlp sort_rtbl
  checking SML (*Haskell module_name "Network.IPTables.Generated" file "generated_code/"*)

end
