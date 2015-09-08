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



text{*The Example from @{file "TUM_Net_Firewall/TUM_Spoofing_new3.thy"}.
  Only used for testing and demonstration purposes.*}
definition "example_TUM_i8_spoofing_ipassmt =
 [(Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,213,4), 24)]),
  (Iface ''eth1.96'', [(ipv4addr_of_dotdecimal (131,159,14,3), 25)]),
  (Iface ''eth1.108'', [(ipv4addr_of_dotdecimal (131,159,14,129), 26)]),
  (Iface ''eth1.109'', [(ipv4addr_of_dotdecimal (131,159,20,11), 24)]),
  (Iface ''eth1.110'', all_but_those_ips [
    (ipv4addr_of_dotdecimal (131,159,14,0), 23),
    (ipv4addr_of_dotdecimal (131,159,20,0), 23),
    (ipv4addr_of_dotdecimal (192,168,212,0), 23),
    (ipv4addr_of_dotdecimal (188,95,233,0), 24),
    (ipv4addr_of_dotdecimal (188,95,232,192), 27),
    (ipv4addr_of_dotdecimal (188,95,234,0), 23),
    (ipv4addr_of_dotdecimal (192,48,107,0), 24),
    (ipv4addr_of_dotdecimal (188,95,236,0), 22),
    (ipv4addr_of_dotdecimal (185,86,232,0), 22)
    ]), (*INET*)
  (Iface ''eth1.116'', [(ipv4addr_of_dotdecimal (131,159,15,131), 26)]),
  (Iface ''eth1.152'', [(ipv4addr_of_dotdecimal (131,159,15,252), 28)]),
  (Iface ''eth1.171'', [(ipv4addr_of_dotdecimal (131,159,15,2), 26)]),
  (Iface ''eth1.173'', [(ipv4addr_of_dotdecimal (131,159,21,252), 24)]),
  (Iface ''eth1.1010'', [(ipv4addr_of_dotdecimal (131,159,15,227), 28)]),
  (Iface ''eth1.1011'', [(ipv4addr_of_dotdecimal (131,159,14,194), 27)]),
  (Iface ''eth1.1012'', [(ipv4addr_of_dotdecimal (131,159,14,238), 28)]),
  (Iface ''eth1.1014'', [(ipv4addr_of_dotdecimal (131,159,15,217), 27)]),
  (Iface ''eth1.1016'', [(ipv4addr_of_dotdecimal (131,159,15,66), 26)]),
  (Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,242), 28)]),
  (Iface ''eth1.1111'', [(ipv4addr_of_dotdecimal (192,168,212,4), 24)]),
  (Iface ''eth1.97'', [(ipv4addr_of_dotdecimal (188,95,233,2), 24)]),
  (Iface ''eth1.1019'', [(ipv4addr_of_dotdecimal (188,95,234,2), 23)]),
  (Iface ''eth1.1020'', [(ipv4addr_of_dotdecimal (192,48,107,2), 24)]),
  (Iface ''eth1.1023'', [(ipv4addr_of_dotdecimal (188,95,236,2), 22)]),
  (Iface ''eth1.1025'', [(ipv4addr_of_dotdecimal (185,86,232,2), 22)]),
  (Iface ''eth1.1024'', all_but_those_ips [
    (ipv4addr_of_dotdecimal (131,159,14,0), 23),
    (ipv4addr_of_dotdecimal (131,159,20,0), 23),
    (ipv4addr_of_dotdecimal (192,168,212,0), 23),
    (ipv4addr_of_dotdecimal (188,95,233,0), 24),
    (ipv4addr_of_dotdecimal (188,95,232,192), 27),
    (ipv4addr_of_dotdecimal (188,95,234,0), 23),
    (ipv4addr_of_dotdecimal (192,48,107,0), 24),
    (ipv4addr_of_dotdecimal (188,95,236,0), 22),
    (ipv4addr_of_dotdecimal (185,86,232,0), 22)
    ]) (*transfer net*)]"


fun ipassmt_iprange_translate :: "ipt_ipv4range list negation_type \<Rightarrow> (32 word \<times> nat) list" where
  "ipassmt_iprange_translate (Pos ips) = concat (map ipt_ipv4range_to_cidr ips)" |
  "ipassmt_iprange_translate (Neg ips) = all_but_those_ips (concat (map ipt_ipv4range_to_cidr ips))"

definition to_ipassmt :: "(iface \<times> ipt_ipv4range list negation_type) list \<Rightarrow> (iface \<times> (32 word \<times> nat) list) list" where
  "to_ipassmt assmt = map (\<lambda>(ifce, ips). (ifce, ipassmt_iprange_translate ips)) assmt"

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
  (*spoofing:*) example_TUM_i8_spoofing_ipassmt
  no_spoofing_iface ipassmt_sanity_defined map_of_ipassmt to_ipassmt debug_ipassmt
  Pos Neg
  in Haskell module_name "Network.IPTables.Generated" file "generated_code/"

end