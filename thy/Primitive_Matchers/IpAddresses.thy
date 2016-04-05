theory IpAddresses
imports "../Bitmagic/IPv4Addr"
  "../Bitmagic/Numberwang_Ln"
  "../Bitmagic/CIDRSplit"
  "../Bitmagic/WordInterval_Lists"
begin


text{*Misc*}
  (*TODO:move?*)
  lemma ipv4range_set_from_prefix_lowest: "a \<in> ipv4range_set_from_prefix a n" using ip4_set_def ipv4range_set_from_prefix_eq_ip4_set by blast

  (*this is why I call the previous lemma 'lowest'*)
  lemma "valid_prefix (PrefixMatch a n) \<Longrightarrow> is_lowest_element a (ipv4range_set_from_prefix a n)"
    apply(simp add: is_lowest_element_def ipv4range_set_from_prefix_lowest)
    apply(simp add: ipv4range_set_from_prefix_eq_ip4_set ip4_set_def)
    apply(simp add: valid_prefix_def pfxm_mask_def)
    apply clarify
    by (metis add.left_neutral antisym_conv word_and_le2 word_bw_comms(1) word_plus_and_or_coroll2)



section{*IPv4 Addresses*}

--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 33 = {0}"
by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipv4range_set_from_prefix_def ipv4range_set_from_netmask_def)


subsection{*IPv4 Addresses in CIDR Notation*}
  (*We need a separate ipv4addr syntax thy*)

  fun ipcidr_to_interval_start :: "('a::len word \<times> nat) \<Rightarrow> 'a::len word" where
    "ipcidr_to_interval_start (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('a) - len);
          network_prefix = (pre AND netmask)
      in network_prefix)"
  fun ipcidr_to_interval_end :: "('a::len word \<times> nat) \<Rightarrow> 'a::len word" where
    "ipcidr_to_interval_end (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('a) - len);
          network_prefix = (pre AND netmask)
      in network_prefix OR (NOT netmask))"
  definition ipcidr_to_interval :: "('a::len word \<times> nat) \<Rightarrow> ('a::len word \<times> 'a::len word)" where
    "ipcidr_to_interval cidr = (ipcidr_to_interval_start cidr, ipcidr_to_interval_end cidr)"

  text{*This @{text "len_of TYPE('a)"} is 32 for IPv4 addresses.*}
  lemma ipv4cidr_to_interval_simps[code_unfold]: "ipcidr_to_interval ((pre::ipv4addr), len) = (
      let netmask = (mask len) << (32 - len);
          network_prefix = (pre AND netmask)
      in (network_prefix, network_prefix OR (NOT netmask)))"
  by(simp add: ipcidr_to_interval_def Let_def)


  lemma ipcidr_to_interval_ipv4range_set_from_prefix:
    "ipv4range_set_from_prefix base len = {ipcidr_to_interval_start (base,len) .. ipcidr_to_interval_end (base,len)}"
    apply(simp add: Let_def ipcidr_to_interval_def)
    apply(subst ipv4range_set_from_prefix_alt)
    by (metis ipv4range_set_from_prefix_alt ipv4range_set_from_prefix_alt1 ipv4range_set_from_netmask_def)

  declare ipcidr_to_interval_start.simps[simp del] ipcidr_to_interval_end.simps[simp del]

  (*TODO: remove this lemma?, refactor*)
  lemma ipv4cidr_to_interval: "ipcidr_to_interval (base, len) = (s,e) \<Longrightarrow> ipv4range_set_from_prefix base len = {s .. e}"
    apply(simp add: Let_def ipcidr_to_interval_def)
    using ipcidr_to_interval_ipv4range_set_from_prefix by presburger



  fun ipv4cidr_conjunct :: "(ipv4addr \<times> nat) \<Rightarrow> (ipv4addr \<times> nat) \<Rightarrow> (ipv4addr \<times> nat) option" where 
    "ipv4cidr_conjunct (base1, m1) (base2, m2) = (if ipv4range_set_from_prefix base1 m1 \<inter> ipv4range_set_from_prefix base2 m2 = {}
       then
        None
       else if 
        ipv4range_set_from_prefix base1 m1 \<subseteq> ipv4range_set_from_prefix base2 m2
       then 
        Some (base1, m1)
       else
        Some (base2, m2)
      )"
  
  lemma ipv4cidr_conjunct_correct: "(case ipv4cidr_conjunct (b1, m1) (b2, m2) of Some (bx, mx) \<Rightarrow> ipv4range_set_from_prefix bx mx | None \<Rightarrow> {}) = 
      (ipv4range_set_from_prefix b1 m1) \<inter> (ipv4range_set_from_prefix b2 m2)"
    apply(simp split: split_if_asm)
    using ipv4range_prefix_intersect by fast
  declare ipv4cidr_conjunct.simps[simp del]

  definition ipv4_cidr_tuple_to_interval :: "(ipv4addr \<times> nat) \<Rightarrow> 32 wordinterval" where
    "ipv4_cidr_tuple_to_interval iprng = ipv4range_range (ipcidr_to_interval iprng)"

  lemma ipv4range_to_set_ipv4_cidr_tuple_to_interval: "ipv4range_to_set (ipv4_cidr_tuple_to_interval (b, m)) = ipv4range_set_from_prefix b m"
    unfolding ipv4_cidr_tuple_to_interval_def ipcidr_to_interval_ipv4range_set_from_prefix ipcidr_to_interval_def
    using ipv4range_range_set_eq by blast

  lemma [code_unfold]: 
  "ipv4cidr_conjunct ips1 ips2 = (if ipv4range_empty (ipv4range_intersection (ipv4_cidr_tuple_to_interval ips1) (ipv4_cidr_tuple_to_interval ips2))
       then
        None
       else if 
        ipv4range_subset (ipv4_cidr_tuple_to_interval ips1) (ipv4_cidr_tuple_to_interval ips2)
       then 
        Some ips1
       else
        Some ips2
      )"
  apply(simp)
  apply(cases ips1, cases ips2, rename_tac b1 m1 b2 m2, simp)
  apply(safe)
     apply(auto simp add: ipv4range_to_set_ipv4_cidr_tuple_to_interval ipv4cidr_conjunct.simps split:split_if_asm)
  done
  value "ipv4cidr_conjunct (0,0) (8,1)" (*with the code_unfold lemma before, this works!*)


  definition ipv4cidr_union_set :: "(ipv4addr \<times> nat) set \<Rightarrow> ipv4addr set" where
    "ipv4cidr_union_set ips \<equiv> \<Union>(base, len) \<in> ips. ipv4range_set_from_prefix base len"


  (*helper we use for spoofing protection specification*)
  definition all_but_those_ips :: "(ipv4addr \<times> nat) list \<Rightarrow> (ipv4addr \<times> nat) list" where
    "all_but_those_ips cidrips = ipv4range_split (ipv4range_invert (l2br (map ipcidr_to_interval cidrips)))"
  
  lemma all_but_those_ips: "ipv4cidr_union_set (set (all_but_those_ips cidrips)) = UNIV - (\<Union> (ip,n) \<in> set cidrips. ipv4range_set_from_prefix ip n)"
    apply(simp add:)
    unfolding ipv4cidr_union_set_def all_but_those_ips_def
    apply(simp)
    apply(simp add: ipv4range_split_prefix[simplified])
    apply(simp add: ipv4range_invert_def ipv4range_setminus_def)
    apply(simp add: ipv4range_UNIV_def)
    apply(simp add: l2br)
    apply(simp add: ipcidr_to_interval_def)
    apply(simp add: ipcidr_to_interval_ipv4range_set_from_prefix)
    done
  



subsection{*IPv4 Addresses in IPTables Notation (how we parse it)*}
  (*src dst ipv4*)
  datatype ipt_ipv4range = Ip4Addr "nat \<times> nat \<times> nat \<times> nat"
                        | Ip4AddrNetmask "nat \<times> nat \<times> nat \<times> nat" nat -- "addr/xx"
                        | Ip4AddrRange  "nat \<times> nat \<times> nat \<times> nat" "nat \<times> nat \<times> nat \<times> nat"-- "-m iprange --src-range a.b.c.d-e.f.g.h"
                            (*the range is inclusive*)
  
  
  fun ipv4s_to_set :: "ipt_ipv4range \<Rightarrow> ipv4addr set" where
    "ipv4s_to_set (Ip4AddrNetmask base m) = ipv4range_set_from_prefix (ipv4addr_of_dotdecimal base) m" |
    "ipv4s_to_set (Ip4Addr ip) = { ipv4addr_of_dotdecimal ip }" |
    "ipv4s_to_set (Ip4AddrRange ip1 ip2) = { ipv4addr_of_dotdecimal ip1 .. ipv4addr_of_dotdecimal ip2 }"
  
  text{*@{term ipv4s_to_set} can only represent an empty set if it is an empty range.*}
  lemma ipv4s_to_set_nonempty: "ipv4s_to_set ip = {} \<longleftrightarrow> (\<exists>ip1 ip2. ip = Ip4AddrRange ip1 ip2 \<and> ipv4addr_of_dotdecimal ip1 > ipv4addr_of_dotdecimal ip2)"
    apply(cases ip)
      apply(simp)
     apply(simp add: ipv4range_set_from_prefix_alt bitmagic_zeroLast_leq_or1Last)
    apply(simp add:linorder_not_le)
    done
  
  text{*maybe this is necessary as code equation?*}
  lemma element_ipv4s_to_set[code_unfold]: "addr \<in> ipv4s_to_set X = (
    case X of (Ip4AddrNetmask pre len) \<Rightarrow> ((ipv4addr_of_dotdecimal pre) AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> (ipv4addr_of_dotdecimal pre) OR (mask (32 - len))
    | Ip4Addr ip \<Rightarrow> (addr = (ipv4addr_of_dotdecimal ip))
    | Ip4AddrRange ip1 ip2 \<Rightarrow> ipv4addr_of_dotdecimal ip1 \<le> addr \<and> ipv4addr_of_dotdecimal ip2 \<ge> addr)"
  apply(cases X)
    apply(simp)
   apply(simp add: ipv4range_set_from_prefix_alt)
  apply(simp)
  done
  

  text{*IPv4 address ranges to @{text "(start, end)"} notation*}
  fun ipt_ipv4range_to_interval :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> ipv4addr)" where
    "ipt_ipv4range_to_interval (Ip4Addr addr) = (ipv4addr_of_dotdecimal addr, ipv4addr_of_dotdecimal addr)" |
    "ipt_ipv4range_to_interval (Ip4AddrNetmask pre len) = ipcidr_to_interval ((ipv4addr_of_dotdecimal pre), len)" |
    "ipt_ipv4range_to_interval (Ip4AddrRange ip1 ip2) = (ipv4addr_of_dotdecimal ip1, ipv4addr_of_dotdecimal ip2)"
  
  lemma ipt_ipv4range_to_interval: "ipt_ipv4range_to_interval ip = (s,e) \<Longrightarrow> {s .. e} = ipv4s_to_set ip"
    by(cases ip) (auto simp add: ipv4cidr_to_interval)


  text{*A list of IPv4 address ranges to a @{typ "32 wordinterval"}.
        The nice thing is: the usual set operations are defined on this type.
        We can use the existing function @{const l2br_intersect} if we want the intersection of the supplied list*}
  lemma "wordinterval_to_set (l2br_intersect (map ipt_ipv4range_to_interval ips)) = (\<Inter> ip \<in> set ips. ipv4s_to_set ip)"
    apply(simp add: l2br_intersect)
    using ipt_ipv4range_to_interval by blast
  
  text{*We can use @{const l2br} if we want the union of the supplied list*}
  lemma "wordinterval_to_set (l2br (map ipt_ipv4range_to_interval ips)) = (\<Union> ip \<in> set ips. ipv4s_to_set ip)"
    apply(simp add: l2br)
    using ipt_ipv4range_to_interval by blast

  text{*A list of (negated) IPv4 address to a @{typ "32 wordinterval"}.*}
  definition ipt_ipv4range_negation_type_to_br_intersect :: "ipt_ipv4range negation_type list \<Rightarrow> 32 wordinterval" where
    "ipt_ipv4range_negation_type_to_br_intersect l = l2br_negation_type_intersect (NegPos_map ipt_ipv4range_to_interval l)" 

  lemma ipt_ipv4range_negation_type_to_br_intersect: "wordinterval_to_set (ipt_ipv4range_negation_type_to_br_intersect l) =
      (\<Inter> ip \<in> set (getPos l). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipv4s_to_set ip)"
    apply(simp add: ipt_ipv4range_negation_type_to_br_intersect_def l2br_negation_type_intersect NegPos_map_simps)
    using ipt_ipv4range_to_interval by blast

  text{*The @{typ "32 wordinterval"} can be translated back into a list of IP ranges.
        If a list of intervals is enough, we can use @{const br2l}.
        If we need it in @{typ ipt_ipv4range}, we can use this function.*}
  definition wi_2_cidr_ipt_ipv4range_list :: "32 wordinterval \<Rightarrow> ipt_ipv4range list" where
    "wi_2_cidr_ipt_ipv4range_list r = map (\<lambda> (base, len). Ip4AddrNetmask (dotdecimal_of_ipv4addr base) len) (ipv4range_split r)"

  lemma wi_2_cidr_ipt_ipv4range_list: "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = wordinterval_to_set r"
    proof -
    have "\<And>a. ipv4s_to_set (case a of (base, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr base) x) = (case a of (x, xa) \<Rightarrow> ipv4range_set_from_prefix x xa)"
      by(clarsimp simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
    hence "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = \<Union>((\<lambda>(x, y). ipv4range_set_from_prefix x y) ` set (ipv4range_split r))"
      unfolding wi_2_cidr_ipt_ipv4range_list_def by(simp)
    thus ?thesis
    using ipv4range_split_prefix by presburger
  qed

  text{*For example, this allows the following transformation*}
  definition ipt_ipv4range_compress :: "ipt_ipv4range negation_type list \<Rightarrow> ipt_ipv4range list" where
    "ipt_ipv4range_compress = wi_2_cidr_ipt_ipv4range_list \<circ> ipt_ipv4range_negation_type_to_br_intersect"

  lemma ipt_ipv4range_compress: "(\<Union> ip \<in> set (ipt_ipv4range_compress l). ipv4s_to_set ip) =
      (\<Inter> ip \<in> set (getPos l). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipv4s_to_set ip)"
    by (metis wi_2_cidr_ipt_ipv4range_list comp_apply ipt_ipv4range_compress_def ipt_ipv4range_negation_type_to_br_intersect)
  
  definition normalized_cidr_ip :: "ipt_ipv4range \<Rightarrow> bool" where
    "normalized_cidr_ip ip \<equiv> case ip of Ip4AddrNetmask _ _ \<Rightarrow> True | _ \<Rightarrow> False"

  lemma wi_2_cidr_ipt_ipv4range_list_normalized_Ip4AddrNetmask: 
    "\<forall>a'\<in>set (wi_2_cidr_ipt_ipv4range_list as). normalized_cidr_ip a'"
    apply(clarify)
    apply(simp add: wi_2_cidr_ipt_ipv4range_list_def normalized_cidr_ip_def)
    by force

  lemma ipt_ipv4range_compress_normalized_Ip4AddrNetmask:
    "\<forall>a'\<in>set (ipt_ipv4range_compress as). normalized_cidr_ip a'"
    by(simp add: ipt_ipv4range_compress_def wi_2_cidr_ipt_ipv4range_list_normalized_Ip4AddrNetmask)


  
  definition ipt_ipv4range_to_cidr :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> nat) list" where
    "ipt_ipv4range_to_cidr ips = ipv4range_split (ipv4range_range (ipt_ipv4range_to_interval ips))"

  lemma ipt_ipv4range_to_cidr: "ipv4cidr_union_set (set (ipt_ipv4range_to_cidr ips)) = (ipv4s_to_set ips)"
    apply(simp add: ipt_ipv4range_to_cidr_def)
    by (metis (no_types, hide_lams) SUP_def ipt_ipv4range_to_interval ipv4cidr_union_set_def ipv4range_range.cases ipv4range_split_prefix_single)
    

end
