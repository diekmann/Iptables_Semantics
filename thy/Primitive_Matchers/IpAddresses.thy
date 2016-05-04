theory IpAddresses
imports "../Bitmagic/IPv4Addr"
  "../Bitmagic/Numberwang_Ln"
  "../Bitmagic/CIDRSplit"
  "../Bitmagic/WordInterval_Lists"
begin


text{*Misc*}
  (*TODO: delete?*)
  (*TODO:move?*)
  lemma ipv4range_set_from_prefix_lowest: "a \<in> ipset_from_cidr a n" 
    using ip_cidr_set_def ipv4range_set_from_prefix_eq_ip_cidr_set by blast

  (*this is why I call the previous lemma 'lowest'*)
  lemma "valid_prefix (PrefixMatch a n) \<Longrightarrow> is_lowest_element a (ipset_from_cidr a n)"
    apply(simp add: is_lowest_element_def ipv4range_set_from_prefix_lowest)
    apply(simp add: ipv4range_set_from_prefix_eq_ip_cidr_set ip_cidr_set_def)
    apply(simp add: valid_prefix_def pfxm_mask_def)
    apply clarify
    by (metis add.left_neutral antisym_conv word_and_le2 word_bw_comms(1) word_plus_and_or_coroll2)



section{*IPv4 Addresses*}

--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 33 = {0}"
by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipv4range_set_from_prefix_def ipv4range_set_from_netmask_def)


  (*TODO: move to IPv4?*)
  text{*This @{text "len_of TYPE('a)"} is 32 for IPv4 addresses.*}
  lemma ipv4cidr_to_interval_simps[code_unfold]: "ipcidr_to_interval ((pre::ipv4addr), len) = (
      let netmask = (mask len) << (32 - len);
          network_prefix = (pre AND netmask)
      in (network_prefix, network_prefix OR (NOT netmask)))"
  by(simp add: ipcidr_to_interval_def Let_def ipcidr_to_interval_start.simps ipcidr_to_interval_end.simps)

  (*TODO: remove this lemma?, refactor*)
  lemma ipv4cidr_to_interval: "ipcidr_to_interval (base, len) = (s,e) \<Longrightarrow> ipv4range_set_from_prefix base len = {s .. e}"
    apply(subst transition_lemma_ipv4_delete_me)
    apply(simp add: Let_def ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast



  fun ipcidr_conjunct :: "('i::len word \<times> nat) \<Rightarrow> ('i word \<times> nat) \<Rightarrow> ('i word \<times> nat) option" where 
    "ipcidr_conjunct (base1, m1) (base2, m2) = (if ipset_from_cidr base1 m1 \<inter> ipset_from_cidr base2 m2 = {}
       then
        None
       else if 
        ipset_from_cidr base1 m1 \<subseteq> ipset_from_cidr base2 m2
       then 
        Some (base1, m1)
       else
        Some (base2, m2)
      )"
  
  lemma ipcidr_conjunct_correct: "(case ipcidr_conjunct (b1, m1) (b2, m2)
                                          of Some (bx, mx) \<Rightarrow> ipset_from_cidr bx mx
                                          |  None \<Rightarrow> {})
      = 
      (ipset_from_cidr b1 m1) \<inter> (ipset_from_cidr b2 m2)"
    apply(simp split: split_if_asm)
    using ip_cidr_intersect by fast
  declare ipcidr_conjunct.simps[simp del]

  (*TODO: this is a duplicate, right?*)
  (*TODO: if not, move!*)
  definition ipcidr_tuple_to_wordinterval :: "('i::len word \<times> nat) \<Rightarrow> 'i wordinterval" where
    "ipcidr_tuple_to_wordinterval iprng = iprange_interval (ipcidr_to_interval iprng)"

  (*TODO: rename*)
  lemma wordinterval_to_set_ipcidr_tuple_to_wordinterval:
    "wordinterval_to_set (ipcidr_tuple_to_wordinterval (b, m)) = ipset_from_cidr b m"
    unfolding ipcidr_tuple_to_wordinterval_def ipset_from_cidr_ipcidr_to_interval ipcidr_to_interval_def
    by(simp add: iprange_interval.simps)

  lemma [code_unfold]: 
  "ipcidr_conjunct ips1 ips2 = (if wordinterval_empty (wordinterval_intersection (ipcidr_tuple_to_wordinterval ips1) (ipcidr_tuple_to_wordinterval ips2))
       then
        None
       else if 
        wordinterval_subset (ipcidr_tuple_to_wordinterval ips1) (ipcidr_tuple_to_wordinterval ips2)
       then 
        Some ips1
       else
        Some ips2
      )"
  apply(simp)
  apply(cases ips1, cases ips2, rename_tac b1 m1 b2 m2, simp)
  apply(safe)
     apply(auto simp add: wordinterval_to_set_ipcidr_tuple_to_wordinterval ipcidr_conjunct.simps split:split_if_asm)
  done
  value "ipcidr_conjunct (0,0) (8,1)" (*with the code_unfold lemma before, this works!*)

  
  (*TODO: generalize, move*)
  definition ipv4cidr_union_set :: "(ipv4addr \<times> nat) set \<Rightarrow> ipv4addr set" where
    "ipv4cidr_union_set ips \<equiv> \<Union>(base, len) \<in> ips. ipv4range_set_from_prefix base len"


  (*helper we use for spoofing protection specification*)
  definition all_but_those_ips :: "(ipv4addr \<times> nat) list \<Rightarrow> (ipv4addr \<times> nat) list" where
    "all_but_those_ips cidrips = cidr_split (ipv4range_invert (l2br (map ipcidr_to_interval cidrips)))"
  
  (*only ipv4*)
  lemma all_but_those_ips:
    "ipv4cidr_union_set (set (all_but_those_ips cidrips)) =
      UNIV - (\<Union> (ip,n) \<in> set cidrips. ipv4range_set_from_prefix ip n)"
    apply(simp add:)
    unfolding ipv4cidr_union_set_def all_but_those_ips_def
    apply(simp)
    apply(subst transition_lemma_ipv4_delete_me)+
    apply(simp add: cidr_split_prefix[simplified])
    apply(simp add: ipv4range_invert_def ipv4range_setminus_def)
    apply(simp add: ipv4range_UNIV_def)
    apply(simp add: l2br)
    apply(simp add: ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast
  



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
    "wi_2_cidr_ipt_ipv4range_list r = map (\<lambda> (base, len). Ip4AddrNetmask (dotdecimal_of_ipv4addr base) len) (cidr_split r)"

  lemma wi_2_cidr_ipt_ipv4range_list: "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = wordinterval_to_set r"
    proof -
    have "\<And>a. ipv4s_to_set (case a of (base, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr base) x) = (case a of (x, xa) \<Rightarrow> ipv4range_set_from_prefix x xa)"
      by(clarsimp simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
    hence "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = \<Union>((\<lambda>(x, y). ipv4range_set_from_prefix x y) ` set (cidr_split r))"
      unfolding wi_2_cidr_ipt_ipv4range_list_def by(simp)
    thus ?thesis
    apply(subst(asm) transition_lemma_ipv4_delete_me)
    using cidr_split_prefix by metis
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
    "ipt_ipv4range_to_cidr ips = cidr_split (ipv4range_range (ipt_ipv4range_to_interval ips))"

  lemma ipt_ipv4range_to_cidr: "ipv4cidr_union_set (set (ipt_ipv4range_to_cidr ips)) = (ipv4s_to_set ips)"
    apply(simp add: ipt_ipv4range_to_cidr_def)
    thm cidr_split_prefix_single 
    apply(simp add: ipv4cidr_union_set_def)
    apply(case_tac "(ipt_ipv4range_to_interval ips)")
    apply(simp add: ipt_ipv4range_to_interval)
    sorry
    by (smetis (no_types, hide_lams) SUP_def ipt_ipv4range_to_interval ipv4cidr_union_set_def ipv4range_range.cases cidr_split_prefix_single)
    



(*TODO probably MOVE: actually, these are toString pretty printing helpers*)
definition interval_to_wi_to_ipt_ipv4range :: "32 word \<Rightarrow> 32 word \<Rightarrow> ipt_ipv4range" where
  "interval_to_wi_to_ipt_ipv4range s e \<equiv>
    if s = e
    then Ip4Addr (dotdecimal_of_ipv4addr s)
    else case cidr_split (WordInterval s e) of [(ip,nmask)] \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) nmask
                                                  | _ \<Rightarrow> Ip4AddrRange (dotdecimal_of_ipv4addr s) (dotdecimal_of_ipv4addr e)"

lemma interval_to_wi_to_ipt_ipv4range: "ipv4s_to_set (interval_to_wi_to_ipt_ipv4range s e) = {s..e}"
  proof -
    from cidr_split_prefix_single[unfolded ipv4range_range.simps, of s e] have
      "cidr_split (WordInterval s e) = [(a, b)] \<Longrightarrow> ipv4range_set_from_prefix a b = {s..e}" for a b
      by(simp)
    thus ?thesis 
      by(simp add: interval_to_wi_to_ipt_ipv4range_def ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr split: list.split)
  qed

fun wi_to_ipt_ipv4range :: "32 wordinterval \<Rightarrow> ipt_ipv4range list" where
  "wi_to_ipt_ipv4range (WordInterval s e) = (if s > e then [] else 
      [interval_to_wi_to_ipt_ipv4range s e])" |
  "wi_to_ipt_ipv4range (RangeUnion a b) = wi_to_ipt_ipv4range a @ wi_to_ipt_ipv4range b"

lemma wi_to_ipt_ipv4range: "\<Union> set (map ipv4s_to_set (wi_to_ipt_ipv4range wi)) = wordinterval_to_set wi"
  apply(induction wi)
   apply(simp add: interval_to_wi_to_ipt_ipv4range)
  apply(simp)
  done
(*TODO end move*)

end
