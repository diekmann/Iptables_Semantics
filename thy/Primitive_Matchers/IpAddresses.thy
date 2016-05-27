theory IpAddresses
imports "../Bitmagic/IPv4Addr"
  "../Bitmagic/IPv6Addr"
  "../Bitmagic/CIDRSplit"
  "../Bitmagic/WordInterval_Lists"
begin




section\<open>IPv4 Addresses\<close>

--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4set_from_cidr (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 33 = {0}"
  by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipv4set_from_cidr_def ipset_from_cidr_large_pfxlen)
  

  (*TODO: remove this lemma?, refactor*)
  lemma ipv4cidr_to_interval: "ipcidr_to_interval (base, len) = (s,e) \<Longrightarrow> ipv4set_from_cidr base len = {s .. e}"
    apply(simp add: ipv4set_from_cidr_def Let_def ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast


  (*helper we use for spoofing protection specification*)
  definition all_but_those_ips :: "('i::len word \<times> nat) list \<Rightarrow> ('i word \<times> nat) list" where
    "all_but_those_ips cidrips = cidr_split (wordinterval_invert (l2br (map ipcidr_to_interval cidrips)))"
  
  lemma all_but_those_ips:
    "ipcidr_union_set (set (all_but_those_ips cidrips)) =
      UNIV - (\<Union> (ip,n) \<in> set cidrips. ipv4set_from_cidr ip n)"
    apply(simp add: )
    unfolding ipcidr_union_set_def all_but_those_ips_def
    apply(simp add: ipv4set_from_cidr_def cidr_split_prefix[simplified])
    apply(simp add: l2br)
    apply(simp add: ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast
  



subsection\<open>IPv4 Addresses in IPTables Notation (how we parse it)\<close>
  (*src dst ipv4*)
  datatype ipt_ipv4range =
                        -- "Singleton IP Address"
                        Ip4Addr "nat \<times> nat \<times> nat \<times> nat"

                        -- "CIDR notation: addr/xx"
                        | Ip4AddrNetmask "nat \<times> nat \<times> nat \<times> nat" nat

                        -- "-m iprange --src-range a.b.c.d-e.f.g.h"
                        | Ip4AddrRange  "nat \<times> nat \<times> nat \<times> nat" "nat \<times> nat \<times> nat \<times> nat"
                            (*the range is inclusive*)
  
  
  fun ipv4s_to_set :: "ipt_ipv4range \<Rightarrow> ipv4addr set" where
    "ipv4s_to_set (Ip4AddrNetmask base m) = ipv4set_from_cidr (ipv4addr_of_dotdecimal base) m" |
    "ipv4s_to_set (Ip4Addr ip) = { ipv4addr_of_dotdecimal ip }" |
    "ipv4s_to_set (Ip4AddrRange ip1 ip2) = { ipv4addr_of_dotdecimal ip1 .. ipv4addr_of_dotdecimal ip2 }"
  
  text\<open>@{term ipv4s_to_set} can only represent an empty set if it is an empty range.\<close>
  lemma ipv4s_to_set_nonempty: "ipv4s_to_set ip = {} \<longleftrightarrow> (\<exists>ip1 ip2. ip = Ip4AddrRange ip1 ip2 \<and> ipv4addr_of_dotdecimal ip1 > ipv4addr_of_dotdecimal ip2)"
    apply(cases ip)
      apply(simp; fail)
     apply(simp add: ipv4set_from_cidr_def ipset_from_cidr_alt bitmagic_zeroLast_leq_or1Last; fail)
    apply(simp add:linorder_not_le; fail)
    done
  
  text\<open>maybe this is necessary as code equation?\<close>
  lemma element_ipv4s_to_set[code_unfold]: "addr \<in> ipv4s_to_set X = (
    case X of (Ip4AddrNetmask pre len) \<Rightarrow> ((ipv4addr_of_dotdecimal pre) AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> (ipv4addr_of_dotdecimal pre) OR (mask (32 - len))
    | Ip4Addr ip \<Rightarrow> (addr = (ipv4addr_of_dotdecimal ip))
    | Ip4AddrRange ip1 ip2 \<Rightarrow> ipv4addr_of_dotdecimal ip1 \<le> addr \<and> ipv4addr_of_dotdecimal ip2 \<ge> addr)"
  apply(cases X)
    apply(simp; fail)
   apply(simp add: ipv4set_from_cidr_def ipset_from_cidr_alt; fail)
  apply(simp; fail)
  done
  

  text\<open>IPv4 address ranges to @{text "(start, end)"} notation\<close>
  fun ipt_ipv4range_to_interval :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> ipv4addr)" where
    "ipt_ipv4range_to_interval (Ip4Addr addr) = (ipv4addr_of_dotdecimal addr, ipv4addr_of_dotdecimal addr)" |
    "ipt_ipv4range_to_interval (Ip4AddrNetmask pre len) = ipcidr_to_interval ((ipv4addr_of_dotdecimal pre), len)" |
    "ipt_ipv4range_to_interval (Ip4AddrRange ip1 ip2) = (ipv4addr_of_dotdecimal ip1, ipv4addr_of_dotdecimal ip2)"
  
  lemma ipt_ipv4range_to_interval: "ipt_ipv4range_to_interval ip = (s,e) \<Longrightarrow> {s .. e} = ipv4s_to_set ip"
    by(cases ip) (auto simp add: ipv4cidr_to_interval)


  text\<open>A list of IPv4 address ranges to a @{typ "32 wordinterval"}.
        The nice thing is: the usual set operations are defined on this type.
        We can use the existing function @{const l2br_intersect} if we want the intersection of the supplied list\<close>
  lemma "wordinterval_to_set (l2br_intersect (map ipt_ipv4range_to_interval ips)) = (\<Inter> ip \<in> set ips. ipv4s_to_set ip)"
    apply(simp add: l2br_intersect)
    using ipt_ipv4range_to_interval by blast
  
  text\<open>We can use @{const l2br} if we want the union of the supplied list\<close>
  lemma "wordinterval_to_set (l2br (map ipt_ipv4range_to_interval ips)) = (\<Union> ip \<in> set ips. ipv4s_to_set ip)"
    apply(simp add: l2br)
    using ipt_ipv4range_to_interval by blast

  text\<open>A list of (negated) IPv4 address to a @{typ "32 wordinterval"}.\<close>
  definition ipt_ipv4range_negation_type_to_br_intersect :: "ipt_ipv4range negation_type list \<Rightarrow> 32 wordinterval" where
    "ipt_ipv4range_negation_type_to_br_intersect l = l2br_negation_type_intersect (NegPos_map ipt_ipv4range_to_interval l)" 

  lemma ipt_ipv4range_negation_type_to_br_intersect: "wordinterval_to_set (ipt_ipv4range_negation_type_to_br_intersect l) =
      (\<Inter> ip \<in> set (getPos l). ipv4s_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipv4s_to_set ip)"
    apply(simp add: ipt_ipv4range_negation_type_to_br_intersect_def l2br_negation_type_intersect NegPos_map_simps)
    using ipt_ipv4range_to_interval by blast

  text\<open>The @{typ "32 wordinterval"} can be translated back into a list of IP ranges.
        If a list of intervals is enough, we can use @{const br2l}.
        If we need it in @{typ ipt_ipv4range}, we can use this function.\<close>
  definition wi_2_cidr_ipt_ipv4range_list :: "32 wordinterval \<Rightarrow> ipt_ipv4range list" where
    "wi_2_cidr_ipt_ipv4range_list r = map (\<lambda> (base, len). Ip4AddrNetmask (dotdecimal_of_ipv4addr base) len) (cidr_split r)"

  lemma wi_2_cidr_ipt_ipv4range_list: "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = wordinterval_to_set r"
    proof -
    have "\<And>a. ipv4s_to_set (case a of (base, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr base) x) = (case a of (x, xa) \<Rightarrow> ipv4set_from_cidr x xa)"
      by(clarsimp simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)
    hence "(\<Union> ip \<in> set (wi_2_cidr_ipt_ipv4range_list r). ipv4s_to_set ip) = \<Union>((\<lambda>(x, y). ipv4set_from_cidr x y) ` set (cidr_split r))"
      unfolding wi_2_cidr_ipt_ipv4range_list_def by(simp)
    thus ?thesis
    unfolding ipv4set_from_cidr_def
    using cidr_split_prefix by metis
  qed

  text\<open>For example, this allows the following transformation\<close>
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

  lemma ipt_ipv4range_to_cidr: "ipcidr_union_set (set (ipt_ipv4range_to_cidr ips)) = (ipv4s_to_set ips)"
    apply(simp add: ipt_ipv4range_to_cidr_def)
    thm cidr_split_prefix_single
    apply(simp add: ipcidr_union_set_def)
    apply(case_tac "(ipt_ipv4range_to_interval ips)")
    apply(simp add: ipt_ipv4range_to_interval)
    apply(subst ipv4range_range_transition_todo_delete_me)
    apply(simp)
    using ipt_ipv4range_to_interval cidr_split_prefix_single by blast
    



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
      "cidr_split (WordInterval s e) = [(a, b)] \<Longrightarrow> ipv4set_from_cidr a b = {s..e}" for a b
        by(simp add: ipv4set_from_cidr_def iprange_interval.simps)
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
