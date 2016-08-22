theory IpAddresses
imports "../../IP_Addresses/IP_Address_toString"
  "../../IP_Addresses/CIDR_Split"
  "../Common/WordInterval_Lists"
begin




--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipset_from_cidr (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 33 = {0}"
  by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipset_from_cidr_large_pfxlen)
  

  (*helper we use for spoofing protection specification*)
  definition all_but_those_ips :: "('i::len word \<times> nat) list \<Rightarrow> ('i word \<times> nat) list" where
    "all_but_those_ips cidrips = cidr_split (wordinterval_invert (l2wi (map ipcidr_to_interval cidrips)))"
  
  lemma all_but_those_ips:
    "ipcidr_union_set (set (all_but_those_ips cidrips)) =
      UNIV - (\<Union> (ip,n) \<in> set cidrips. ipset_from_cidr ip n)"
    apply(simp add: )
    unfolding ipcidr_union_set_uncurry all_but_those_ips_def
    apply(simp add: cidr_split_prefix)
    apply(simp add: l2wi)
    apply(simp add: ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast
  

section\<open>IPv4 Addresses\<close>



subsection\<open>IPv4 Addresses in IPTables Notation (how we parse it)\<close>
  context
    notes [[typedef_overloaded]]
  begin
    datatype 'i ipt_iprange =
                          -- "Singleton IP Address"
                          IpAddr "'i::len word"
  
                          -- "CIDR notation: addr/xx"
                          | IpAddrNetmask "'i word" nat
  
                          -- "-m iprange --src-range a.b.c.d-e.f.g.h"
                          | IpAddrRange  "'i word" "'i word"
                              (*the range is inclusive*)
  end  
  
  fun ipt_iprange_to_set :: "'i::len ipt_iprange \<Rightarrow> 'i word set" where
    "ipt_iprange_to_set (IpAddrNetmask base m) = ipset_from_cidr base m" |
    "ipt_iprange_to_set (IpAddr ip) = { ip }" |
    "ipt_iprange_to_set (IpAddrRange ip1 ip2) = { ip1 .. ip2 }"
  
  text\<open>@{term ipt_iprange_to_set} can only represent an empty set if it is an empty range.\<close>
  lemma ipt_iprange_to_set_nonempty: "ipt_iprange_to_set ip = {} \<longleftrightarrow> 
    (\<exists>ip1 ip2. ip = IpAddrRange ip1 ip2 \<and> ip1 > ip2)"
    apply(cases ip)
      apply(simp; fail)
     apply(simp add: ipset_from_cidr_alt bitmagic_zeroLast_leq_or1Last; fail)
    apply(simp add:linorder_not_le; fail)
    done
  
  text\<open>maybe this is necessary as code equation?\<close>
  lemma element_ipt_iprange_to_set[code_unfold]: "(addr::'i::len word) \<in> ipt_iprange_to_set X = (
    case X of (IpAddrNetmask pre len) \<Rightarrow>
                  (pre AND ((mask len) << (len_of (TYPE('i)) - len))) \<le> addr \<and>
                  addr \<le> pre OR (mask (len_of (TYPE('i)) - len))
    | IpAddr ip \<Rightarrow> (addr = ip)
    | IpAddrRange ip1 ip2 \<Rightarrow> ip1 \<le> addr \<and> ip2 \<ge> addr)"
  apply(cases X)
    apply(simp; fail)
   apply(simp add: ipset_from_cidr_alt; fail)
  apply(simp; fail)
  done

  
  lemma ipt_iprange_to_set_uncurry_IpAddrNetmask:
    "ipt_iprange_to_set (uncurry IpAddrNetmask a) = uncurry ipset_from_cidr a"
    by(simp split: uncurry_splits)
  

  text\<open>IP address ranges to @{text "(start, end)"} notation\<close>
  fun ipt_iprange_to_interval :: "'i::len ipt_iprange \<Rightarrow> ('i word \<times> 'i word)" where
    "ipt_iprange_to_interval (IpAddr addr) = (addr, addr)" |
    "ipt_iprange_to_interval (IpAddrNetmask pre len) = ipcidr_to_interval (pre, len)" |
    "ipt_iprange_to_interval (IpAddrRange ip1 ip2) = (ip1, ip2)"
  
  lemma ipt_iprange_to_interval: "ipt_iprange_to_interval ip = (s,e) \<Longrightarrow> {s .. e} = ipt_iprange_to_set ip"
    apply(cases ip)
      apply(auto simp add: ipcidr_to_interval)
    done


  text\<open>A list of IP address ranges to a @{typ "'i::len wordinterval"}.
        The nice thing is: the usual set operations are defined on this type.
        We can use the existing function @{const l2wi_intersect} if we want the intersection of the supplied list\<close>
  lemma "wordinterval_to_set (l2wi_intersect (map ipt_iprange_to_interval ips)) =
            (\<Inter> ip \<in> set ips. ipt_iprange_to_set ip)"
    apply(simp add: l2wi_intersect)
    using ipt_iprange_to_interval by blast
  
  text\<open>We can use @{const l2wi} if we want the union of the supplied list\<close>
  lemma "wordinterval_to_set (l2wi (map ipt_iprange_to_interval ips)) = (\<Union> ip \<in> set ips. ipt_iprange_to_set ip)"
    apply(simp add: l2wi)
    using ipt_iprange_to_interval by blast

  text\<open>A list of (negated) IP address to a @{typ "'i::len wordinterval"}.\<close>
  definition ipt_iprange_negation_type_to_br_intersect ::
    "'i::len ipt_iprange negation_type list \<Rightarrow> 'i wordinterval" where
    "ipt_iprange_negation_type_to_br_intersect l = l2wi_negation_type_intersect (NegPos_map ipt_iprange_to_interval l)" 

  lemma ipt_iprange_negation_type_to_br_intersect: "wordinterval_to_set (ipt_iprange_negation_type_to_br_intersect l) =
      (\<Inter> ip \<in> set (getPos l). ipt_iprange_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipt_iprange_to_set ip)"
    apply(simp add: ipt_iprange_negation_type_to_br_intersect_def l2wi_negation_type_intersect NegPos_map_simps)
    using ipt_iprange_to_interval by blast

  text\<open>The @{typ "'i::len wordinterval"} can be translated back into a list of IP ranges.
        If a list of intervals is enough, we can use @{const wi2l}.
        If we need it in @{typ "'i::len ipt_iprange"}, we can use this function.\<close>
  definition wi_2_cidr_ipt_iprange_list :: "'i::len wordinterval \<Rightarrow> 'i ipt_iprange list" where
    "wi_2_cidr_ipt_iprange_list r = map (uncurry IpAddrNetmask) (cidr_split r)"

  lemma wi_2_cidr_ipt_iprange_list:
    "(\<Union> ip \<in> set (wi_2_cidr_ipt_iprange_list r). ipt_iprange_to_set ip) = wordinterval_to_set r"
    proof -
    have "(\<Union> ip \<in> set (wi_2_cidr_ipt_iprange_list r). ipt_iprange_to_set ip) =
           (\<Union>x\<in>set (cidr_split r). uncurry ipset_from_cidr x)"
      unfolding wi_2_cidr_ipt_iprange_list_def by force
    thus ?thesis using cidr_split_prefix by metis
  qed

  text\<open>For example, this allows the following transformation\<close>
  definition ipt_iprange_compress :: "'i::len ipt_iprange negation_type list \<Rightarrow> 'i ipt_iprange list" where
    "ipt_iprange_compress = wi_2_cidr_ipt_iprange_list \<circ> ipt_iprange_negation_type_to_br_intersect"

  lemma ipt_iprange_compress: "(\<Union> ip \<in> set (ipt_iprange_compress l). ipt_iprange_to_set ip) =
      (\<Inter> ip \<in> set (getPos l). ipt_iprange_to_set ip) - (\<Union> ip \<in> set (getNeg l). ipt_iprange_to_set ip)"
    by (metis wi_2_cidr_ipt_iprange_list comp_apply ipt_iprange_compress_def ipt_iprange_negation_type_to_br_intersect)
  
  definition normalized_cidr_ip :: "'i::len ipt_iprange \<Rightarrow> bool" where
    "normalized_cidr_ip ip \<equiv> case ip of IpAddrNetmask _ _ \<Rightarrow> True | _ \<Rightarrow> False"

  lemma wi_2_cidr_ipt_iprange_list_normalized_IpAddrNetmask: 
    "\<forall>a'\<in>set (wi_2_cidr_ipt_iprange_list as). normalized_cidr_ip a'"
    apply(clarify)
    apply(simp add: wi_2_cidr_ipt_iprange_list_def normalized_cidr_ip_def)
    by force

  lemma ipt_iprange_compress_normalized_IpAddrNetmask:
    "\<forall>a'\<in>set (ipt_iprange_compress as). normalized_cidr_ip a'"
    by(simp add: ipt_iprange_compress_def wi_2_cidr_ipt_iprange_list_normalized_IpAddrNetmask)


  
  definition ipt_iprange_to_cidr :: "'i::len ipt_iprange \<Rightarrow> ('i word \<times> nat) list" where
    "ipt_iprange_to_cidr ips = cidr_split (iprange_interval (ipt_iprange_to_interval ips))"

  lemma ipt_ipvange_to_cidr: "ipcidr_union_set (set (ipt_iprange_to_cidr ips)) = (ipt_iprange_to_set ips)"
    apply(simp add: ipt_iprange_to_cidr_def)
    apply(simp add: ipcidr_union_set_uncurry)
    apply(case_tac "(ipt_iprange_to_interval ips)")
    apply(simp add: ipt_iprange_to_interval cidr_split_prefix_single)
    done
    



(* actually, these are toString pretty printing helpers*)
definition interval_to_wi_to_ipt_iprange :: "'i::len word \<Rightarrow> 'i word \<Rightarrow> 'i ipt_iprange" where
  "interval_to_wi_to_ipt_iprange s e \<equiv>
    if s = e
    then IpAddr s
    else case cidr_split (WordInterval s e) of [(ip,nmask)] \<Rightarrow> IpAddrNetmask ip nmask
                                            |   _ \<Rightarrow> IpAddrRange s e"

lemma interval_to_wi_to_ipt_ipv4range: "ipt_iprange_to_set (interval_to_wi_to_ipt_iprange s e) = {s..e}"
  proof -
    from cidr_split_prefix_single[of s e] have
      "cidr_split (WordInterval s e) = [(a, b)] \<Longrightarrow> ipset_from_cidr a b = {s..e}" for a b
        by(simp add: iprange_interval.simps)
    thus ?thesis 
      by(simp add: interval_to_wi_to_ipt_iprange_def split: list.split)
  qed

fun wi_to_ipt_iprange :: "'i::len wordinterval \<Rightarrow> 'i ipt_iprange list" where
  "wi_to_ipt_iprange (WordInterval s e) = (if s > e then [] else 
      [interval_to_wi_to_ipt_iprange s e])" |
  "wi_to_ipt_iprange (RangeUnion a b) = wi_to_ipt_iprange a @ wi_to_ipt_iprange b"

lemma wi_to_ipt_ipv4range: "\<Union> set (map ipt_iprange_to_set (wi_to_ipt_iprange wi)) = wordinterval_to_set wi"
  apply(induction wi)
   apply(simp add: interval_to_wi_to_ipt_ipv4range)
  apply(simp)
  done

end
