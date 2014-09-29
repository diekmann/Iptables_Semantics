theory IPSpace_operations
imports Negation_Type "../Bitmagic/Numberwang_Ln" IPSpace_Syntax "../Bitmagic/IPv4Addr"
begin

definition intersect_netmask_empty :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "intersect_netmask_empty base1 m1 base2 m2 \<equiv> 
    ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base1) m1 \<inter> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base2) m2 = {}"

thm ipv4range_set_from_bitmask_alt
fun ipv4range_set_from_bitmask_to_executable_ipv4range :: "ipt_ipv4range \<Rightarrow> 32 bitrange" where
   "ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask pre len) = 
      ipv4range_range (((ipv4addr_of_dotteddecimal pre) AND ((mask len) << (32 - len))))  ((ipv4addr_of_dotteddecimal pre) OR (mask (32 - len)))" |
   "ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4Addr ip) = ipv4range_single (ipv4addr_of_dotteddecimal ip)"

export_code ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_intersection ipv4range_empty in SML

definition "intersect_netmask_empty_executable \<equiv> (\<lambda> base1 m1 base2 m2. ipv4range_empty (
        ipv4range_intersection 
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base1 m1))
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base2 m2))))"
export_code intersect_netmask_empty_executable in SML

lemma [code]: "intersect_netmask_empty = intersect_netmask_empty_executable"
apply (rule ext)+
unfolding intersect_netmask_empty_def intersect_netmask_empty_executable_def
apply(simp only: ipv4range_empty_set_eq ipv4range_intersection_set_eq )
apply(simp only: ipv4range_set_from_bitmask_to_executable_ipv4range.simps ipv4range_set_from_bitmask_alt ipv4range_range_set_eq)
done

export_code intersect_netmask_empty in SML


definition subset_netmask :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "subset_netmask base1 m1 base2 m2 \<equiv> 
    ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base1) m1 \<subseteq> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base2) m2"

definition subset_netmask_executable :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "subset_netmask_executable \<equiv> (\<lambda> base1 m1 base2 m2. ipv4range_subset
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base1 m1))
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base2 m2)))"

lemma [code]: "subset_netmask = subset_netmask_executable"
apply(simp only: fun_eq_iff, intro allI)
unfolding subset_netmask_def subset_netmask_executable_def
apply(simp only: ipv4range_subset_set_eq)
apply(simp only: ipv4range_set_from_bitmask_to_executable_ipv4range.simps ipv4range_set_from_bitmask_alt ipv4range_range_set_eq)
done

(* \<inter> pos \ \<union> neg*)
(*TODO option type!!! nur die positiven anschauen*)
(*None means empty, Some range otherwise*)
fun intersect_ips :: "ipt_ipv4range \<Rightarrow> ipt_ipv4range \<Rightarrow> ipt_ipv4range option" where
  "intersect_ips (Ip4Addr ip) (Ip4AddrNetmask base m) =
    (if (ipv4addr_of_dotteddecimal ip) \<in> (ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base) m) 
     then 
      Some (Ip4Addr ip)
     else
      None)" |
  "intersect_ips (Ip4AddrNetmask base m) (Ip4Addr ip) =
    (if (ipv4addr_of_dotteddecimal ip) \<in> (ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base) m) 
     then 
      Some (Ip4Addr ip)
     else
      None)" |
  "intersect_ips (Ip4Addr ip1) (Ip4Addr ip2) =
    (if ipv4addr_of_dotteddecimal ip2 = ipv4addr_of_dotteddecimal ip1 (*there might be overflows if someone uses values > 256*)
     then 
      Some (Ip4Addr ip1)
     else
      None)" |
  "intersect_ips (Ip4AddrNetmask base1 m1) (Ip4AddrNetmask base2 m2) = 
    (if (*ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base1) m1 \<inter> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base2) m2 = {}*)
        intersect_netmask_empty base1 m1 base2 m2
     then
      None
     else if (*m1 \<ge> m2*) (*maybe use execuatble subset check to make proofs easier?*)
      subset_netmask base1 m1 base2 m2
     then
      Some (Ip4AddrNetmask base1 m1) (*andersrum?*)
     else if subset_netmask base2 m2 base1 m1 then
      Some (Ip4AddrNetmask base2 m2)
     else
      None (*cannot happen, one must be subset of each other*))"

export_code intersect_ips in SML


lemma ipv4_setinterval_inter_not_empty: "{a::ipv4addr..b} \<inter> {c..d} \<noteq> {} \<longleftrightarrow>
    a \<le> b \<and> c \<le> d \<and>
    (a \<ge> c \<and> b \<le> d \<or>
    c \<le> b \<and> a \<le> c \<or>
    a \<le> d \<and> c \<le> a)"
apply(rule iffI)
apply force
apply(simp)
apply(clarify)
apply(elim disjE)
apply simp_all
apply fastforce+
done





lemma "\<not> ipv4range_set_from_bitmask b2 m2 \<subseteq> ipv4range_set_from_bitmask b1 m1 \<longrightarrow>
       \<not> ipv4range_set_from_bitmask b1 m1 \<subseteq> ipv4range_set_from_bitmask b2 m2 \<longrightarrow>
       ipv4range_set_from_bitmask b1 m1 \<inter> ipv4range_set_from_bitmask b2 m2 = {}"
  using ipv4range_bitmask_intersect by auto



lemma intersect_ips_None: "intersect_ips ip1 ip2 = None \<longleftrightarrow> (ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = {}"
  apply(induction ip1 ip2 rule: intersect_ips.induct)
  apply(simp_all add: intersect_netmask_empty_def)[3]
  apply(simp add: intersect_netmask_empty_def)
  by (metis subset_netmask_def ipv4range_bitmask_intersect)
 


lemma intersect_ips_Some: "intersect_ips ip1 ip2 = Some X \<Longrightarrow> (ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = ipv4s_to_set X"
  apply(induction ip1 ip2 rule: intersect_ips.induct)
  apply(simp_all)
  apply(safe)[3]
  apply(simp_all)
  apply(case_tac [!] X)[9]
  apply(simp_all)
  apply(simp_all split: split_if_asm)[12]


  apply(simp split: split_if_asm)
  apply(simp_all add: intersect_netmask_empty_def subset_netmask_def)
  apply(case_tac [!] X)
  apply(simp_all)
  apply blast

  apply(blast)
  
done


text{*The other direction does not directly hold. Someone might enter some invalid ips.*}

(*This proof looks like cheating because always @{term "ipv4s_to_set X \<noteq> {}"}"*)
lemma intersect_ips_Some2: "(ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = ipv4s_to_set X \<Longrightarrow> \<exists>Y. intersect_ips ip1 ip2 = Some Y \<and> ipv4s_to_set X = ipv4s_to_set Y"
  apply(subgoal_tac "(ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) \<noteq> {}")
   prefer 2
   apply(simp add: ipv4s_to_set_nonempty)
  apply(simp add: intersect_ips_None)
  apply(subgoal_tac "intersect_ips ip1 ip2 \<noteq> None")
   prefer 2
   apply(simp add: intersect_ips_None)
  apply(simp)
  apply(erule exE)
  apply(rule_tac x=y in exI)
  apply(simp)
by (metis intersect_ips_Some)


fun compress_pos_ips :: "ipt_ipv4range list \<Rightarrow> ipt_ipv4range option" where
  "compress_pos_ips [] = Some (Ip4AddrNetmask (0,0,0,0) 0)" | (*hmm, looks correct but bloating*)
  "compress_pos_ips [ip] = Some ip" |
  "compress_pos_ips (a#b#cs) = (
    case intersect_ips a b of None \<Rightarrow> None
    | Some x \<Rightarrow> compress_pos_ips (x#cs)
    )"


  
lemma compress_pos_ips_None: "compress_pos_ips ips = None \<longleftrightarrow> \<Inter> (ipv4s_to_set ` set ips) = {}"
  apply(induction ips rule: compress_pos_ips.induct)
    apply(simp)
   apply(simp add: ipv4s_to_set_nonempty)
  apply(simp)
  apply(simp split: option.split)
  apply(simp add: intersect_ips_None)
by (metis (hide_lams, no_types) inf_assoc inf_bot_left intersect_ips_Some)


lemma compress_pos_ips_Some: "compress_pos_ips ips = Some X \<Longrightarrow> \<Inter> (ipv4s_to_set ` set ips) = ipv4s_to_set X"
  apply(induction ips rule: compress_pos_ips.induct)
    apply(simp)
    apply(auto simp add: ipv4range_set_from_bitmask_0)[1]
   apply(simp)
  apply(simp)
  apply(simp split: option.split_asm)
by (metis Int_assoc intersect_ips_Some)


fun collect_to_range :: "ipt_ipv4range list \<Rightarrow> 32 bitrange" where
 "collect_to_range [] = Empty_Bitrange" |
 "collect_to_range (r#rs) = RangeUnion (ipv4range_set_from_bitmask_to_executable_ipv4range r) (collect_to_range rs)"






fun compress_ips :: "ipt_ipv4range negation_type list \<Rightarrow> ipt_ipv4range negation_type list option" where
  "compress_ips l = (if (getPos l) = [] then Some l (*fix not to introduce (Ip4AddrNetmask (0,0,0,0) 0), only return the negative list*)
  else
  (case compress_pos_ips (getPos l)
    of None \<Rightarrow> None
    | Some ip \<Rightarrow> 
      if ipv4range_empty (ipv4range_setminus (ipv4range_set_from_bitmask_to_executable_ipv4range ip) (collect_to_range (getNeg l)))
      (* \<Inter> pos - \<Union> neg = {}*)
      then
        None
      else Some (Pos ip # map Neg (getNeg l))
      ))"

export_code compress_ips in SML

(*TODO move*)
lemma ipv4range_set_from_bitmask_to_executable_ipv4range: 
  "ipv4range_to_set (ipv4range_set_from_bitmask_to_executable_ipv4range a) = ipv4s_to_set a"
apply(case_tac a)
 apply(simp_all add:ipv4range_single_set_eq ipv4range_range_set_eq)
 apply(simp add: ipv4range_set_from_bitmask_alt)
done

lemma ipv4range_to_set_collect_to_range: "ipv4range_to_set (collect_to_range ips) = (\<Union>x\<in>set ips. ipv4s_to_set x)"
  apply(induction ips)
   apply(simp add: ipv4range_to_set_def)
  apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_def)
  by (metis ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_def)


lemma compress_ips_None: "getPos ips \<noteq> [] \<Longrightarrow> compress_ips ips = None \<longleftrightarrow> (\<Inter> (ipv4s_to_set ` set (getPos ips))) - (\<Union> (ipv4s_to_set ` set (getNeg ips))) = {}"
  apply(simp only: compress_ips.simps split: split_if)
  apply(intro conjI impI)
   apply(simp)
   (*getPos on empty should be the UNIV*)
  apply(simp split: option.split)
  apply(intro conjI impI allI)
  apply(simp add: compress_pos_ips_None)
  apply(rename_tac a)
  apply(frule compress_pos_ips_Some)
   apply(case_tac a)
    apply(simp add: ipv4range_to_set_collect_to_range ipv4range_single_set_eq)
   apply(simp add: ipv4range_set_from_bitmask_alt)
   apply(simp add: ipv4range_to_set_collect_to_range)
  apply(frule compress_pos_ips_Some)
  apply(rename_tac a)
  apply(case_tac a)
   apply(simp add: ipv4range_to_set_collect_to_range ipv4range_range_set_eq)
  apply(simp add: ipv4range_set_from_bitmask_alt ipv4range_range_set_eq)
  apply(simp add: ipv4range_to_set_collect_to_range)
by (metis INF_def compress_pos_ips_Some ipv4range_set_from_bitmask_to_executable_ipv4range)

  

lemma compress_ips_emptyPos: "getPos ips = [] \<Longrightarrow> compress_ips ips = Some ips \<and> ips = map Neg (getNeg ips)"
  apply(simp only: compress_ips.simps split: split_if)
  apply(intro conjI impI)
   apply(simp_all)
  apply(induction ips)
  apply(simp_all)
  apply(case_tac a)
  apply(simp_all)
done




end
