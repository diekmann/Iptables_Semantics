theory IPSpace_Operations
imports Negation_Type "../Bitmagic/Numberwang_Ln" "../Primitive_Matchers/IPSpace_Syntax" "../Bitmagic/IPv4Addr"
begin

definition intersect_netmask_empty :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "intersect_netmask_empty base1 m1 base2 m2 \<equiv> 
    ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base1) m1 \<inter> ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base2) m2 = {}"

fun ipv4range_set_from_bitmask_to_executable_ipv4range :: "ipt_ipv4range \<Rightarrow> 32 bitrange" where
   "ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask pre len) = 
      ipv4range_range (((ipv4addr_of_dotteddecimal pre) AND ((mask len) << (32 - len))))  ((ipv4addr_of_dotteddecimal pre) OR (mask (32 - len)))" |
   "ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4Addr ip) = ipv4range_single (ipv4addr_of_dotteddecimal ip)"


lemma ipv4range_set_from_bitmask_to_executable_ipv4range_simps: 
      "ipv4range_to_set (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base m)) = 
       ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal base) m"
      "ipv4range_to_set (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4Addr ip)) = {ipv4addr_of_dotteddecimal ip}"
  unfolding ipv4range_set_from_bitmask_to_executable_ipv4range.simps
  apply(simp_all add: ipv4range_set_from_bitmask_alt ipv4range_range_set_eq ipv4range_single_set_eq)
  done

declare ipv4range_set_from_bitmask_to_executable_ipv4range.simps[simp del]

definition "intersect_netmask_empty_executable \<equiv> (\<lambda> base1 m1 base2 m2. ipv4range_empty (
        ipv4range_intersection 
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base1 m1))
          (ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4AddrNetmask base2 m2))))"

lemma [code]: "intersect_netmask_empty = intersect_netmask_empty_executable"
apply (rule ext)+
unfolding intersect_netmask_empty_def intersect_netmask_empty_executable_def
apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range_simps)
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
apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range_simps)
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


lemma "\<not> ipv4range_set_from_bitmask b2 m2 \<subseteq> ipv4range_set_from_bitmask b1 m1 \<longrightarrow>
       \<not> ipv4range_set_from_bitmask b1 m1 \<subseteq> ipv4range_set_from_bitmask b2 m2 \<longrightarrow>
       ipv4range_set_from_bitmask b1 m1 \<inter> ipv4range_set_from_bitmask b2 m2 = {}"
  using ipv4range_bitmask_intersect by auto



lemma intersect_ips_None: "intersect_ips ip1 ip2 = None \<longleftrightarrow> (ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = {}"
  apply(induction ip1 ip2 rule: intersect_ips.induct)
     apply(simp_all add: intersect_netmask_empty_def subset_netmask_def ipv4range_bitmask_intersect)
  done
 


lemma intersect_ips_Some: "intersect_ips ip1 ip2 = Some X \<Longrightarrow> (ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = ipv4s_to_set X"
  apply(induction ip1 ip2 rule: intersect_ips.induct)
     apply(case_tac [!] X)
     apply(auto simp add: ipv4range_set_from_bitmask_to_executable_ipv4range_simps intersect_netmask_empty_def subset_netmask_def split: split_if_asm)
done


text{*The other direction does not directly hold. Someone might enter some invalid ips.*}

(*This proof looks like cheating because always @{term "ipv4s_to_set X \<noteq> {}"}"*)
lemma intersect_ips_Some2: "(ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = ipv4s_to_set X \<Longrightarrow> \<exists>Y. intersect_ips ip1 ip2 = Some Y \<and> ipv4s_to_set X = ipv4s_to_set Y"
  proof -
    assume a: "(ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) = ipv4s_to_set X"
    hence "(ipv4s_to_set ip1) \<inter> (ipv4s_to_set ip2) \<noteq> {}" by(simp add: ipv4s_to_set_nonempty)
    with a have "ipv4s_to_set X \<noteq> {}" by(simp add: intersect_ips_None)
    with a have "intersect_ips ip1 ip2 \<noteq> None" by(simp add: intersect_ips_None)
    from this obtain Y where "intersect_ips ip1 ip2 = Some Y" by blast
    with a intersect_ips_Some have "intersect_ips ip1 ip2 = Some Y \<and> ipv4s_to_set X = ipv4s_to_set Y" by simp
    thus ?thesis by blast
  qed


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
  using intersect_ips_Some by blast


lemma compress_pos_ips_Some: "compress_pos_ips ips = Some X \<Longrightarrow> \<Inter> (ipv4s_to_set ` set ips) = ipv4s_to_set X"
  apply(induction ips rule: compress_pos_ips.induct)
    apply(simp)
    apply(auto simp add: ipv4range_set_from_bitmask_0)[1]
   apply(simp)
  apply(simp)
  apply(simp split: option.split_asm)
by (metis Int_assoc intersect_ips_Some)



(*SCRATCH: *)
(*TODO TODO: refactor whole mess above to this simple proof? *)

(*from IPSpace_Operations.intersect_ips*)
  fun simple_ips_conjunct :: "(ipv4addr \<times> nat) \<Rightarrow> (ipv4addr \<times> nat) \<Rightarrow> (ipv4addr \<times> nat) option" where 
    "simple_ips_conjunct (base1, m1) (base2, m2) = (if ipv4range_set_from_bitmask base1 m1 \<inter> ipv4range_set_from_bitmask base2 m2 = {}
       then
        None
       else if 
        ipv4range_set_from_bitmask base1 m1 \<subseteq> ipv4range_set_from_bitmask base2 m2
       then 
        Some (base1, m1)
       else
        Some (base2, m2)
      )"
  
  (*this proof appears simpler than the other one, maybe refactor?*)
  lemma simple_ips_conjunct_correct: "(case simple_ips_conjunct (b1, m1) (b2, m2) of Some (bx, mx) \<Rightarrow> ipv4range_set_from_bitmask bx mx | None \<Rightarrow> {}) = 
      (ipv4range_set_from_bitmask b1 m1) \<inter> (ipv4range_set_from_bitmask b2 m2)"
    apply(simp split: split_if_asm)
    using ipv4range_bitmask_intersect apply fast+
    done
  declare simple_ips_conjunct.simps[simp del]
  

(*End Scratch*)

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
 apply(auto simp add:ipv4range_set_from_bitmask_to_executable_ipv4range_simps)
done

lemma ipv4range_to_set_collect_to_range: "ipv4range_to_set (collect_to_range ips) = (\<Union>x\<in>set ips. ipv4s_to_set x)"
  apply(induction ips)
   apply(simp add: ipv4range_to_set_def)
  apply(simp add: ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_def)
  by (metis ipv4range_set_from_bitmask_to_executable_ipv4range ipv4range_to_set_def)


lemma compress_ips_None: "getPos ips \<noteq> [] \<Longrightarrow> compress_ips ips = None \<longleftrightarrow> (\<Inter> (ipv4s_to_set ` set (getPos ips))) - (\<Union> (ipv4s_to_set ` set (getNeg ips))) = {}"
  apply(simp split: split_if)
  apply(simp)
   (*getPos on empty should be the UNIV*)
  apply(simp split: option.split)
  apply(intro conjI impI allI)
    apply(simp add: compress_pos_ips_None)
   apply(rename_tac a)
   apply(frule compress_pos_ips_Some)
   apply(case_tac a)
    (* why won't it apply  ipv4range_set_from_bitmask_to_executable_ipv4range_simps in the simplifier?*)
    apply(auto simp add: ipv4range_set_from_bitmask_to_executable_ipv4range_simps)[1]
    apply(simp add: ipv4range_to_set_collect_to_range ipv4range_set_from_bitmask_to_executable_ipv4range_simps)
   apply(auto simp add: ipv4range_to_set_collect_to_range ipv4range_set_from_bitmask_to_executable_ipv4range_simps)[1]
  apply(rename_tac a)
  apply(frule compress_pos_ips_Some)
  apply(case_tac a)
   apply(auto simp add: ipv4range_to_set_collect_to_range ipv4range_set_from_bitmask_to_executable_ipv4range_simps)
done


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
