theory Numberwang_Ln
imports PrefixMatch IPAddr
begin

(*TODO: move to IpAddresses or somewhere*)
lemma ip_cidr_intersect: " \<not> ipset_from_cidr b2 m2 \<subseteq> ipset_from_cidr b1 m1 \<Longrightarrow>
       \<not> ipset_from_cidr b1 m1 \<subseteq> ipset_from_cidr b2 m2 \<Longrightarrow>
       ipset_from_cidr b1 m1 \<inter> ipset_from_cidr b2 m2 = {}"
apply(simp add: ipv4set_from_cidr_eq_ip_cidr_set)
using ip_cidr_set_notsubset_empty_inter by blast



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

lemma ipcidr_conjunct_any: "ipcidr_conjunct (0, 0) (0, 0) \<noteq> None"
  by(simp add: ipset_from_cidr_0)

lemma ipcidr_conjunct_correct: "(case ipcidr_conjunct (b1, m1) (b2, m2)
                                        of Some (bx, mx) \<Rightarrow> ipset_from_cidr bx mx
                                        |  None \<Rightarrow> {})
    = (ipset_from_cidr b1 m1) \<inter> (ipset_from_cidr b2 m2)"
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
  (*with the code_unfold lemma before, this works!*)
  lemma "ipcidr_conjunct (0::32 word,0) (8,1) = Some (8, 1)" by eval




end
