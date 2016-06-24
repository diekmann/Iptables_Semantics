theory WordInterval_Lists
imports WordInterval
  "../Iptables_Semantics/Common/Negation_Type"
begin


  fun l2br_negation_type_union :: "('a::len word \<times> 'a::len word) negation_type list \<Rightarrow> 'a::len wordinterval" where
    "l2br_negation_type_union [] = Empty_WordInterval" |
    "l2br_negation_type_union ((Pos (s,e))#ls) = wordinterval_union (WordInterval s e) (l2br_negation_type_union ls)" |
    "l2br_negation_type_union ((Neg (s,e))#ls) = wordinterval_union (wordinterval_invert (WordInterval s e)) (l2br_negation_type_union ls)"


  lemma l2br_negation_type_union: "wordinterval_to_set (l2br_negation_type_union l) = 
                        (\<Union> (i,j) \<in> set (getPos l). {i .. j}) \<union> (\<Union> (i,j) \<in> set (getNeg l). - {i .. j})"
  apply(simp add: l2br)
  apply(induction l rule: l2br_negation_type_union.induct)
    apply(simp_all)
   apply fast+
  done



 definition l2br_intersect :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len wordinterval" where
    "l2br_intersect = foldl (\<lambda> acc (s,e). wordinterval_intersection (WordInterval s e) acc) wordinterval_UNIV"

  lemma l2br_intersect: "wordinterval_to_set (l2br_intersect l) = (\<Inter> (i,j) \<in> set l. {i .. j})"
    proof -
    { fix U --\<open>@{const wordinterval_UNIV} generalized\<close>
      have "wordinterval_to_set (foldl (\<lambda>acc (s, e). wordinterval_intersection (WordInterval s e) acc) U l) = (wordinterval_to_set U) \<inter> (\<Inter>(i, j)\<in>set l. {i..j})"
          apply(induction l arbitrary: U)
           apply(simp)
          by force
    } thus ?thesis
      unfolding l2br_intersect_def by simp
    qed


  fun l2br_negation_type_intersect :: "('a::len word \<times> 'a::len word) negation_type list \<Rightarrow> 'a::len wordinterval" where
    "l2br_negation_type_intersect [] = wordinterval_UNIV" |
    "l2br_negation_type_intersect ((Pos (s,e))#ls) = wordinterval_intersection (WordInterval s e) (l2br_negation_type_intersect ls)" |
    "l2br_negation_type_intersect ((Neg (s,e))#ls) = wordinterval_intersection (wordinterval_invert (WordInterval s e)) (l2br_negation_type_intersect ls)"

  lemma l2br_negation_type_intersect_alt: "wordinterval_to_set (l2br_negation_type_intersect l) = 
                  wordinterval_to_set (wordinterval_setminus (l2br_intersect (getPos l)) (l2br (getNeg l)))"
    apply(simp add: l2br_intersect l2br)
    apply(induction l rule :l2br_negation_type_intersect.induct)
       apply(simp_all)
      apply(fast)+
    done

  lemma l2br_negation_type_intersect: "wordinterval_to_set (l2br_negation_type_intersect l) = 
                        (\<Inter> (i,j) \<in> set (getPos l). {i .. j}) - (\<Union> (i,j) \<in> set (getNeg l). {i .. j})"
    by(simp add: l2br_negation_type_intersect_alt l2br_intersect l2br)


end
