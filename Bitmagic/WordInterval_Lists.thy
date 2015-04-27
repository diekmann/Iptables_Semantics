theory WordInterval_Lists
imports WordInterval
  "../Semantics_Ternary/Negation_Type"
begin

subsection{*WordInterval to List*}
text{*A list of @{text "(start, end)"} tuples.*}

  fun br2l :: "'a::len wordinterval \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "br2l (RangeUnion r1 r2) = br2l r1 @ br2l r2" |
    "br2l (WordInterval s e) = (if e < s then [] else [(s,e)])"
  
  fun l2br :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len wordinterval" where
    "l2br [] = Empty_WordInterval" | 
    "l2br [(s,e)] = (WordInterval s e)" | 
    "l2br ((s,e)#rs) = (RangeUnion (WordInterval s e) (l2br rs))"
  

  lemma l2br_append: "wordinterval_to_set (l2br (l1@l2)) = wordinterval_to_set (l2br l1) \<union> wordinterval_to_set (l2br l2)"
    apply(induction l1 arbitrary: l2 rule:l2br.induct)
      apply(simp_all)
     apply(case_tac l2)
      apply(simp_all)
    by blast
  
  lemma l2br_br2l: "wordinterval_to_set (l2br (br2l r)) = wordinterval_to_set r"
    by(induction r) (simp_all add: l2br_append)

  lemma l2br: "wordinterval_to_set (l2br l) = (\<Union> (i,j) \<in> set l. {i .. j})"
    by(induction l rule: l2br.induct, simp_all)

  (*TODO: delete?*)
  definition l_br_toset :: "('a::len word \<times> 'a::len word) list \<Rightarrow> ('a::len word) set" where
    "l_br_toset l \<equiv> \<Union> (i,j) \<in> set l. {i .. j}"
  lemma l_br_toset: "l_br_toset l = wordinterval_to_set (l2br l)"
    unfolding l_br_toset_def
    apply(induction l rule: l2br.induct)
      apply(simp_all)
    done
  



  definition l2br_intersect :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len wordinterval" where
    "l2br_intersect = foldl (\<lambda> acc (s,e). wordinterval_intersection (WordInterval s e) acc) wordinterval_UNIV"

  lemma l2br_intersect: "wordinterval_to_set (l2br_intersect l) = (\<Inter> (i,j) \<in> set l. {i .. j})"
    proof -
    { fix U --{*@{const wordinterval_UNIV} generalized*}
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
