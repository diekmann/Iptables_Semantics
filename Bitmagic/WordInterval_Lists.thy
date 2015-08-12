theory WordInterval_Lists
imports WordInterval
  "../Common/Negation_Type"
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
    proof(induction l1 arbitrary: l2 rule:l2br.induct)
    case 1 thus ?case by simp
    next
    case (2 s e l2) thus ?case by (cases l2) simp_all
    next
    case 3 thus ?case by force
    qed
  
  lemma l2br_br2l: "wordinterval_to_set (l2br (br2l r)) = wordinterval_to_set r"
    by(induction r) (simp_all add: l2br_append)

  lemma l2br: "wordinterval_to_set (l2br l) = (\<Union> (i,j) \<in> set l. {i .. j})"
    by(induction l rule: l2br.induct, simp_all)



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
end
