theory BitrangeLists
imports Bitrange
begin

subsection{*Bitrange to List*}
text{*A list of @{text "(start, end)"} tuples.*}

  fun br2l :: "'a::len bitrange \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "br2l (RangeUnion r1 r2) = br2l r1 @ br2l r2" |
    "br2l (Bitrange s e) = (if e < s then [] else [(s,e)])"
  
  fun l2br :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len bitrange" where
    "l2br [] = Empty_Bitrange" | 
    "l2br [(s,e)] = (Bitrange s e)" | 
    "l2br ((s,e)#rs) = (RangeUnion (Bitrange s e) (l2br rs))"
  

  lemma l2br_append: "bitrange_to_set (l2br (l1@l2)) = bitrange_to_set (l2br l1) \<union> bitrange_to_set (l2br l2)"
    apply(induction l1 arbitrary: l2 rule:l2br.induct)
      apply(simp_all)
     apply(case_tac l2)
      apply(simp_all)
    by blast
  
  lemma l2br_br2l: "bitrange_to_set (l2br (br2l r)) = bitrange_to_set r"
    by(induction r) (simp_all add: l2br_append)


  definition l_br_toset :: "('a::len word \<times> 'a::len word) list \<Rightarrow> ('a::len word) set" where
    "l_br_toset l \<equiv> \<Union> (i,j) \<in> set l. {i .. j}"

  lemma l_br_toset: "l_br_toset l = bitrange_to_set (l2br l)"
    unfolding l_br_toset_def
    apply(induction l rule: l2br.induct)
      apply(simp_all)
    done
  



  definition l2br_intersect :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len bitrange" where
    "l2br_intersect = foldl (\<lambda> acc (s,e). bitrange_intersection (Bitrange s e) acc) bitrange_UNIV"

  lemma l2br_intersect: "bitrange_to_set (l2br_intersect l) = (\<Inter> (i,j) \<in> set l. {i .. j})"
    proof -
    { fix U --{*@{const bitrange_UNIV} generalized*}
      have "bitrange_to_set (foldl (\<lambda>acc (s, e). bitrange_intersection (Bitrange s e) acc) U l) = (bitrange_to_set U) \<inter> (\<Inter>(i, j)\<in>set l. {i..j})"
          apply(induction l arbitrary: U)
           apply(simp)
          by force
    } thus ?thesis
      unfolding l2br_intersect_def by simp
    qed
    

end
