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

  lemma br2l: "(\<Union>(i,j)\<in>set (br2l r). {i .. j}) = wordinterval_to_set r"
    by(induction r rule: br2l.induct, simp_all)

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






text{*minimizing @{typ "('a::len) wordinterval"}s*}
(*TODO result has no empty intervals and all are disjoiint. merging things such as [1,7] [8,10] would still be possible*)
context
begin

  private definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
    "disjoint A B \<equiv> A \<inter> B = {}"

  private fun interval_of :: "('a::len) word \<times> 'a word \<Rightarrow> 'a word set" where
    "interval_of (s,e) = {s .. e}"
  declare interval_of.simps[simp del]

  private definition disjoint_intervals :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool" where
    "disjoint_intervals A B \<equiv> disjoint (interval_of A) (interval_of B)"

  private definition not_disjoint_intervals :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool" where
    "not_disjoint_intervals A B \<equiv> \<not> disjoint (interval_of A) (interval_of B)"

  private lemma [code]: "not_disjoint_intervals A B = (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s \<le> e' \<and> s' \<le> e \<and> s \<le> e \<and> s' \<le> e')"
    apply(cases A, cases B)
    apply(simp add: not_disjoint_intervals_def interval_of.simps disjoint_def)
    done

  private lemma [code]: "disjoint_intervals A B = (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e')"
    apply(cases A, cases B)
    apply(simp add: disjoint_intervals_def interval_of.simps disjoint_def)
    by fastforce

  private fun merge_overlap :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list" where
   "merge_overlap s [] = [s]" |
   "merge_overlap (s,e) ((s',e')#ss) = (
      if not_disjoint_intervals (s,e) (s',e')
      then (min s s', max e e')#ss
      else (s',e')#merge_overlap (s,e) ss)"

  private lemma not_disjoint_union:
      fixes s :: "('a::len) word"
      shows "\<not> disjoint {s..e} {s'..e'} \<Longrightarrow> {s..e} \<union> {s'..e'} = {min s s' .. max e e'}"
    by(auto simp add: disjoint_def min_def max_def)

  private lemma disjoint_subset: "disjoint A B \<Longrightarrow> A \<subseteq> B \<union> C \<Longrightarrow> A \<subseteq> C"
    unfolding disjoint_def
    by blast

  private lemma merge_overlap_helper1: "interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s) \<Longrightarrow>
      (\<Union>s \<in> set (merge_overlap A ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply blast
    apply(drule_tac C="(\<Union>x\<in>set xs. interval_of x)" in disjoint_subset)
     apply(simp_all)
    done

  private lemma merge_overlap_helper2: "\<exists>s'\<in>set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow>
          interval_of A \<union> (\<Union>s \<in> set ss. interval_of s) = (\<Union>s \<in> set (merge_overlap A ss). interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply blast
    apply(simp)
    by blast

  private lemma merge_overlap_length: "\<exists>s' \<in> set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow> length (merge_overlap A ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    done

  value[code] "merge_overlap (1:: 16 word,2)"

  private function listwordinterval_compress :: "(('a::len) word \<times> ('a::len) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
    "listwordinterval_compress [] = []" |
    "listwordinterval_compress (s#ss) = (
            if \<forall>s' \<in> set ss. disjoint_intervals s s'
            then s#listwordinterval_compress ss
            else listwordinterval_compress (merge_overlap s ss))"
  by(pat_completeness, auto)

  private termination listwordinterval_compress
  apply (relation "measure length")
    apply(rule wf_measure)
   apply(simp)
  using disjoint_intervals_def merge_overlap_length by fastforce

  private lemma listwordinterval_compress: "(\<Union>s \<in> set (listwordinterval_compress ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp)
    apply(intro impI)
    apply(simp add: disjoint_intervals_def)
    apply(drule merge_overlap_helper2)
    apply(simp)
    done

  value[code] "listwordinterval_compress [(1::32 word,3), (8,10), (2,5), (3,7)]"

  private lemma A_in_listwordinterval_compress: "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s)"
    using listwordinterval_compress by blast

  private lemma listwordinterval_compress_disjoint: 
    "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> B \<in> set (listwordinterval_compress ss) \<Longrightarrow> A \<noteq> B \<Longrightarrow> disjoint (interval_of A) (interval_of B)"
    apply(induction ss arbitrary: rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp split: split_if_asm)
    apply(elim disjE)
       apply(simp_all)
     apply(simp_all add: disjoint_intervals_def disjoint_def)
     apply(thin_tac [!] "False \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
     apply(blast dest: A_in_listwordinterval_compress)+
    done

  definition wordinterval_compress :: "('a::len) wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_compress r \<equiv> l2br (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))"

  lemma wordinterval_compress: "wordinterval_to_set (wordinterval_compress r) = wordinterval_to_set r"
    unfolding  wordinterval_compress_def
    proof -
      have interval_of': "\<And>s. interval_of s = (case s of (s,e) \<Rightarrow> {s .. e})" apply(case_tac s) using interval_of.simps by simp

      have "wordinterval_to_set (l2br (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))) =
            (\<Union>x\<in>set (listwordinterval_compress (br2l (wordinterval_optimize_empty r))). interval_of x)"
      using l2br interval_of.simps[symmetric] by blast
      also have "\<dots> =  (\<Union>s\<in>set (br2l (wordinterval_optimize_empty r)). interval_of s)"
        by(simp add: listwordinterval_compress)
      also have "\<dots> = (\<Union>(i, j)\<in>set (br2l (wordinterval_optimize_empty r)). {i..j})" by(simp add: interval_of')
      also have "\<dots> = wordinterval_to_set r" by(simp add: br2l)
      finally show "wordinterval_to_set (l2br (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))) = wordinterval_to_set r" .
  qed

end

(*RangeUnion (WordInterval 8 0xA) (WordInterval 1 7)
  this is not minimal, it would be possible to merge those two
  *)
value[code] "wordinterval_compress (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10)) (WordInterval 3 7))"
    



end
