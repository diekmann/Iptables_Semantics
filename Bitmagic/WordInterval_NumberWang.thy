theory WordInterval_NumberWang
imports WordInterval
  "./l4v/lib/WordLemmaBucket"
  WordInterval_Lists
begin

text{*Cardinality approximation for wordintervals*}
(*TODO: move!*)
context begin
  lemma remdups_enum_upto: fixes s::"('a::len) word" shows "remdups [s .e. e] = [s .e. e]"
    by(simp)
  
  lemma card_enum_upto: fixes s::"('a::len) word" shows "card (set [s .e. e]) = Suc (unat e) - unat s"
    apply(subst List.card_set)
    apply(simp add: remdups_enum_upto)
    done
  
  lemma card_atLeastAtMost_word: fixes s::"('a::len) word" shows "card {s..e} = Suc (unat e) - (unat s)"
    apply(cases "s > e")
     apply(simp)
     apply(subst(asm) Word.word_less_nat_alt)
     apply simp
    apply(subst WordLemmaBucket.upto_enum_set_conv2[symmetric])
    apply(subst List.card_set)
    apply(simp add: remdups_enum_upto)
    done

  lemma finite_wordinterval: "finite (wordinterval_to_set r)" using WordLemmaBucket.finite_word by simp

  fun wordinterval_card :: "('a::len) wordinterval \<Rightarrow> nat" where
    "wordinterval_card (WordInterval s e) = Suc (unat e) - (unat s)" |
    "wordinterval_card (RangeUnion a b) = wordinterval_card a + wordinterval_card b"

  lemma wordinterval_card: "wordinterval_card r \<ge> card (wordinterval_to_set r)"
    proof(induction r)
    case WordInterval thus ?case by (simp add: card_atLeastAtMost_word)
    next
    case (RangeUnion r1 r2)
      have "card (wordinterval_to_set r1 \<union> wordinterval_to_set r2) \<le> card (wordinterval_to_set r1) + card (wordinterval_to_set r2)"
        using Finite_Set.card_Un_le by blast
      with RangeUnion show ?case by(simp)
    qed
end



(*minimizing wordintervals*)
(*TODO*)
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

  private lemma "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> B \<in> set (listwordinterval_compress ss) \<Longrightarrow> A \<noteq> B \<Longrightarrow> disjoint (interval_of A) (interval_of B)"
    apply(induction ss arbitrary:  rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp split: split_if_asm)
    apply(elim disjE)
    apply(simp_all)
    apply(simp_all add: disjoint_intervals_def disjoint_def)
    
    oops

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


value[code] "wordinterval_compress (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10)) (WordInterval 3 7))"
    

 

end