theory WordInterval_NumberWang
imports WordInterval
  "./l4v/lib/WordLemmaBucket"
  WordInterval_Lists
begin

text{*Cardinality approximation for @{typ "('a::len) wordinterval"}s*}
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

  text{*With @{thm wordinterval_compress} it should be possible to get the exact cardinality*}
end





context begin
  lemma shows "Suc e = m \<Longrightarrow> {l .. e} = {l..<m}"
    using atLeastLessThanSuc_atLeastAtMost by blast

  lemma word_Suc_leq: fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> x < k + 1 \<longleftrightarrow> x \<le> k"
    using WordLemmaBucket.less_x_plus_1 word_le_less_eq by auto


  lemma word_Suc_le: fixes k::"'a::len word" shows "x \<noteq> max_word \<Longrightarrow> x + 1 \<le> k \<longleftrightarrow> x < k"
    by (meson not_less word_Suc_leq)
    
    
  lemma word_lessThan_Suc_atMost: fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> {..< k + 1} = {..k}"
    by(simp add: lessThan_def atMost_def word_Suc_leq)
    
  lemma word_atLeastLessThan_Suc_atLeastAtMost:
    fixes l::"'a::len word" shows "u \<noteq> max_word \<Longrightarrow> {l..< u + 1} = {l..u}"
    by (simp add: atLeastAtMost_def atLeastLessThan_def word_lessThan_Suc_atMost)

  lemma word_atLeastAtMost_Suc_greaterThanAtMost: fixes l::"'a::len word" shows "m \<noteq> max_word \<Longrightarrow> {m<..u} = {m + 1..u}"
    by(simp add: greaterThanAtMost_def greaterThan_def atLeastAtMost_def atLeast_def word_Suc_le)
    

  lemma word_atLeastLessThan_Suc_atLeastAtMost_union: 
    fixes l::"'a::len word"
    assumes "m \<noteq> max_word" and "l \<le> m" and "m \<le> u"
    shows "{l..m} \<union> {m+1..u} = {l..u}"
    proof -
    from ivl_disj_un_two(8)[OF assms(2) assms(3)] have "{l..u} = {l..m} \<union> {m<..u}" by blast
    with assms show ?thesis by(simp add: word_atLeastAtMost_Suc_greaterThanAtMost)
    qed

  lemma huuuu: "word_next e = s' \<Longrightarrow> s \<le> e \<Longrightarrow> s' \<le> e' \<Longrightarrow> {s..e} \<union> {s'..e'} = {s .. e'}"
    by (metis Un_absorb2 atLeastatMost_subset_iff ivl_disj_un_two(7) max_word_max
              word_atLeastLessThan_Suc_atLeastAtMost word_le_less_eq word_next_def word_not_le)
    

  (*WIP*)
  private fun merge_adjacent :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list" where
     "merge_adjacent s [] = [s]" |
     "merge_adjacent (s,e) ((s',e')#ss) = (
        if s \<le>e \<and> s' \<le> e' \<and> word_next e = s'
        then (s, e')#ss
        else if s \<le>e \<and> s' \<le> e' \<and> word_next e' = s
        then (s', e)#ss
        else (s',e')#merge_adjacent (s,e) ss)"


  (*TODO: duplicate*)
  private fun interval_of :: "('a::len) word \<times> 'a word \<Rightarrow> 'a word set" where
    "interval_of (s,e) = {s .. e}"
  declare interval_of.simps[simp del]

  private lemma "interval_of A \<union> (\<Union>s \<in> set ss. interval_of s) = (\<Union>s \<in> set (merge_adjacent A ss). interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add:  interval_of.simps)
    apply(intro impI conjI)
       apply (metis Un_assoc huuuu)
      apply (smt Un_assoc Un_commute huuuu)
     using huuuu apply blast
    by blast
end


end