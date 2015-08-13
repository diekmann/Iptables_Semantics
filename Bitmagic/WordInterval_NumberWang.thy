theory WordInterval_NumberWang
imports WordInterval
  "./l4v/lib/WordLemmaBucket"
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

  definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
    "disjoint A B \<equiv> A \<inter> B = {}"

  fun interval_of :: "('a::len) word \<times> 'a word \<Rightarrow> 'a word set" where
    "interval_of (s,e) = {s .. e}"
  declare interval_of.simps[simp del]

  fun merge_overlap :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list" where
   "merge_overlap s [] = [s]" |
   "merge_overlap (s,e) ((s',e')#ss) = (
      if (*s \<le> e' \<and> s' \<le> e \<and> s \<le> e \<and> s' \<le> e'*) \<not> disjoint {s..e} {s'..e'}
      then (min s s', max e e')#ss
      else (s',e')#merge_overlap (s,e) ss)"

  private lemma not_disjoint_union:
      fixes s :: "('a::len) word"
      shows "\<not> disjoint {s..e} {s'..e'} \<Longrightarrow> {s..e} \<union> {s'..e'} = {min s s' .. max e e'}"
    by(auto simp add: disjoint_def min_def max_def)

  private lemma disjoint_subset: "disjoint A B \<Longrightarrow> A \<subseteq> B \<union> C \<Longrightarrow> A \<subseteq> C"
    unfolding disjoint_def
    by blast

  private lemma merge_overlap_helper: "interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s) \<Longrightarrow>
      (\<Union>s \<in> set ss. interval_of s) = (\<Union>s \<in> set (merge_overlap A ss). interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply(simp add: interval_of.simps[symmetric])
     apply blast
    apply(drule_tac C="(\<Union>x\<in>set xs. interval_of x)" in disjoint_subset)
     apply(simp_all add: interval_of.simps)
    done

  lemma merge_overlap_length: "\<exists>s' \<in> set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow> length (merge_overlap A ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: interval_of.simps)
    done

  function listwordinterval_compress :: "(('a::len) word \<times> ('a::len) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
    "listwordinterval_compress [] = []" |
    "listwordinterval_compress (s#ss) = (
            if \<forall>s' \<in> set ss. disjoint (interval_of s) (interval_of s')
            then s#listwordinterval_compress ss
            else listwordinterval_compress (merge_overlap s ss))"
  by(pat_completeness, auto)

  termination listwordinterval_compress
  apply (relation "measure length")
    apply(rule wf_measure)
   apply(simp)
  using merge_overlap_length by fastforce



  fun get_overlap :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> (('a::len) word \<times> ('a::len) word) list \<Rightarrow> (('a::len) word \<times> ('a::len) word) option" where
   "get_overlap _ [] = None" |
   "get_overlap (s,e) ((s',e')#ss)= (if (*{s..e} \<inter> {s'..e'} \<noteq> {}*) (s \<le> e' \<and> s' \<le> e \<and> s \<le> e \<and> s' \<le> e') then Some (s',e') else get_overlap (s,e) ss)"

  fun listinterval_minimize :: "(('a::len) word \<times> ('a::len) word) list \<Rightarrow> (('a::len) word \<times> ('a::len) word) list" where
    "listinterval_minimize [] = []" |
    "listinterval_minimize ((s,e)#ss) = (case get_overlap (s,e) ss of None \<Rightarrow> (s,e)#listinterval_minimize ss |
                                                                Some (s',e') \<Rightarrow> (min s s', max e e')#listinterval_minimize (*remove1 (s',e') ss)*) ss)"

  private lemma helper1: "{x. x = (min aa ab, max ba bb) \<or> x \<in> set (listinterval_minimize ss)} = {(min aa ab, max ba bb)} \<union> (set (listinterval_minimize ss))"
    by blast

  private lemma get_overlap_helper: "get_overlap (s,e) ss = Some (s',e') \<Longrightarrow> {min s s' .. max e e'} \<subseteq> (\<Union>(s,e) \<in> set ((s,e)#ss). {s .. e})"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(case_tac x)
    apply(simp)
    apply(simp split: option.split split_if_asm)
     apply(clarify)
     apply(simp add: min_def max_def split: split_if_asm)
    apply(clarify)
    by blast

  private lemma helper2: fixes s::"('a::len) word" shows "{min s s' .. max e e'} \<subseteq> (\<Union>(s,e) \<in> set ((s,e)#ss). {s .. e}) \<Longrightarrow>
    {min s s' .. max e e'} \<union> (\<Union>(s,e) \<in> set ((s,e)#ss). {s .. e}) = {min s s' .. max e e'} \<union> (\<Union>(s,e) \<in> set (ss). {s .. e})"
  apply(subgoal_tac "{s .. e} \<subseteq> {min s s' .. max e e'}")
   prefer 2
   apply simp
  by fastforce (*>3s*)
   
  
  lemma "(\<Union>(s,e) \<in> set ss. {s .. e}) = (\<Union>(s,e) \<in> set (listinterval_minimize ss). {s .. e})"
    apply(induction ss)
     apply(simp)
    apply(rename_tac s ss)
    apply(case_tac s)
    apply(simp split: option.split)
    apply(clarify)
    apply(simp add: helper1)
    apply(drule get_overlap_helper)
    apply(subst helper2[symmetric])
     apply(simp)
    by auto

  (*TODO: it does actually not minimize since we do not remove the merged interval*)
  lemma "\<forall>(a,b) \<in> set (listinterval_minimize ss). \<forall> (c,d) \<in> set (listinterval_minimize ss). {a..b} \<inter> {c..d} = {}"
    oops
end 
 

end