(*  Title:      IPv4Addr.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory WordInterval
imports Main
  NumberWang
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

text{*Intervals of consecutive words*}

value "(2::nat) < 2^32" (*without Code_Target_Nat, this would be really slow*)

  datatype ('a::len) wordinterval = WordInterval
                                        "('a::len) word" --"start (inclusive)"
                                        "('a::len) word" --"end (inclusive)"
                                  | RangeUnion "'a wordinterval" "'a wordinterval"

  fun wordinterval_to_set :: "'a::len wordinterval \<Rightarrow> ('a::len word) set" where
    "wordinterval_to_set (WordInterval start end) = {start .. end}" |
    "wordinterval_to_set (RangeUnion r1 r2) = (wordinterval_to_set r1) \<union> (wordinterval_to_set r2)"

  fun wordinterval_element :: "'a::len word \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where
    "wordinterval_element el (WordInterval s e) = (s \<le> el \<and> el \<le> e)" |
    "wordinterval_element el (RangeUnion r1 r2) = (wordinterval_element el r1 \<or> wordinterval_element el r2)"
  lemma wordinterval_element_set_eq[simp]: "wordinterval_element el rg = (el \<in> wordinterval_to_set rg)"
    by(induction rg rule: wordinterval_element.induct) simp_all

  fun wordinterval_union :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where 
    "wordinterval_union r1 r2 = RangeUnion r1 r2"
  lemma wordinterval_union_set_eq[simp]: "wordinterval_to_set (wordinterval_union r1 r2) = wordinterval_to_set r1 \<union> wordinterval_to_set r2" by simp

  fun wordinterval_empty :: "'a::len wordinterval \<Rightarrow> bool" where
    "wordinterval_empty (WordInterval s e) = (e < s)" |
    "wordinterval_empty (RangeUnion r1 r2) = (wordinterval_empty r1 \<and> wordinterval_empty r2)"
  lemma wordinterval_empty_set_eq[simp]: "wordinterval_empty r \<longleftrightarrow> wordinterval_to_set r = {}"
    by(induction r) auto

  context
  begin
    fun wordinterval_optimize_empty where
      "wordinterval_optimize_empty (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1 in (let r2o = wordinterval_optimize_empty r2 in (
        if wordinterval_empty r1o then r2o else (if wordinterval_empty r2o then r1o else (RangeUnion r1o r2o)))))" |
      "wordinterval_optimize_empty r = r"
    lemma wordinterval_optimize_empty_set_eq[simp]: "wordinterval_to_set (wordinterval_optimize_empty r) = wordinterval_to_set r"
      by(induction r) (simp_all add: Let_def)
    lemma wordinterval_optimize_empty_double[simp]: "wordinterval_optimize_empty (wordinterval_optimize_empty r) = wordinterval_optimize_empty r"
      apply(induction r)
      by(simp_all add: Let_def)
    private fun wordinterval_empty_shallow where
      "wordinterval_empty_shallow (WordInterval s e) = (e < s)" |
      "wordinterval_empty_shallow (RangeUnion _ _) = False"
    private lemma helper_optimize_shallow: "wordinterval_empty (wordinterval_optimize_empty r) = wordinterval_empty_shallow (wordinterval_optimize_empty r)"
      by(induction r) fastforce+
    private fun wordinterval_optimize_empty2 where
      "wordinterval_optimize_empty2 (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1 in (let r2o = wordinterval_optimize_empty r2 in (
        if wordinterval_empty_shallow r1o then r2o else (if wordinterval_empty_shallow r2o then r1o else (RangeUnion r1o r2o)))))" |
      "wordinterval_optimize_empty2 r = r"
    lemma wordinterval_optimize_empty_code[code_unfold]: "wordinterval_optimize_empty = wordinterval_optimize_empty2"
      by (subst fun_eq_iff, clarify, rename_tac r, induct_tac r)
         (unfold wordinterval_optimize_empty.simps wordinterval_optimize_empty2.simps Let_def helper_optimize_shallow[symmetric], simp_all)
  end

  definition Empty_WordInterval :: "'a::len wordinterval" where  "Empty_WordInterval \<equiv> WordInterval 1 0"
  lemma wordinterval_empty_Empty_WordInterval: "wordinterval_empty Empty_WordInterval" by(simp add: Empty_WordInterval_def)
  lemma Empty_WordInterval_set_eq[simp]: "wordinterval_to_set Empty_WordInterval = {}" by(simp add: Empty_WordInterval_def)

  fun wordinterval_to_list  :: "'a::len wordinterval \<Rightarrow> ('a::len wordinterval) list" where
    "wordinterval_to_list (RangeUnion r1 r2) = wordinterval_to_list r1 @ wordinterval_to_list r2" |
    "wordinterval_to_list r = (if wordinterval_empty r then [] else [r])"

  lemma wordinterval_to_list_set_eq: "(\<Union>set (map wordinterval_to_set (wordinterval_to_list rs))) = wordinterval_to_set rs"
  by(induction rs) simp_all

  fun list_to_wordinterval where
    "list_to_wordinterval [r] = r" |
    "list_to_wordinterval (r#rs) = (RangeUnion r (list_to_wordinterval rs))" |
    "list_to_wordinterval [] = Empty_WordInterval"

  lemma list_to_wordinterval_set_eq: "wordinterval_to_set (list_to_wordinterval rs) = (\<Union>set (map wordinterval_to_set rs)) "
    by(induction rs rule: list_to_wordinterval.induct) simp_all
  
  lemma list_to_wordinterval_set_eq_simp[simp]: "wordinterval_to_set (list_to_wordinterval (a # as)) = wordinterval_to_set (wordinterval_union a (list_to_wordinterval as))"
    by(cases as) auto
    
  (*
  fun wordinterval_linearize :: "('a::len) wordinterval \<Rightarrow> ('a::len) wordinterval" where
    "wordinterval_linearize rs = list_to_wordinterval (wordinterval_to_list rs)"
  lemma "wordinterval_to_set (wordinterval_linearize r) = wordinterval_to_set r"
    by(simp, metis list_to_wordinterval_set_eq wordinterval_to_list_set_eq)
  *)

  (*TODO: remove this*)
  fun wordinterval_optimize_same where "wordinterval_optimize_same rs = list_to_wordinterval (remdups (wordinterval_to_list rs))"
  lemma wordinterval_optimize_same_set_eq[simp]: "wordinterval_to_set (wordinterval_optimize_same rs) = wordinterval_to_set rs"
   by(simp, subst list_to_wordinterval_set_eq) (metis image_set wordinterval_to_list_set_eq set_remdups)
  

  fun wordinterval_is_simple where "wordinterval_is_simple (WordInterval _ _) = True" | "wordinterval_is_simple (RangeUnion _ _) = False"
  fun wordintervalist_union_free where
    "wordintervalist_union_free (r#rs) = (wordinterval_is_simple r \<and> wordintervalist_union_free rs)" |
    "wordintervalist_union_free [] = True"
  lemma wordintervalist_union_freeX: "wordintervalist_union_free (r # rs) \<Longrightarrow> \<exists> s e. r = WordInterval s e"
    by (induction rs) (cases r, simp, simp)+
  lemma wordintervalist_union_free_append: "wordintervalist_union_free (a@b) = (wordintervalist_union_free a \<and> wordintervalist_union_free b)"
    by (induction a) (auto)
  lemma wordinterval_to_list_union_free: "l = wordinterval_to_list r \<Longrightarrow> wordintervalist_union_free l"
    by(induction r arbitrary: l) (simp_all add: wordintervalist_union_free_append)




  text{*previous and next words addresses, without wrap around*}
    definition word_next :: "'a::len word \<Rightarrow> 'a::len word" where
      "word_next a \<equiv> if a = max_word then max_word else a + 1"
    definition word_prev :: "'a::len word \<Rightarrow> 'a::len word" where
      "word_prev a \<equiv> if a = 0 then 0 else a - 1"
  
    lemma "word_next (2:: 8 word) = 3" by eval
    lemma "word_prev (2:: 8 word) = 1" by eval
    lemma "word_prev (0:: 8 word) = 0" by eval


  fun wordinterval_setminus :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_setminus (WordInterval s e) (WordInterval ms me) = (
      if s > e \<or> ms > me then WordInterval s e else
      if me \<ge> e
        then
          WordInterval (if ms = 0 then 1 else s) (min e (word_prev ms))
        else if ms \<le> s
        then
          WordInterval (max s (word_next me)) (if me = max_word then 0 else e)
        else
          RangeUnion (WordInterval (if ms = 0 then 1 else s) (word_prev ms)) (WordInterval (word_next me) (if me = max_word then 0 else e))
        )" |
     "wordinterval_setminus (RangeUnion r1 r2) t = RangeUnion (wordinterval_setminus r1 t) (wordinterval_setminus r2 t)"|
     "wordinterval_setminus t (RangeUnion r1 r2) = wordinterval_setminus (wordinterval_setminus t r1) r2"

  lemma wordinterval_setminus_rr_set_eq[simp]: "wordinterval_to_set(wordinterval_setminus (WordInterval s e) (WordInterval ms me)) = 
    wordinterval_to_set (WordInterval s e) - wordinterval_to_set (WordInterval ms me)"
     apply(simp only: wordinterval_setminus.simps)
     apply(case_tac "e < s") 
      apply simp
     apply(case_tac "me < ms") 
      apply simp
     apply(case_tac [!] "e \<le> me")
      apply(case_tac [!] "ms = 0") 
        apply(case_tac [!] "ms \<le> s") 
            apply(case_tac [!] "me = max_word")
                    apply(simp_all add: word_prev_def word_next_def min_def max_def)
            apply(safe)
                                  apply(auto)
                          apply(uint_arith) 
                         apply(uint_arith)
                        apply(uint_arith)
                       apply(uint_arith)
                      apply(uint_arith)
                     apply(uint_arith)
                    apply(uint_arith)
                   apply(uint_arith)
                  apply(uint_arith)
                 apply(uint_arith)
                apply(uint_arith)
               apply(uint_arith)
              apply(uint_arith)
             apply(uint_arith)
            apply(uint_arith)
           apply(uint_arith)
          apply(uint_arith)
         apply(uint_arith)
        apply(uint_arith)
       apply(uint_arith)
      apply(uint_arith)
     apply(uint_arith)
   done

  lemma wordinterval_setminus_set_eq[simp]: "wordinterval_to_set (wordinterval_setminus r1 r2) = 
    wordinterval_to_set r1 - wordinterval_to_set r2"
    apply(induction rule: wordinterval_setminus.induct)
      using wordinterval_setminus_rr_set_eq apply blast
     apply auto
    done
  lemma wordinterval_setminus_empty_struct: "wordinterval_empty r2 \<Longrightarrow> wordinterval_setminus r1 r2 = r1"
    by(induction r1 r2 rule: wordinterval_setminus.induct) auto

  definition "wordinterval_UNIV \<equiv> WordInterval 0 max_word"
  lemma wordinterval_UNIV_set_eq[simp]: "wordinterval_to_set wordinterval_UNIV = UNIV"
    unfolding wordinterval_UNIV_def
    using max_word_max by fastforce
    
  fun wordinterval_invert :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_invert r = wordinterval_setminus wordinterval_UNIV r"
  lemma wordinterval_invert_set_eq[simp]: "wordinterval_to_set (wordinterval_invert r) = UNIV - wordinterval_to_set r" by(auto)

  lemma wordinterval_invert_UNIV_empty: "wordinterval_empty (wordinterval_invert wordinterval_UNIV)" by simp


  lemma "{(s::nat) .. e} \<inter> {s' .. e'} = {} \<longleftrightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e'"
    by simp linarith

  fun wordinterval_intersection' :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_intersection' (WordInterval s e) (WordInterval s' e') = (
        if s > e \<or> s' > e' \<or> s > e' \<or> s' > e \<or> s > e \<or> s' > e'
        then
          Empty_WordInterval
        else
          WordInterval (max s s') (min e e')
        )" |
    "wordinterval_intersection' (RangeUnion r1 r2) t = RangeUnion (wordinterval_intersection' r1 t) (wordinterval_intersection' r2 t)"|
    "wordinterval_intersection' t (RangeUnion r1 r2) = RangeUnion (wordinterval_intersection' t r1) (wordinterval_intersection' t r2)"

  lemma wordinterval_intersection'_set_eq[simp]: 
    "wordinterval_to_set (wordinterval_intersection' r1 r2) = wordinterval_to_set r1 \<inter> wordinterval_to_set r2"
    by(induction r1 r2 rule: wordinterval_intersection'.induct) (auto)
  
  
  lemma wordinterval_setminus_intersection_empty_struct_rr: 
    "wordinterval_empty (wordinterval_intersection' (WordInterval r1s r1e) (WordInterval r2s r2e)) \<Longrightarrow> 
    wordinterval_setminus (WordInterval r1s r1e) (WordInterval r2s r2e) = (WordInterval r1s r1e)"
    apply(subst(asm) wordinterval_empty_set_eq) 
    apply(subst(asm) wordinterval_intersection'_set_eq)
    apply(unfold wordinterval_to_set.simps(1))
    apply(cases "wordinterval_empty (WordInterval r1s r1e)", case_tac [!] "wordinterval_empty (WordInterval r2s r2e)")
       apply(unfold wordinterval_empty.simps(1))
       apply(force, force, force)
    apply(cases "r1e < r2s") 
     defer
     apply(subgoal_tac "r2e < r1s")
      defer
      apply force
     apply(simp only: wordinterval_setminus.simps)
     apply(case_tac [!] "r1e \<le> r2e", case_tac [!] "r2s \<le> r1s")
           apply(auto)
     apply (metis add.commute inc_i le_minus min_absorb1 word_le_sub1 word_prev_def word_zero_le)
    apply(metis inc_le word_next_def max.order_iff)
  done

  declare wordinterval_intersection'.simps[simp del]
  declare wordinterval_setminus.simps(1)[simp del]

  lemma wordinterval_setminus_intersection_empty_struct:
    "wordinterval_empty (wordinterval_intersection' r1 r2) \<Longrightarrow> 
    wordinterval_setminus r1 r2 = r1"
    by (induction r1 r2 rule: wordinterval_setminus.induct, auto simp add: wordinterval_setminus_intersection_empty_struct_rr) fastforce

  definition wordinterval_subset :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where
    "wordinterval_subset r1 r2 \<equiv> wordinterval_empty (wordinterval_setminus r1 r2)"
  lemma wordinterval_subset_set_eq[simp]: "wordinterval_subset r1 r2 = (wordinterval_to_set r1 \<subseteq> wordinterval_to_set r2)"
    unfolding wordinterval_subset_def by simp

  definition wordinterval_eq :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where 
    "wordinterval_eq r1 r2 = (wordinterval_subset r1 r2 \<and> wordinterval_subset r2 r1)"
  lemma wordinterval_eq_set_eq: "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_to_set r1 = wordinterval_to_set r2"
    unfolding wordinterval_eq_def by auto
  thm iffD1[OF wordinterval_eq_set_eq]
  declare iffD1[OF wordinterval_eq_set_eq, simp]
  lemma wordinterval_eq_comm: "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_eq r2 r1"
    unfolding wordinterval_eq_def by fast
  lemma wordinterval_to_set_alt: "wordinterval_to_set r = {x. wordinterval_element x r}"
    unfolding wordinterval_element_set_eq by blast
 
  lemma wordinterval_un_empty: "wordinterval_empty r1 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r2"
    by(subst wordinterval_eq_set_eq, simp)
  lemma wordinterval_un_emty_b: "wordinterval_empty r2 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r1"
    by(subst wordinterval_eq_set_eq, simp)
  
  lemma wordinterval_Diff_triv: 
    assumes "wordinterval_empty (wordinterval_intersection' a b)" shows "wordinterval_eq (wordinterval_setminus a b) a"
    using wordinterval_setminus_intersection_empty_struct[OF assms] wordinterval_eq_set_eq[of a a] by simp

  fun wordinterval_size :: "('a::len) wordinterval \<Rightarrow> nat" where
    "wordinterval_size (RangeUnion a b) = wordinterval_size a + wordinterval_size b" |
    "wordinterval_size (WordInterval s e) = (if s \<le> e then 1 else 0)"
  lemma "wordinterval_size r = length (wordinterval_to_list r)"
    by(induction r, simp_all)

  lemma [simp]: "\<exists>x::('a::len wordinterval). y \<in> wordinterval_to_set x"
  proof show "y \<in> wordinterval_to_set wordinterval_UNIV" by simp qed





  lemma wordinterval_eq_reflp:
    "reflp wordinterval_eq"
    apply(rule reflpI)
    by(simp only: wordinterval_eq_set_eq)
  lemma wordintervalt_eq_symp:
    "symp wordinterval_eq"
    apply(rule sympI)
    by(simp add: wordinterval_eq_comm)
  lemma wordinterval_eq_transp:
    "transp wordinterval_eq"
    apply(rule transpI)
    by(simp only: wordinterval_eq_set_eq)

  lemma wordinterval_eq_equivp:
    "equivp wordinterval_eq"
    by (auto intro: equivpI wordinterval_eq_reflp wordintervalt_eq_symp wordinterval_eq_transp)
(*
  quotient_type 'a bitrrq = "'a::len wordinterval" / "wordinterval_eq"
    by (rule wordinterval_eq_equivp)
*)
    
end
