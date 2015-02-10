(*  Title:      IPv4Addr.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory Bitrange
imports Main
  NumberWang
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

text{*Intervals of consecutive words*}

value "(2::nat) < 2^32" (*without Code_Target_Nat, this would be really slow*)

  datatype ('a::len) bitrange = Bitrange
                "('a::len) word" --"start (inclusive)"
                "('a::len) word" --"end (inclusive)"
                | RangeUnion "'a bitrange" "'a bitrange"

  fun bitrange_to_set :: "'a::len bitrange \<Rightarrow> ('a::len word) set" where
    "bitrange_to_set (Bitrange start end) = {start .. end}" |
    "bitrange_to_set (RangeUnion r1 r2) = (bitrange_to_set r1) \<union> (bitrange_to_set r2)"

  fun bitrange_element :: "'a::len word \<Rightarrow> 'a::len bitrange \<Rightarrow> bool" where
    "bitrange_element el (Bitrange s e) = (s \<le> el \<and> el \<le> e)" |
    "bitrange_element el (RangeUnion r1 r2) = (bitrange_element el r1 \<or> bitrange_element el r2)"
  lemma bitrange_element_set_eq[simp]: "bitrange_element el rg = (el \<in> bitrange_to_set rg)"
    by(induction rg rule: bitrange_element.induct) simp_all

  fun bitrange_union :: "'a::len bitrange \<Rightarrow> 'a::len bitrange \<Rightarrow> 'a::len bitrange" where 
    "bitrange_union r1 r2 = RangeUnion r1 r2"
  lemma bitrange_union_set_eq[simp]: "bitrange_to_set (bitrange_union r1 r2) = bitrange_to_set r1 \<union> bitrange_to_set r2" by simp

  fun bitrange_empty :: "'a::len bitrange \<Rightarrow> bool" where
    "bitrange_empty (Bitrange s e) = (e < s)" |
    "bitrange_empty (RangeUnion r1 r2) = (bitrange_empty r1 \<and> bitrange_empty r2)"
  lemma bitrange_empty_set_eq[simp]: "bitrange_empty r \<longleftrightarrow> bitrange_to_set r = {}"
    by(induction r) auto

  fun bitrange_optimize_empty where
    "bitrange_optimize_empty (RangeUnion r1 r2) = (let r1o = bitrange_optimize_empty r1 in (let r2o = bitrange_optimize_empty r2 in (
      if bitrange_empty r1o then r2o else (if bitrange_empty r2o then r1o else (RangeUnion r1o r2o)))))" |
    "bitrange_optimize_empty r = r"
  lemma bitrange_optimize_empty_set_eq[simp]: "bitrange_to_set (bitrange_optimize_empty r) = bitrange_to_set r"
    by(induction r) (simp_all add: Let_def)
  lemma bitrange_optimize_empty_double[simp]: "bitrange_optimize_empty (bitrange_optimize_empty r) = bitrange_optimize_empty r"
    apply(induction r)
    by(simp_all add: Let_def)
  fun bitrange_empty_shallow where
    "bitrange_empty_shallow (Bitrange s e) = (e < s)" |
    "bitrange_empty_shallow (RangeUnion _ _) = False"
  lemma helper_optimize_shallow: "bitrange_empty (bitrange_optimize_empty r) = bitrange_empty_shallow (bitrange_optimize_empty r)"
    by(induction r) fastforce+
  fun bitrange_optimize_empty2 where
    "bitrange_optimize_empty2 (RangeUnion r1 r2) = (let r1o = bitrange_optimize_empty r1 in (let r2o = bitrange_optimize_empty r2 in (
      if bitrange_empty_shallow r1o then r2o else (if bitrange_empty_shallow r2o then r1o else (RangeUnion r1o r2o)))))" |
    "bitrange_optimize_empty2 r = r"
  lemma bitrange_optimize_empty_code[code_unfold]: "bitrange_optimize_empty = bitrange_optimize_empty2"
    by (subst fun_eq_iff, clarify, rename_tac r, induct_tac r)
       (unfold bitrange_optimize_empty.simps bitrange_optimize_empty2.simps Let_def helper_optimize_shallow[symmetric], simp_all)

  definition Empty_Bitrange :: "'a::len bitrange" where  "Empty_Bitrange \<equiv> Bitrange 1 0"
  lemma bitrange_empty_Empty_Bitrange: "bitrange_empty Empty_Bitrange" by(simp add: Empty_Bitrange_def)
  lemma Empty_Bitrange_set_eq[simp]: "bitrange_to_set Empty_Bitrange = {}" by(simp add: Empty_Bitrange_def)

  fun bitrange_to_list  :: "'a::len bitrange \<Rightarrow> ('a::len bitrange) list" where
    "bitrange_to_list (RangeUnion r1 r2) = bitrange_to_list r1 @ bitrange_to_list r2" |
    "bitrange_to_list r = (if bitrange_empty r then [] else [r])"

  lemma bitrange_to_list_set_eq: "(\<Union>set (map bitrange_to_set (bitrange_to_list rs))) = bitrange_to_set rs"
  by(induction rs) simp_all

  fun list_to_bitrange where
    "list_to_bitrange [r] = r" |
    "list_to_bitrange (r#rs) = (RangeUnion r (list_to_bitrange rs))" |
    "list_to_bitrange [] = Empty_Bitrange"

  lemma list_to_bitrange_set_eq: "(\<Union>set (map bitrange_to_set rs)) = bitrange_to_set (list_to_bitrange rs)"
    by(induction rs rule: list_to_bitrange.induct) simp_all
  
  lemma list_to_bitrange_set_eq_simp[simp]: "bitrange_to_set (list_to_bitrange (a # as)) = bitrange_to_set (bitrange_union a (list_to_bitrange as))"
    by(cases as) auto
    
    
  fun bitrange_linearize where "bitrange_linearize rs = list_to_bitrange (bitrange_to_list rs)"
  lemma "bitrange_to_set (bitrange_linearize r) = bitrange_to_set r"
    by(simp, metis list_to_bitrange_set_eq bitrange_to_list_set_eq)

  fun bitrange_optimize_same where "bitrange_optimize_same rs = list_to_bitrange (remdups (bitrange_to_list rs))"
  lemma bitrange_optimize_same_set_eq[simp]: "bitrange_to_set (bitrange_optimize_same rs) = bitrange_to_set rs"
   by(simp, subst list_to_bitrange_set_eq[symmetric]) (metis image_set bitrange_to_list_set_eq set_remdups)

  fun bitrange_is_simple where "bitrange_is_simple (Bitrange _ _) = True" | "bitrange_is_simple (RangeUnion _ _) = False"
  fun bitrangelist_union_free where
    "bitrangelist_union_free (r#rs) = (bitrange_is_simple r \<and> bitrangelist_union_free rs)" |
    "bitrangelist_union_free [] = True"
  lemma bitrangelist_union_freeX: "bitrangelist_union_free (r # rs) \<Longrightarrow> \<exists> s e. r = Bitrange s e"
    by (induction rs) (cases r, simp, simp)+
  lemma bitrangelist_union_free_append: "bitrangelist_union_free (a@b) = (bitrangelist_union_free a \<and> bitrangelist_union_free b)"
    by (induction a) (auto)
  lemma bitrange_to_list_union_free: "l = bitrange_to_list r \<Longrightarrow> bitrangelist_union_free l"
    by(induction r arbitrary: l) (simp_all add: bitrangelist_union_free_append)




  text{*previous and next words addresses, without wrap around*}
    definition word_next :: "'a::len word \<Rightarrow> 'a::len word" where
      "word_next a \<equiv> if a = max_word then max_word else a + 1"
    definition word_prev :: "'a::len word \<Rightarrow> 'a::len word" where
      "word_prev a \<equiv> if a = 0 then 0 else a - 1"
  
    lemma "word_next (2:: 8 word) = 3" by eval
    lemma "word_prev (2:: 8 word) = 1" by eval
    lemma "word_prev (0:: 8 word) = 0" by eval


  fun bitrange_setminus :: "'a::len bitrange \<Rightarrow> 'a::len bitrange \<Rightarrow> 'a::len bitrange" where
    "bitrange_setminus (Bitrange s e) (Bitrange ms me) = (
      if s > e \<or> ms > me then Bitrange s e else
      if me \<ge> e
        then
          Bitrange (if ms = 0 then 1 else s) (min e (word_prev ms))
        else if ms \<le> s
        then
          Bitrange (max s (word_next me)) (if me = max_word then 0 else e)
        else
          RangeUnion (Bitrange (if ms = 0 then 1 else s) (word_prev ms)) (Bitrange (word_next me) (if me = max_word then 0 else e))
        )" |
     "bitrange_setminus (RangeUnion r1 r2) t = RangeUnion (bitrange_setminus r1 t) (bitrange_setminus r2 t)"|
     "bitrange_setminus t (RangeUnion r1 r2) = bitrange_setminus (bitrange_setminus t r1) r2"

  lemma bitrange_setminus_rr_set_eq[simp]: "bitrange_to_set(bitrange_setminus (Bitrange s e) (Bitrange ms me)) = 
    bitrange_to_set (Bitrange s e) - bitrange_to_set (Bitrange ms me)"
     apply(simp only: bitrange_setminus.simps)
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

  lemma bitrange_setminus_set_eq[simp]: "bitrange_to_set (bitrange_setminus r1 r2) = 
    bitrange_to_set r1 - bitrange_to_set r2"
    apply(induction rule: bitrange_setminus.induct)
      using bitrange_setminus_rr_set_eq apply blast
     apply auto
    done
  lemma bitrange_setminus_empty_struct: "bitrange_empty r2 \<Longrightarrow> bitrange_setminus r1 r2 = r1"
    by(induction r1 r2 rule: bitrange_setminus.induct) auto

  definition "bitrange_UNIV \<equiv> Bitrange 0 max_word"
  lemma bitrange_UNIV_set_eq[simp]: "bitrange_to_set bitrange_UNIV = UNIV"
    unfolding bitrange_UNIV_def
    using max_word_max by fastforce
    
  fun bitrange_invert :: "'a::len bitrange \<Rightarrow> 'a::len bitrange" where
    "bitrange_invert r = bitrange_setminus bitrange_UNIV r"
  lemma bitrange_invert_set_eq[simp]: "bitrange_to_set (bitrange_invert r) = UNIV - bitrange_to_set r" by(auto)

  lemma bitrange_invert_UNIV_empty: "bitrange_empty (bitrange_invert bitrange_UNIV)" by simp

  fun bitrange_intersection :: "'a::len bitrange \<Rightarrow> 'a::len bitrange \<Rightarrow> 'a::len bitrange" where 
    "bitrange_intersection r1 r2 = 
      bitrange_optimize_same (bitrange_setminus (bitrange_union r1 r2) (bitrange_union (bitrange_invert r1) (bitrange_invert r2)))"
  lemma bitrange_intersection_set_eq[simp]: "bitrange_to_set (bitrange_intersection r1 r2) = bitrange_to_set r1 \<inter> bitrange_to_set r2"
    unfolding bitrange_intersection.simps bitrange_optimize_same_set_eq by auto
  
  lemma bitrange_setminus_intersection_empty_struct_rr: 
    "bitrange_empty (bitrange_intersection (Bitrange r1s r1e) (Bitrange r2s r2e)) \<Longrightarrow> 
    bitrange_setminus (Bitrange r1s r1e) (Bitrange r2s r2e) = (Bitrange r1s r1e)"
    apply(subst(asm) bitrange_empty_set_eq) 
    apply(subst(asm) bitrange_intersection_set_eq)
    apply(unfold bitrange_to_set.simps(1))
    apply(cases "bitrange_empty (Bitrange r1s r1e)", case_tac [!] "bitrange_empty (Bitrange r2s r2e)")
       apply(unfold bitrange_empty.simps(1))
       apply(force, force, force)
    apply(cases "r1e < r2s") 
     defer
     apply(subgoal_tac "r2e < r1s")
      defer
      apply force
     apply(simp only: bitrange_setminus.simps)
     apply(case_tac [!] "r1e \<le> r2e", case_tac [!] "r2s \<le> r1s")
           apply(auto)
     apply(metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(24) inc_i word_prev_def le_minus min.absorb_iff1 word_le_sub1 word_zero_le)
    apply(metis inc_le word_next_def max.order_iff)
  done

  declare bitrange_intersection.simps[simp del]
  declare bitrange_setminus.simps(1)[simp del]

  lemma bitrange_setminus_intersection_empty_struct:
    "bitrange_empty (bitrange_intersection r1 r2) \<Longrightarrow> 
    bitrange_setminus r1 r2 = r1"
    by (induction r1 r2 rule: bitrange_setminus.induct, auto simp add: bitrange_setminus_intersection_empty_struct_rr) fastforce

  definition bitrange_subset :: "'a::len bitrange \<Rightarrow> 'a::len bitrange \<Rightarrow> bool" where
    "bitrange_subset r1 r2 \<equiv> bitrange_empty (bitrange_setminus r1 r2)"
  lemma bitrange_subset_set_eq[simp]: "bitrange_subset r1 r2 = (bitrange_to_set r1 \<subseteq> bitrange_to_set r2)"
    unfolding bitrange_subset_def by simp

  definition bitrange_eq :: "'a::len bitrange \<Rightarrow> 'a::len bitrange \<Rightarrow> bool" where 
    "bitrange_eq r1 r2 = (bitrange_subset r1 r2 \<and> bitrange_subset r2 r1)"
  lemma bitrange_eq_set_eq: "bitrange_eq r1 r2 \<longleftrightarrow> bitrange_to_set r1 = bitrange_to_set r2"
    unfolding bitrange_eq_def by auto
  thm iffD1[OF bitrange_eq_set_eq]
  declare iffD1[OF bitrange_eq_set_eq, simp]
  lemma bitrange_eq_comm: "bitrange_eq r1 r2 \<longleftrightarrow> bitrange_eq r2 r1"
    unfolding bitrange_eq_def by fast
  lemma bitrange_to_set_alt: "bitrange_to_set r = {x. bitrange_element x r}"
    unfolding bitrange_element_set_eq by blast
 
  lemma bitrange_un_empty: "bitrange_empty r1 \<Longrightarrow> bitrange_eq (bitrange_union r1 r2) r2"
    by(subst bitrange_eq_set_eq, simp)
  lemma bitrange_un_emty_b: "bitrange_empty r2 \<Longrightarrow> bitrange_eq (bitrange_union r1 r2) r1"
    by(subst bitrange_eq_set_eq, simp)
  
  lemma bitrange_Diff_triv: 
    assumes "bitrange_empty (bitrange_intersection a b)" shows "bitrange_eq (bitrange_setminus a b) a"
    using bitrange_setminus_intersection_empty_struct[OF assms] bitrange_eq_set_eq[of a a] by simp

  fun bitrange_size where
    "bitrange_size (RangeUnion a b) = bitrange_size a + bitrange_size b" |
    "bitrange_size (Bitrange s e) = (if s \<le> e then 1 else 0)"
  lemma "bitrange_size r = length (bitrange_to_list r)"
    by(induction r, simp_all)

  lemma [simp]: "\<exists>x::('a::len bitrange). y \<in> bitrange_to_set x"
  proof show "y \<in> bitrange_to_set bitrange_UNIV" by simp qed





  lemma bitrange_eq_reflp:
    "reflp bitrange_eq"
    apply(rule reflpI)
    by(simp only: bitrange_eq_set_eq)
  lemma bitranget_eq_symp:
    "symp bitrange_eq"
    apply(rule sympI)
    by(simp add: bitrange_eq_comm)
  lemma bitrange_eq_transp:
    "transp bitrange_eq"
    apply(rule transpI)
    by(simp only: bitrange_eq_set_eq)

  lemma bitrange_eq_equivp:
    "equivp bitrange_eq"
    by (auto intro: equivpI bitrange_eq_reflp bitranget_eq_symp bitrange_eq_transp)
(*
  quotient_type 'a bitrrq = "'a::len bitrange" / "bitrange_eq"
    by (rule bitrange_eq_equivp)
*)
    
end
