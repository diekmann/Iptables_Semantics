theory Word_Upto
imports Main
  Hs_Compat
  "./l4v/lib/Word_Lib/Word_Lemmas"
begin

function word_upto :: "'a word \<Rightarrow> 'a word \<Rightarrow> ('a::len0) word list" where
"word_upto a b = (if a = b then [a] else word_upto a (b - 1) @ [b])"
by auto

termination word_upto
apply(relation "measure (unat \<circ> uncurry (op -) \<circ> prod.swap)")
apply(rule wf_measure)
apply(unfold in_measure)
apply(unfold comp_def)
apply(simp)
apply(subgoal_tac "unat (b - a - 1) < unat (b - a)")
apply(simp add: diff_right_commute)
apply(rule measure_unat)
apply auto
done

declare word_upto.simps[simp del]

(* Most of the lemmas I show about word_upto hold without a \<le> b, but I don't need that right now and it's giving me a headache *)

lemma word_upto_set_eq2: "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<Longrightarrow> a \<le> x \<and> x \<le> b"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst(asm) word_upto.simps)
apply(simp)
apply(subst(asm) word_upto.simps)
apply(simp)
apply(erule disjE)
apply simp
proof -
       case goal1
       from goal1(2-3) have "b \<noteq> 0" by force
       from goal1(2,3) have "a \<le> b - 1" by (metis `b \<noteq> 0` le_step_down_nat order_class.order.antisym unat_minus_one word_le_nat_alt) 
       from goal1(1)[OF this goal1(4)] show ?case by (metis dual_order.trans goal1(2) goal1(3) less_imp_le measure_unat word_le_0_iff word_le_nat_alt)
qed

lemma word_upto_set_eq3: "a \<le> x \<and> x \<le> b \<Longrightarrow> x \<in> set (word_upto a b)"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst word_upto.simps)
apply(simp; force)
apply(subst word_upto.simps)
apply(simp)
apply(case_tac "x = b")
apply(simp;fail)
proof -
       case goal1
       from goal1(2-4) have "b \<noteq> 0" by force
       from goal1(2,4) have "x \<le> b - 1" by (metis `b \<noteq> 0` dual_order.antisym le_step_down_nat unat_minus_one word_le_nat_alt) 
       from goal1(1) this show ?case by simp
qed

lemma word_upto_set_eq: "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<longleftrightarrow> a \<le> x \<and> x \<le> b"
       using word_upto_set_eq3 word_upto_set_eq2 by metis

lemma word_upto_distinct_hlp: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<notin> set (word_upto a (b - 1))"
       apply(rule ccontr, unfold not_not)
       apply(subgoal_tac "a \<le> b - 1")
        apply(drule word_upto_set_eq2[of a "b -1" b])
         apply(simp add: word_upto.simps; fail)
        apply(subgoal_tac "b \<noteq> 0")
         apply(meson leD measure_unat word_le_nat_alt)
        apply(blast intro: iffD1[OF word_le_0_iff])
       apply(metis antisym_conv le_step_down_nat unat_minus_one word_le_0_iff word_le_nat_alt)
done

lemma distinct_word_upto: "a \<le> b \<Longrightarrow> distinct (word_upto a b)"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst word_upto.simps)
apply(simp; force)
apply(subst word_upto.simps)
apply(case_tac "a \<le> b - 1")
apply(simp)
apply(rule word_upto_distinct_hlp;simp_all;fail)
apply(simp)
apply(rule ccontr)
apply(metis le_step_down_nat less_le not_le unat_minus_one word_le_nat_alt word_not_simps(1))
done

(*abbreviation "word_of_nat \<equiv> of_nat :: nat \<Rightarrow> ('l :: len) word"*)
lemma word_upto_eq_upto: "s \<le> e \<Longrightarrow> e \<le> unat (max_word :: 'l word) \<Longrightarrow>
       word_upto ((of_nat :: nat \<Rightarrow> ('l :: len) word) s) (of_nat e) = map of_nat (upt s (Suc e))"
proof(induction e)
       let ?mwon = "of_nat :: nat \<Rightarrow> 'l word"
       let ?mmw = "max_word :: 'l word"
       case (Suc e)
       show ?case
       proof(cases "?mwon s = ?mwon (Suc e)")
               case True
               have "s = Suc e" using le_unat_uoi Suc.prems True by metis
               with True show ?thesis by(subst word_upto.simps) (simp)
       next
               case False 
               hence le: "s \<le> e" using le_SucE Suc.prems by blast
               have lm: "e \<le> unat ?mmw" using Suc.prems by simp
               have sucm: "(of_nat :: nat \<Rightarrow> ('l :: len) word) (Suc e) - 1 = of_nat e" using Suc.prems(2) by simp
               note mIH = Suc.IH[OF le lm]
               show ?thesis by(subst word_upto.simps) (simp add: False[simplified] Suc.prems mIH sucm)
       qed
qed(simp add: word_upto.simps)

lemma word_upto_alt: "(a :: ('l :: len) word) \<le> b \<Longrightarrow> word_upto a b = map of_nat (upt (unat a) (Suc (unat b)))"
proof -
       let ?mmw = "max_word :: 'l word"
       assume le: "a \<le> b"
       hence nle: "unat a \<le> unat b" by(unat_arith)
       have lem: "unat b \<le> unat ?mmw" by (simp add: word_unat_less_le) 
       note word_upto_eq_upto[OF nle lem, unfolded word_unat.Rep_inverse]
       thus "word_upto a b = map of_nat [unat a..<Suc (unat b)]" .
qed

definition "stop_word_upto_unfold = word_upto"
lemma [code_unfold]: "word_upto a b = (if a \<le> b then map of_nat (upt (unat a) (Suc (unat b))) else stop_word_upto_unfold a b)"
       using word_upto_alt stop_word_upto_unfold_def by metis
value[code] "word_upto (3 :: 16 word) 5"
(* TODO: Does this break something? *)

lemma sorted_word_upto:
       fixes a b :: "('l :: len) word"
       assumes "a \<le> b"
       shows "sorted (word_upto a b)"
using assms
proof(induction b)
       fix b
       assume le_prem: "a \<le> 1 + b"
       assume nmax_prem: "1 + b \<noteq> 0"
    assume IH: "a \<le> b \<Longrightarrow> sorted (word_upto a b)"
       show "sorted (word_upto a (1 + b))" proof(cases "a = 1 + b")
               case True thus ?thesis by(simp add: word_upto.simps)
       next
               case False
               have fprem: "a \<le> b" using le_prem False by (metis add.commute antisym_conv1 plus_one_helper)
               note mIH = IH[OF this]
               show ?thesis by(subst word_upto.simps)
                       (simp add: fprem lt1_neq0 nmax_prem word_le_plus_either word_upto_set_eq False sorted_append mIH)
       qed
qed(simp add: word_upto.simps)
end
