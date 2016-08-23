theory Normalized_Matches
imports Fixed_Action
begin

section\<open>Normalized (DNF) matches\<close>

text\<open>simplify a match expression. The output is a list of match exprissions, the semantics is @{text "\<or>"} of the list elements.\<close>
fun normalize_match :: "'a match_expr \<Rightarrow> 'a match_expr list" where
  "normalize_match (MatchAny) = [MatchAny]" |
  "normalize_match (Match m) = [Match m]" |
  "normalize_match (MatchAnd m1 m2) = [MatchAnd x y. x <- normalize_match m1, y <- normalize_match m2]" |
  "normalize_match (MatchNot (MatchAnd m1 m2)) = normalize_match (MatchNot m1) @ normalize_match (MatchNot m2)" | (*DeMorgan*)
  "normalize_match (MatchNot (MatchNot m)) = normalize_match m" | (*idem*)
  "normalize_match (MatchNot (MatchAny)) = []" | (*false*)
  "normalize_match (MatchNot (Match m)) = [MatchNot (Match m)]"


lemma normalize_match_not_matcheq_matchNone: "\<forall>m' \<in> set (normalize_match m). \<not> matcheq_matchNone m'"
  proof(induction m rule: normalize_match.induct)
  case 4 thus ?case by (simp) blast
  qed(simp_all)
 
lemma normalize_match_empty_iff_matcheq_matchNone: "normalize_match m = [] \<longleftrightarrow> matcheq_matchNone m "
  proof(induction m rule: normalize_match.induct) 
  case 3 thus ?case  by (simp) fastforce
  qed(simp_all)

lemma match_list_normalize_match: "match_list \<gamma> [m] a p \<longleftrightarrow> match_list \<gamma> (normalize_match m) a p"
  proof(induction m rule:normalize_match.induct)
  case 1 thus ?case by(simp add: match_list_singleton)
  next
  case 2 thus ?case by(simp add: match_list_singleton)
  next
  case (3 m1 m2) thus ?case 
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    apply(case_tac "matches \<gamma> m1 a p")
     apply(rule matches_list_And_concat)
      apply(simp)
     apply(case_tac "(normalize_match m1)")
      apply simp
     apply (auto)[1]
    apply(simp add: bunch_of_lemmata_about_matches match_list_helper)
    done
  next
  case 4 thus ?case 
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    apply(simp add: match_list_append)
    apply(safe)
        apply(simp_all add: matches_DeMorgan)
    done
  next 
  case 5 thus ?case 
    by(simp add: match_list_singleton bunch_of_lemmata_about_matches)
  next
  case 6 thus ?case 
    by(simp add: match_list_singleton bunch_of_lemmata_about_matches)
  next
  case 7 thus ?case by(simp add: match_list_singleton)
qed
  
thm match_list_normalize_match[simplified match_list_singleton]


theorem normalize_match_correct: "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (normalize_match m)) s = approximating_bigstep_fun \<gamma> p [Rule m a] s"
apply(rule match_list_semantics[of _ _ _ _ "[m]", simplified])
using match_list_normalize_match by fastforce


lemma normalize_match_empty: "normalize_match m = [] \<Longrightarrow> \<not> matches \<gamma> m a p"
  proof(induction m rule: normalize_match.induct)
  case 3 thus ?case by(fastforce dest: matches_dest)
  next
  case 4 thus ?case using match_list_normalize_match by (simp add: matches_DeMorgan)
  next
  case 5 thus ?case using matches_not_idem by fastforce
  next
  case 6 thus ?case by(simp add: bunch_of_lemmata_about_matches)
  qed(simp_all)


lemma matches_to_match_list_normalize: "matches \<gamma> m a p = match_list \<gamma> (normalize_match m) a p"
  using match_list_normalize_match[simplified match_list_singleton] .

lemma wf_ruleset_normalize_match: "wf_ruleset \<gamma> p [(Rule m a)] \<Longrightarrow> wf_ruleset \<gamma> p (map (\<lambda>m. Rule m a) (normalize_match m))"
proof(induction m rule: normalize_match.induct)
  case 1 thus ?case by simp
  next
  case 2 thus ?case by simp
  next
  case 3 thus ?case by(simp add: fixedaction_wf_ruleset wf_ruleset_singleton matches_to_match_list_normalize)
  next
  case 4 thus ?case 
    apply(simp add: wf_ruleset_append)
    apply(simp add: fixedaction_wf_ruleset)
    apply(unfold wf_ruleset_singleton)
    apply(safe) (*there is a simpler way but the simplifier takes for ever if we just apply it here, ...*)
           apply(simp_all add: matches_to_match_list_normalize)
         apply(simp_all add: match_list_append)
    done
  next
  case 5 thus ?case by(simp add: wf_ruleset_singleton matches_to_match_list_normalize)
  next
  case 6 thus ?case by(simp add: wf_ruleset_def)
  next
  case 7 thus ?case by(simp_all add: wf_ruleset_append)
  qed


lemma normalize_match_wf_ruleset: "wf_ruleset \<gamma> p (map (\<lambda>m. Rule m a) (normalize_match m)) \<Longrightarrow> wf_ruleset \<gamma> p [Rule m a]"
proof(induction m rule: normalize_match.induct)
  case 1 thus ?case by simp
  next
  case 2 thus ?case by simp
  next
  case 3 thus ?case by(simp add: fixedaction_wf_ruleset wf_ruleset_singleton matches_to_match_list_normalize)
  next
  case 4 thus ?case 
    apply(simp add: wf_ruleset_append)
    apply(simp add: fixedaction_wf_ruleset)
    apply(unfold wf_ruleset_singleton)
    apply(safe)
         apply(simp_all add: matches_to_match_list_normalize)
         apply(simp_all add: match_list_append)
    done
  next
  case 5 thus ?case 
    unfolding wf_ruleset_singleton by(simp add: matches_to_match_list_normalize)
  next
  case 6 thus ?case unfolding wf_ruleset_singleton by(simp add: bunch_of_lemmata_about_matches)
  next
  case 7 thus ?case by(simp add: wf_ruleset_append)
  qed


lemma good_ruleset_normalize_match: "good_ruleset [(Rule m a)] \<Longrightarrow> good_ruleset (map (\<lambda>m. Rule m a) (normalize_match m))"
by(simp add: good_ruleset_def)

section\<open>Normalizing rules instead of only match expressions\<close>
  fun normalize_rules :: "('a match_expr \<Rightarrow> 'a match_expr list) \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
    "normalize_rules _ [] = []" |
    "normalize_rules f ((Rule m a)#rs) = (map (\<lambda>m. Rule m a) (f m))@(normalize_rules f rs)"
  
  lemma normalize_rules_singleton: "normalize_rules f [Rule m a] = map (\<lambda>m. Rule m a) (f m)" by(simp)
  lemma normalize_rules_fst: "(normalize_rules f (r # rs)) = (normalize_rules f [r]) @ (normalize_rules f rs)"
    by(cases r) (simp)

  lemma normalize_rules_concat_map:
    "normalize_rules f rs = concat (map (\<lambda>r. map (\<lambda>m. Rule m (get_action r)) (f (get_match r))) rs)"
    apply(induction rs)
     apply(simp_all)
    apply(rename_tac r rs, case_tac r)
    apply(simp)
    done

  lemma good_ruleset_normalize_rules: "good_ruleset rs \<Longrightarrow> good_ruleset (normalize_rules f rs)"
    proof(induction rs)
    case Nil thus ?case by (simp)
    next
    case(Cons r rs)
      from Cons have IH: "good_ruleset (normalize_rules f rs)" using good_ruleset_tail by blast
      from Cons.prems have "good_ruleset [r]" using good_ruleset_fst by fast
      hence "good_ruleset (normalize_rules f [r])" by(cases r) (simp add: good_ruleset_alt)
      with IH good_ruleset_append have "good_ruleset (normalize_rules f [r] @ normalize_rules f rs)" by blast
      thus ?case using normalize_rules_fst by metis
    qed

  lemma simple_ruleset_normalize_rules: "simple_ruleset rs \<Longrightarrow> simple_ruleset (normalize_rules f rs)"
    proof(induction rs)
    case Nil thus ?case by (simp)
    next
    case(Cons r rs)
      from Cons have IH: "simple_ruleset (normalize_rules f rs)" using simple_ruleset_tail by blast
      from Cons.prems have "simple_ruleset [r]" using simple_ruleset_append by fastforce
      hence "simple_ruleset (normalize_rules f [r])" by(cases r) (simp add: simple_ruleset_def) 
      with IH simple_ruleset_append have  "simple_ruleset (normalize_rules f [r] @ normalize_rules f rs)" by blast
      thus ?case using normalize_rules_fst by metis
    qed
    

  (*tuned version of the next lemma for usage with normalize_primitive_extract where P=normalized_nnf_match*)
  lemma normalize_rules_match_list_semantics_3: 
    assumes "\<forall>m a. P m \<longrightarrow> match_list \<gamma> (f m) a p = matches \<gamma> m a p"
    and "simple_ruleset rs"
    and P: "\<forall> r \<in> set rs. P (get_match r)"
    shows "approximating_bigstep_fun \<gamma> p (normalize_rules f rs) s = approximating_bigstep_fun \<gamma> p rs s"
    proof -
      have assm_1: "\<forall>r\<in>set rs. match_list \<gamma> (f (get_match r)) (get_action r) p = matches \<gamma> (get_match r) (get_action r) p" using P assms(1) by blast
      { fix r s
        assume "r \<in> set rs"
        with assm_1 have "match_list \<gamma> (f (get_match r)) (get_action r) p \<longleftrightarrow> match_list \<gamma> [(get_match r)] (get_action r) p" by simp
        with match_list_semantics[of \<gamma> "f (get_match r)" "(get_action r)" p "[(get_match r)]"] have
          "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m (get_action r)) (f (get_match r))) s = 
           approximating_bigstep_fun \<gamma> p [Rule (get_match r) (get_action r)] s" by simp
        hence "(approximating_bigstep_fun \<gamma> p (normalize_rules f [r]) s) = approximating_bigstep_fun \<gamma> p [r] s"
          by(cases r) (simp)
      }
  
    with assms show ?thesis
      proof(induction rs arbitrary: s)
        case Nil thus ?case by (simp)
      next
        case (Cons r rs)
        from Cons.prems have "simple_ruleset [r]" by(simp add: simple_ruleset_def)
        with simple_imp_good_ruleset good_imp_wf_ruleset have wf_r: "wf_ruleset \<gamma> p [r]" by fast
  
        from \<open>simple_ruleset [r]\<close> simple_imp_good_ruleset good_imp_wf_ruleset have wf_r: 
          "wf_ruleset \<gamma> p [r]" by fast
        from simple_ruleset_normalize_rules[OF \<open>simple_ruleset [r]\<close>] have "simple_ruleset (normalize_rules f [r])"
          by(simp) 
        with simple_imp_good_ruleset good_imp_wf_ruleset have wf_nr: "wf_ruleset \<gamma> p (normalize_rules f [r])" by fast
  
        from Cons have IH: "\<And>s. approximating_bigstep_fun \<gamma> p (normalize_rules f rs) s = approximating_bigstep_fun \<gamma> p rs s"
          using simple_ruleset_tail by force
        
        from Cons have a: "\<And>s. approximating_bigstep_fun \<gamma> p (normalize_rules f [r]) s = approximating_bigstep_fun \<gamma> p [r] s" by simp

        show ?case
          apply(subst normalize_rules_fst)
          apply(simp add: approximating_bigstep_fun_seq_wf[OF wf_nr])
          apply(subst approximating_bigstep_fun_seq_wf[OF wf_r, simplified])
          apply(simp add: a)
          apply(simp add: IH)  
          done
      qed
    qed

 corollary normalize_rules_match_list_semantics: 
  "(\<forall>m a. match_list \<gamma> (f m) a p = matches \<gamma> m a p) \<Longrightarrow> simple_ruleset rs \<Longrightarrow>
   approximating_bigstep_fun \<gamma> p (normalize_rules f rs) s = approximating_bigstep_fun \<gamma> p rs s"
  apply(rule normalize_rules_match_list_semantics_3[where P="\<lambda>_. True"])
    using assms by(simp_all)

lemma in_normalized_matches: "ls \<in> set (normalize_match m) \<and> matches \<gamma> ls a p \<Longrightarrow> matches \<gamma> m a p"
  by (meson match_list_matches matches_to_match_list_normalize)

 text\<open>applying a function (with a prerequisite @{text Q}) to all rules\<close>
 lemma normalize_rules_property:
 assumes "\<forall> r \<in> set rs. P (get_match r)"
     and "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (f m). Q m')"
  shows "\<forall>r \<in> set (normalize_rules f rs). Q (get_match r)"
  proof
    fix r' assume a: "r' \<in> set (normalize_rules f rs)"
    from a assms show "Q (get_match r')"
    proof(induction rs)
    case Nil thus ?case by simp
    next
    case (Cons r rs)
      { 
        assume "r' \<in> set (normalize_rules f rs)"
        from Cons.IH this have "Q (get_match r')" using Cons.prems(2) Cons.prems(3) by fastforce
      } note 1=this
      { 
        assume "r' \<in> set (normalize_rules f [r])"
        hence a: "(get_match r') \<in> set (f (get_match r))" by(cases r) (auto)
        with Cons.prems(2) Cons.prems(3) have "\<forall>m'\<in>set (f (get_match r)). Q m'" by auto
        with a have "Q (get_match r')" by blast
      } note 2=this
      from Cons.prems(1) have "r' \<in> set (normalize_rules f [r]) \<or> r' \<in> set (normalize_rules f rs)"
        by(subst(asm) normalize_rules_fst) auto
      with 1 2 show ?case
        by(elim disjE)(simp)
    qed
 qed

 text\<open>If a function @{text f} preserves some property of the match expressions, then this property is preserved when applying @{const normalize_rules}\<close>

 lemma normalize_rules_preserves: assumes "\<forall> r \<in> set rs. P (get_match r)"
     and "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (f m). P m')"
  shows "\<forall>r \<in> set (normalize_rules f rs). P (get_match r)"
  using normalize_rules_property[OF assms(1) assms(2)] by simp

fun normalize_rules_dnf :: "'a rule list \<Rightarrow> 'a rule list" where
  "normalize_rules_dnf [] = []" |
  "normalize_rules_dnf ((Rule m a)#rs) = (map (\<lambda>m. Rule m a) (normalize_match m))@(normalize_rules_dnf rs)"

lemma normalize_rules_dnf_append: "normalize_rules_dnf (rs1@rs2) = normalize_rules_dnf rs1 @ normalize_rules_dnf rs2"
  proof(induction rs1 rule: normalize_rules_dnf.induct)
  qed(simp_all)

lemma normalize_rules_dnf_def2: "normalize_rules_dnf = normalize_rules normalize_match"
  proof(simp add: fun_eq_iff, intro allI)
    fix x::"'a rule list" show "normalize_rules_dnf x = normalize_rules normalize_match x"
    proof(induction x)
    case (Cons r rs) thus ?case by (cases r) simp
    qed(simp)
  qed

lemma wf_ruleset_normalize_rules_dnf: "wf_ruleset \<gamma> p rs \<Longrightarrow> wf_ruleset \<gamma> p (normalize_rules_dnf rs)"
  proof(induction rs)
  case Nil thus ?case by simp
  next
  case(Cons r rs)
    from Cons have IH: "wf_ruleset \<gamma> p (normalize_rules_dnf rs)" by(auto dest: wf_rulesetD) 
    from Cons.prems have "wf_ruleset \<gamma> p [r]" by(auto dest: wf_rulesetD) 
    hence "wf_ruleset \<gamma> p (normalize_rules_dnf [r])" using wf_ruleset_normalize_match by(cases r) simp
    with IH wf_ruleset_append have "wf_ruleset \<gamma> p (normalize_rules_dnf [r] @ normalize_rules_dnf rs)" by fast
    thus ?case using normalize_rules_dnf_def2 normalize_rules_fst by metis
  qed

lemma good_ruleset_normalize_rules_dnf: "good_ruleset rs \<Longrightarrow> good_ruleset (normalize_rules_dnf rs)"
  using normalize_rules_dnf_def2 good_ruleset_normalize_rules by metis

lemma simple_ruleset_normalize_rules_dnf: "simple_ruleset rs \<Longrightarrow> simple_ruleset (normalize_rules_dnf rs)"
  using normalize_rules_dnf_def2 simple_ruleset_normalize_rules by metis


(*This is the simple correctness proof, using the generalized version.
  below, we have a more complex correctness proof with a slighter generic assumption.
  Probably, we can delete the complex proof when we only focus on simple rulesets
  *)
lemma "simple_ruleset rs \<Longrightarrow> 
  approximating_bigstep_fun \<gamma> p (normalize_rules_dnf rs) s = approximating_bigstep_fun \<gamma> p rs s"
  unfolding normalize_rules_dnf_def2
  apply(rule normalize_rules_match_list_semantics)
   apply (metis matches_to_match_list_normalize)
  by simp
  
lemma normalize_rules_dnf_correct: "wf_ruleset \<gamma> p rs \<Longrightarrow> 
  approximating_bigstep_fun \<gamma> p (normalize_rules_dnf rs) s = approximating_bigstep_fun \<gamma> p rs s"
  proof(induction rs)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    show ?case
    proof(induction s rule: just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
    case Undecided
    from Cons wf_rulesetD(2) have IH: "approximating_bigstep_fun \<gamma> p (normalize_rules_dnf rs) s = approximating_bigstep_fun \<gamma> p rs s" by fast
    from Cons.prems have "wf_ruleset \<gamma> p [r]" and "wf_ruleset \<gamma> p (normalize_rules_dnf [r])"
      by(auto dest: wf_rulesetD simp: wf_ruleset_normalize_rules_dnf)
    with IH Undecided have
      "approximating_bigstep_fun \<gamma> p (normalize_rules_dnf rs) (approximating_bigstep_fun \<gamma> p (normalize_rules_dnf [r]) Undecided) = approximating_bigstep_fun \<gamma> p (r # rs) Undecided"
      apply(cases r, rename_tac m a)
      apply(simp)
      apply(case_tac a)
              apply(simp_all add: normalize_match_correct Decision_approximating_bigstep_fun wf_ruleset_singleton)
      done
    hence "approximating_bigstep_fun \<gamma> p (normalize_rules_dnf [r] @ normalize_rules_dnf rs) s = approximating_bigstep_fun \<gamma> p (r # rs) s"
      using Undecided \<open>wf_ruleset \<gamma> p [r]\<close> \<open>wf_ruleset \<gamma> p (normalize_rules_dnf [r])\<close> 
      by(simp add: approximating_bigstep_fun_seq_wf)
    thus ?thesis using normalize_rules_fst normalize_rules_dnf_def2 by metis
    qed
  qed


fun normalized_nnf_match :: "'a match_expr \<Rightarrow> bool" where
  "normalized_nnf_match MatchAny = True" |
  "normalized_nnf_match (Match _ ) = True" |
  "normalized_nnf_match (MatchNot (Match _)) = True" |
  "normalized_nnf_match (MatchAnd m1 m2) = ((normalized_nnf_match m1) \<and> (normalized_nnf_match m2))" |
  "normalized_nnf_match _ = False"


text\<open>Essentially, @{term normalized_nnf_match} checks for a negation normal form: Only AND is at toplevel, negation only occurs in front of literals.
 Since @{typ "'a match_expr"} does not support OR, the result is in conjunction normal form.
 Applying @{const normalize_match}, the reuslt is a list. Essentially, this is the disjunctive normal form.\<close>

lemma normalize_match_already_normalized: "normalized_nnf_match m \<Longrightarrow> normalize_match m = [m]"
  by(induction m rule: normalize_match.induct) (simp)+

lemma normalized_nnf_match_normalize_match: "\<forall> m' \<in> set (normalize_match m). normalized_nnf_match m'"
  proof(induction m arbitrary: rule: normalize_match.induct)
  case 4 thus ?case by fastforce
  qed (simp_all)


lemma normalized_nnf_match_MatchNot_D: "normalized_nnf_match (MatchNot m) \<Longrightarrow> normalized_nnf_match m"
  by(induction m) (simp_all)


text\<open>Example\<close>
lemma "normalize_match (MatchNot (MatchAnd (Match ip_src) (Match tcp))) = [MatchNot (Match ip_src), MatchNot (Match tcp)]" by simp



subsection\<open>Functions which preserve @{const normalized_nnf_match}\<close>

lemma optimize_matches_option_normalized_nnf_match: "(\<And> r. r \<in> set rs \<Longrightarrow> normalized_nnf_match (get_match r)) \<Longrightarrow>
     (\<And>m m'. normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m') \<Longrightarrow>
      \<forall> r \<in> set (optimize_matches_option f rs). normalized_nnf_match (get_match r)"
    proof(induction rs)
      case Nil thus ?case by simp
    next
      case (Cons r rs)
      from Cons.IH Cons.prems have IH: "\<forall>r\<in>set (optimize_matches_option f rs). normalized_nnf_match (get_match r)" by simp
      from Cons.prems have "\<forall>r\<in>set (optimize_matches_option f [r]). normalized_nnf_match (get_match r)"
        apply(cases r)
        apply(simp split: option.split)
        by force (*1s*)
      with IH show ?case by(cases r, simp split: option.split_asm)
    qed



lemma optimize_matches_normalized_nnf_match: "\<lbrakk>\<forall> r \<in> set rs. normalized_nnf_match (get_match r); \<forall>m. normalized_nnf_match m \<longrightarrow> normalized_nnf_match (f m) \<rbrakk> \<Longrightarrow>
      \<forall> r \<in> set (optimize_matches f rs). normalized_nnf_match (get_match r)"
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_normalized_nnf_match)
   apply(simp; fail)
  apply(simp split: split_if_asm)
  by blast


lemma normalize_rules_dnf_normalized_nnf_match: "\<forall>x \<in> set (normalize_rules_dnf rs). normalized_nnf_match (get_match x)"
  proof(induction rs)
  case Nil thus ?case by simp
  next
  case (Cons r rs) thus ?case using normalized_nnf_match_normalize_match by(cases r) fastforce
  qed

end