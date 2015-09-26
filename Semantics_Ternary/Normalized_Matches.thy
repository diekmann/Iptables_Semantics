theory Normalized_Matches
imports Fixed_Action
begin

section{*Normalized (DNF) matches*}

text{*simplify a match expression. The output is a list of match exprissions, the semantics is @{text "\<or>"} of the list elements.*}
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
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    apply (metis matches_not_idem)
    done
  next
  case 6 thus ?case 
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    by (metis bunch_of_lemmata_about_matches(3))
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
  case 6 thus ?case unfolding wf_ruleset_singleton using bunch_of_lemmata_about_matches(3) by metis
  next
  case 7 thus ?case by(simp_all add: wf_ruleset_append)
  qed


lemma good_ruleset_normalize_match: "good_ruleset [(Rule m a)] \<Longrightarrow> good_ruleset (map (\<lambda>m. Rule m a) (normalize_match m))"
by(simp add: good_ruleset_def)

section{*Normalizing rules instead of only match expressions*}
  fun normalize_rules :: "('a match_expr \<Rightarrow> 'a match_expr list) \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
    "normalize_rules _ [] = []" |
    "normalize_rules f ((Rule m a)#rs) = (map (\<lambda>m. Rule m a) (f m))@(normalize_rules f rs)"
  
  lemma normalize_rules_singleton: "normalize_rules f [Rule m a] = map (\<lambda>m. Rule m a) (f m)" by(simp)
  lemma normalize_rules_fst: "(normalize_rules f (r # rs)) = (normalize_rules f [r]) @ (normalize_rules f rs)"
    by(cases r) (simp)


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
    and P: "\<forall> m \<in> get_match ` set rs. P m"
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
  
        from `simple_ruleset [r]` simple_imp_good_ruleset good_imp_wf_ruleset have wf_r: 
          "wf_ruleset \<gamma> p [r]" by fast
        from simple_ruleset_normalize_rules[OF `simple_ruleset [r]`] have "simple_ruleset (normalize_rules f [r])"
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


 text{*applying a function (with a prerequisite @{text Q}) to all rules*}
 lemma normalize_rules_property:
 assumes "\<forall> m \<in> get_match ` set rs. P m"
     and "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (f m). Q m')"
  shows "\<forall>m \<in> get_match ` set (normalize_rules f rs). Q m"
  proof
    fix m assume a: "m \<in> get_match ` set (normalize_rules f rs)"
    from a assms show "Q m"
    proof(induction rs)
    case Nil thus ?case by simp
    next
    case (Cons r rs)
      {
        assume "m \<in> get_match ` set (normalize_rules f rs)"
        from Cons.IH this have "Q m" using Cons.prems(2) Cons.prems(3) by fastforce
      } note 1=this
      {
        assume "m \<in> get_match ` set (normalize_rules f [r])"
        hence a: "m \<in> set (f (get_match r))" by(cases r) (auto)
        with Cons.prems(2) Cons.prems(3) have "\<forall>m'\<in>set (f (get_match r)). Q m'" by auto
        with a have "Q m" by blast
      } note 2=this
      from Cons.prems(1) have "m \<in> get_match ` set (normalize_rules f [r]) \<or> m \<in> get_match ` set (normalize_rules f rs)"
        by(subst(asm) normalize_rules_fst) auto
      with 1 2 show ?case
        by(elim disjE)(simp)
    qed
 qed

 text{*If a function @{text f} preserves some property of the match expressions, then this property is preserved when applying @{const normalize_rules}*}
 lemma normalize_rules_preserves: assumes "\<forall> m \<in> get_match ` set rs. P m"
     and "\<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (f m). P m')"
  shows "\<forall>m \<in> get_match ` set (normalize_rules f rs). P m"
  using normalize_rules_property[OF assms(1) assms(2)] .

 (*the simplifier preferes this*)
 lemma normalize_rules_preserves': "\<forall> m \<in> set rs. P (get_match m) \<Longrightarrow> \<forall>m. P m \<longrightarrow> (\<forall>m' \<in> set (f m). P m') \<Longrightarrow> \<forall>m \<in> set (normalize_rules f rs). P (get_match m)"
  using normalize_rules_preserves[simplified] by blast

(*TODO: generalize!*)
fun normalize_rules_dnf :: "'a rule list \<Rightarrow> 'a rule list" where
  "normalize_rules_dnf [] = []" |
  "normalize_rules_dnf ((Rule m a)#rs) = (map (\<lambda>m. Rule m a) (normalize_match m))@(normalize_rules_dnf rs)"

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
      using Undecided `wf_ruleset \<gamma> p [r]` `wf_ruleset \<gamma> p (normalize_rules_dnf [r])` 
      by(simp add: approximating_bigstep_fun_seq_wf)
    thus ?thesis using normalize_rules_fst normalize_rules_dnf_def2 by metis
    qed
  qed

(*
value "normalize_rules_dnf
  [(Rule (MatchNot (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16)))) (MatchAnd (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) (MatchAnd (Match (Prot ipt_protocol.ProtTCP)) (Match (Extra ''reject-with tcp-reset'')))))) Drop)]
 "
*)

fun normalized_nnf_match :: "'a match_expr \<Rightarrow> bool" where
  "normalized_nnf_match MatchAny = True" |
  "normalized_nnf_match (Match _ ) = True" |
  "normalized_nnf_match (MatchNot (Match _)) = True" |
  "normalized_nnf_match (MatchAnd m1 m2) = ((normalized_nnf_match m1) \<and> (normalized_nnf_match m2))" |
  "normalized_nnf_match _ = False"


text{*Essentially, @{term normalized_nnf_match} checks for a negation normal form: Only AND is at toplevel, negation only occurs in front of literals.
 Since @{typ "'a match_expr"} does not support OR, the result is in conjunction normal form.
 Applying @{const normalize_match}, the reuslt is a list. Essentially, this is the disjunctive normal form.*}


lemma normalized_nnf_match_normalize_match: "\<forall> m' \<in> set (normalize_match m). normalized_nnf_match m'"
  proof(induction m arbitrary: rule: normalize_match.induct)
  case 4 thus ?case by fastforce
  qed (simp_all)


lemma normalized_nnf_match_MatchNot_D: "normalized_nnf_match (MatchNot m) \<Longrightarrow> normalized_nnf_match m"
  by(induction m) (simp_all)


text{*Example*}
lemma "normalize_match (MatchNot (MatchAnd (Match ip_src) (Match tcp))) = [MatchNot (Match ip_src), MatchNot (Match tcp)]" by simp



subsection{*Functions which preserve @{const normalized_nnf_match}*}

(* TODO: this is the place to collect functions that maintain the normalized structure *)
lemma optimize_matches_normalized_nnf_match: "\<lbrakk>\<forall> r \<in> set rs. normalized_nnf_match (get_match r); \<forall>m. normalized_nnf_match m \<longrightarrow> normalized_nnf_match (f m) \<rbrakk> \<Longrightarrow>
      \<forall> r \<in> set (optimize_matches f rs). normalized_nnf_match (get_match r)"
    proof(induction rs)
      case Nil thus ?case unfolding optimize_matches_def by simp
    next
      case (Cons r rs)
      from Cons.IH Cons.prems have IH: "\<forall>r\<in>set (optimize_matches f rs). normalized_nnf_match (get_match r)" by simp
      from Cons.prems have "\<forall>r\<in>set (optimize_matches f [r]). normalized_nnf_match (get_match r)"
        by(simp add: optimize_matches_def)
      with IH show ?case by(simp add: optimize_matches_def)
    qed


lemma normalize_rules_dnf_normalized_nnf_match: "\<forall>x \<in> set (normalize_rules_dnf rs). normalized_nnf_match (get_match x)"
  proof(induction rs)
  case Nil thus ?case by simp
  next
  case (Cons r rs) thus ?case using normalized_nnf_match_normalize_match by(cases r) fastforce
  qed

end