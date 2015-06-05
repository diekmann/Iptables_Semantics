theory Matching
imports Semantics
begin

subsection{*Boolean Matcher Algebra*}
text{*Lemmas about matching in the @{const iptables_bigstep} semantics.*}

lemma matches_rule_iptables_bigstep:
  assumes "matches \<gamma> m p \<longleftrightarrow> matches \<gamma> m' p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a], s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow>?r")
proof -
  {
    fix m m'
    assume "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t" "matches \<gamma> m p \<longleftrightarrow> matches \<gamma> m' p"
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a], s\<rangle> \<Rightarrow> t"
      by (induction "[Rule  m a]" s t rule: iptables_bigstep_induct)
         (auto intro: iptables_bigstep.intros simp: Cons_eq_append_conv dest: skipD)
  }
  with assms show ?thesis by blast
qed

lemma matches_rule_and_simp_help:
  assumes "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m m') a'], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a'], s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow>?r")
proof
  assume ?l thus ?r
    by (induction "[Rule (MatchAnd m m') a']" s t rule: iptables_bigstep_induct)
       (auto intro: iptables_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
next
  assume ?r thus ?l
    by (induction "[Rule m' a']" s t rule: iptables_bigstep_induct)
       (auto intro: iptables_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
qed

lemma matches_MatchNot_simp: 
  assumes "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchNot m) a], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l thus ?r
    by (induction "[Rule (MatchNot m) a]" "Undecided" t rule: iptables_bigstep_induct)
       (auto intro: iptables_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
next
  assume ?r
  hence "t = Undecided"
    by (metis skipD)
  with assms show ?l
    by (fastforce intro: nomatch)
qed

lemma matches_MatchNotAnd_simp:
  assumes "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd (MatchNot m) m') a], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l thus ?r
    by (induction "[Rule (MatchAnd (MatchNot m) m') a]" "Undecided" t rule: iptables_bigstep_induct)
       (auto intro: iptables_bigstep.intros simp add: assms Cons_eq_append_conv dest: skipD)
next
  assume ?r
  hence "t = Undecided"
    by (metis skipD)
  with assms show ?l
    by (fastforce intro: nomatch)
qed
  
lemma matches_rule_and_simp:
  assumes "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m m') a'], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a'], s\<rangle> \<Rightarrow> t"
proof (cases s)
  case Undecided
  with assms show ?thesis
    by (simp add: matches_rule_and_simp_help)
next
  case Decision
  thus ?thesis by (metis decision decisionD)
qed

lemma iptables_bigstep_MatchAnd_comm:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m1 m2) a], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m2 m1) a], s\<rangle> \<Rightarrow> t"
proof -
  { fix m1 m2
    have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m1 m2) a], s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m2 m1) a], s\<rangle> \<Rightarrow> t"
      proof (induction "[Rule (MatchAnd m1 m2) a]" s t rule: iptables_bigstep_induct)
        case Seq thus ?case
          by (smt list_app_singletonE skipD)(*TODO*)
      qed (auto intro: iptables_bigstep.intros)
  }
  thus ?thesis by blast
qed


definition add_match :: "'a match_expr \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "add_match m rs = map (\<lambda>r. case r of Rule m' a' \<Rightarrow> Rule (MatchAnd m m') a') rs"

lemma add_match_split: "add_match m (rs1@rs2) = add_match m rs1 @ add_match m rs2"
  unfolding add_match_def
  by (fact map_append)

lemma add_match_split_fst: "add_match m (Rule m' a' # rs) = Rule (MatchAnd m m') a' # add_match m rs"
  unfolding add_match_def
  by simp

lemma matches_add_match_no_matching_Goto_simp: "matches \<gamma> m p \<Longrightarrow> no_matching_Goto \<gamma> p (add_match m rs) \<Longrightarrow> no_matching_Goto \<gamma> p rs"
  apply(induction rs)
   apply(simp_all)
  apply(rename_tac r rs)
  apply(case_tac r)
  apply(simp add: add_match_split_fst no_matching_Goto_tail)
  apply(drule no_matching_Goto_head)
  apply(rename_tac m' a')
  apply(case_tac a')
          apply simp_all
  done


lemma not_matches_add_match_simp:
  assumes "\<not> matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> t"
  proof(induction rs)
    case Nil
    thus ?case
      unfolding add_match_def by simp
  next
    case (Cons r rs)
    thus ?case
      apply (cases r)
      apply(simp add: add_match_split_fst)
      apply(rule iffI)
       apply(erule seqE_cons)
        apply(simp_all)
        apply(subgoal_tac "ti = Undecided")
         apply(simp)
        apply (simp add: assms nomatchD)
       apply(simp add: not_no_matching_Goto_singleton_cases)
       apply(clarify)
       apply(simp)
       using assms apply blast
      apply(subgoal_tac "t = Undecided")
       prefer 2
       using skipD apply metis
      apply(simp)
      by (meson assms matches.simps(1) nomatch not_no_matching_Goto_singleton_cases seq_cons)  
  qed

lemma matches_add_match_MatchNot_simp:
  assumes m: "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], s\<rangle> \<Rightarrow> t" (is "?l s \<longleftrightarrow> ?r s")
  proof (cases s)
    case Undecided
    have "?l Undecided \<longleftrightarrow> ?r Undecided"
      proof
        assume "?l Undecided" with m show "?r Undecided"
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
            thus ?case
              by (cases r) (metis matches_MatchNotAnd_simp skipD seqE_cons add_match_split_fst)
          qed
      next
        assume "?r Undecided" with m show "?l Undecided"
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
            thus ?case
              apply (cases r) 
              apply(simp add: add_match_split_fst)
              apply(subgoal_tac "t = Undecided")
               prefer 2
               using skipD apply metis
              apply(simp)
              by (metis matches.simps(1) matches.simps(2) matches_MatchNotAnd_simp not_no_matching_Goto_singleton_cases seq_cons)
          qed
      qed
    with Undecided show ?thesis by fast
  next
    case (Decision d)
    thus ?thesis
      by(metis decision decisionD)
  qed


(*TODO: push this lemma to the main semantics?*)
lemma just_show_all_bigstep_semantics_equalities_with_start_Undecided: 
      "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs1, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs2, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> 
       \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs1, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs2, s\<rangle> \<Rightarrow> t"
  apply(cases s)
   apply(simp)
  apply(simp)
  using decision decisionD by fastforce
  
lemma matches_add_match_simp_helper:
  assumes m: "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
  proof
    assume ?l with m show ?r
      proof (induction rs)
        case Nil
        thus ?case
          unfolding add_match_def by simp
      next
        case (Cons r rs)
        thus ?case
          apply(cases r)
          apply(simp only: add_match_split_fst)
           apply(erule seqE_cons_Undecided)
           apply(simp only: matches_rule_and_simp)
           apply(subgoal_tac "no_matching_Goto \<gamma> p [Rule (x1) x2]")
            apply (metis decision state.exhaust iptables_bigstep_deterministic seq_cons)
           apply (metis matches.simps(1) not_no_matching_Goto_singleton_cases)
          apply(simp)
          apply(clarify)
          apply(simp)
          apply(simp add: matches_rule_and_simp_help)
          by (simp add: seq_cons_Goto_t)
      qed
  next
    assume ?r with m show ?l
      proof (induction rs)
        case Nil
        thus ?case
          unfolding add_match_def by simp
      next
        case (Cons r rs)
        thus ?case
          apply(cases r)
          apply(simp only: add_match_split_fst)
          apply(erule seqE_cons_Undecided)
           apply(subst(asm) matches_rule_and_simp[symmetric])
            apply(simp)
           apply(simp)
           apply(case_tac ti)
            apply (metis matches.simps(1) not_no_matching_Goto_singleton_cases seq_cons)
           apply (metis decision decisionD matches.simps(1) not_no_matching_Goto_singleton_cases seq_cons)
          by (simp add: matches_rule_and_simp_help seq_cons_Goto_t)
      qed
  qed


lemma matches_add_match_simp:
  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  apply(rule just_show_all_bigstep_semantics_equalities_with_start_Undecided)
  by(simp add: matches_add_match_simp_helper)

lemma not_matches_add_matchNot_simp:
  "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  by (simp add: matches_add_match_simp)


lemma unfold_Goto_Undecided:
    assumes "\<Gamma> chain = Some rs"
    shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs @ add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t"
          (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  thus ?r
  proof(cases rule: seqE_cons)
  case (no_matching_Goto ti)
    from no_matching_Goto have "\<not> matches \<gamma> m p" by simp
    with no_matching_Goto have ti: "ti = Undecided" using nomatchD by metis
    from `\<not> matches \<gamma> m p` have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> Undecided"
      using not_matches_add_match_simp skip by fast
    from no_matching_Goto ti have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rest, Undecided\<rangle> \<Rightarrow> t" by simp
    with matches_add_match_MatchNot_simp
  apply -
  apply(drule seqE_cons)
    apply(simp_all)
   apply(subgoal_tac "ti = Undecided")
    prefer 2
   apply(simp)
 thm not_matches_add_match_simp
 apply(simp add: not_matches_add_match_simp) 
 
thm gotoD seqE_cons
oops


lemma matches_add_match_MatchNot_simp:
  assumes m: "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], s\<rangle> \<Rightarrow> t" (is "?l s \<longleftrightarrow> ?r s")
  proof (cases s)
    case Undecided
    have "?l Undecided \<longleftrightarrow> ?r Undecided"
      proof
        assume "?l Undecided" with m show "?r Undecided"
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
            thus ?case
              by (cases r) (metis matches_MatchNotAnd_simp skipD seqE_cons add_match_split_fst)
          qed
      next
        assume "?r Undecided" with m show "?l Undecided"
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
            thus ?case
              by (cases r) (metis matches_MatchNotAnd_simp skipD seq'_cons add_match_split_fst)
          qed
      qed
    with Undecided show ?thesis by fast
  next
    case (Decision d)
    thus ?thesis
      by(metis decision decisionD)
  qed

lemma not_matches_add_match_simp:
  assumes "\<not> matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> t"
  proof(induction rs)
    case Nil
    thus ?case
      unfolding add_match_def by simp
  next
    case (Cons r rs)
    thus ?case
      by (cases r) (metis assms add_match_split_fst matches.simps(1) nomatch seq'_cons nomatchD seqE_cons)
  qed

lemma iptables_bigstep_add_match_notnot_simp: 
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot (MatchNot m)) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, s\<rangle> \<Rightarrow> t"
  proof(induction rs)
    case Nil
    thus ?case
      unfolding add_match_def by simp
  next
    case (Cons r rs)
    thus ?case
      by (cases r)
         (metis decision decisionD state.exhaust matches.simps(2) matches_add_match_simp not_matches_add_match_simp)
  qed

lemma not_matches_add_matchNot_simp:
  "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  by (simp add: matches_add_match_simp)

lemma iptables_bigstep_add_match_and:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchAnd m1 m2) rs, s\<rangle> \<Rightarrow> t"
  proof(induction rs arbitrary: s t)
    case Nil
    thus ?case
      unfolding add_match_def by simp
  next
    case(Cons r rs)
    show ?case
    proof (cases r, simp only: add_match_split_fst)
      fix m a
      show "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule (MatchAnd m1 (MatchAnd m2 m)) a # add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule (MatchAnd (MatchAnd m1 m2) m) a # add_match (MatchAnd m1 m2) rs, s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
      proof
        assume ?l with Cons.IH show ?r
          apply -
          apply(erule seqE_cons)
          apply(case_tac s)
          apply(case_tac ti)
          apply (metis matches.simps(1) matches_rule_and_simp matches_rule_and_simp_help nomatch seq'_cons)
          apply (metis add_match_split_fst matches.simps(1) matches_add_match_simp not_matches_add_match_simp seq_cons)
          apply (metis decision decisionD)
          done
      next
        assume ?r with Cons.IH show ?l
          apply -
          apply(erule seqE_cons)
          apply(case_tac s)
          apply(case_tac ti)
          apply (metis matches.simps(1) matches_rule_and_simp matches_rule_and_simp_help nomatch seq'_cons)
          apply (metis add_match_split_fst matches.simps(1) matches_add_match_simp not_matches_add_match_simp seq_cons)
          apply (metis decision decisionD)
          done
        qed
    qed
  qed

end
