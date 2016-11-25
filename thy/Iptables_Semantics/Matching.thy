theory Matching
imports Semantics
begin

subsection\<open>Boolean Matcher Algebra\<close>

lemma MatchOr: "matches \<gamma> (MatchOr m1 m2) p \<longleftrightarrow> matches \<gamma> m1 p \<or> matches \<gamma> m2 p"
  by(simp add: MatchOr_def)

lemma opt_MatchAny_match_expr_correct: "matches \<gamma> (opt_MatchAny_match_expr m) = matches \<gamma> m"
 proof -
  have "matches \<gamma> (opt_MatchAny_match_expr_once m) = matches \<gamma> m" for m
   apply(simp add: fun_eq_iff)
   by(induction m rule: opt_MatchAny_match_expr_once.induct) (simp_all)
   thus ?thesis
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(rule repeat_stabilize_induct)
     by(simp)+
 qed
    

lemma matcheq_matchAny: "\<not> has_primitive m \<Longrightarrow> matcheq_matchAny m \<longleftrightarrow> matches \<gamma> m p"
  by(induction m) simp_all

lemma matcheq_matchNone: "\<not> has_primitive m \<Longrightarrow> matcheq_matchNone m \<longleftrightarrow> \<not> matches \<gamma> m p"
  by(auto dest: matcheq_matchAny matachAny_matchNone)

lemma matcheq_matchNone_not_matches: "matcheq_matchNone m \<Longrightarrow> \<not> matches \<gamma> m p"
  by(induction m rule: matcheq_matchNone.induct) auto


text\<open>Lemmas about matching in the @{const iptables_bigstep} semantics.\<close>

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
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m m') a'], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a'], Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow>?r")
proof
  assume ?l thus ?r
    by (induction "[Rule (MatchAnd m m') a']" Undecided t rule: iptables_bigstep_induct)
       (auto intro: iptables_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
next
  assume ?r thus ?l
    by (induction "[Rule m' a']" Undecided t rule: iptables_bigstep_induct)
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
          by (metis Nil_is_append_conv append_Nil butlast_append butlast_snoc seq)
      qed (auto intro: iptables_bigstep.intros)
  }
  thus ?thesis by blast
qed


subsection\<open>Add match\<close>

definition add_match :: "'a match_expr \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "add_match m rs = map (\<lambda>r. case r of Rule m' a' \<Rightarrow> Rule (MatchAnd m m') a') rs"

lemma add_match_split: "add_match m (rs1@rs2) = add_match m rs1 @ add_match m rs2"
  unfolding add_match_def
  by (fact map_append)

lemma add_match_split_fst: "add_match m (Rule m' a' # rs) = Rule (MatchAnd m m') a' # add_match m rs"
  unfolding add_match_def
  by simp


lemma add_match_distrib:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
proof -
  {
    fix m1 m2
    have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
      proof (induction rs arbitrary: s)
        case Nil thus ?case by (simp add: add_match_def)
        next
        case (Cons r rs)
        from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
        with Cons.prems obtain ti where 1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m1 (MatchAnd m2 m)) a], s\<rangle> \<Rightarrow> ti" and 2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), ti\<rangle> \<Rightarrow> t"
          apply(simp add: add_match_split_fst)
          apply(erule seqE_cons)
          by simp
        from 1 r have base: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m2 (MatchAnd m1 m)) a], s\<rangle> \<Rightarrow> ti"
           by (metis matches.simps(1) matches_rule_iptables_bigstep)
        from 2 Cons.IH have IH: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), ti\<rangle> \<Rightarrow> t" by simp
        from base IH seq'_cons have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule (MatchAnd m2 (MatchAnd m1 m)) a # add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t" by fast
        thus ?case using r by(simp add: add_match_split_fst[symmetric])
      qed
  }
  thus ?thesis by blast
qed

lemma add_match_split_fst': "add_match m (a # rs) = add_match m [a] @ add_match m rs"
  by (simp add: add_match_split[symmetric])



lemma matches_add_match_simp:
  assumes m: "matches \<gamma> m p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
  proof
    assume ?l with m show ?r
      proof (induction rs)
        case Nil
        thus ?case
          unfolding add_match_def by simp
      next
        case (Cons r rs)
        hence IH: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" by(simp add: add_match_split_fst)
        obtain m' a where r: "r = Rule m' a" by (cases r)
        with Cons.prems(2) obtain ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m m') a], s\<rangle> \<Rightarrow> ti" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, ti\<rangle> \<Rightarrow> t"
          by(auto elim:seqE_cons simp add: add_match_split_fst)
        with Cons.prems(1) IH have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a], s\<rangle> \<Rightarrow> ti" by(simp add: matches_rule_and_simp)
        with \<open>\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, ti\<rangle> \<Rightarrow> t\<close> IH r show ?case by(metis decision state.exhaust iptables_bigstep_deterministic seq_cons)
      qed
  next
    assume ?r with m show ?l
      proof (induction rs)
        case Nil
        thus ?case
          unfolding add_match_def by simp
      next
        case (Cons r rs)
        hence IH: " \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m rs, s\<rangle> \<Rightarrow> t" by(simp add: add_match_split_fst)
        obtain m' a where r: "r = Rule m' a" by (cases r)
        with Cons.prems(2) obtain ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' a], s\<rangle> \<Rightarrow> ti" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, ti\<rangle> \<Rightarrow> t"
          by(auto elim:seqE_cons simp add: add_match_split_fst)
        with Cons.prems(1) IH have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m m') a], s\<rangle> \<Rightarrow> ti" by(simp add: matches_rule_and_simp)
        with \<open>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, ti\<rangle> \<Rightarrow> t\<close> IH r show ?case 
          apply(simp add: add_match_split_fst)
          by(metis decision state.exhaust iptables_bigstep_deterministic seq_cons)
      qed
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


lemma add_match_match_not_cases:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> matches \<gamma> m p \<or> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  by (metis matches.simps(2) matches_add_match_simp)


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


lemma optimize_matches_option_generic:
  assumes "\<forall> r \<in> set rs. P (get_match r)"
      and "(\<And>m m'. P m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' p = matches \<gamma> m p)"
      and "(\<And>m. P m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m p)"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>optimize_matches_option f rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
      (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?rhs
    from this assms show ?lhs
    apply(induction rs s t rule: iptables_bigstep_induct)
    apply(auto simp: optimize_matches_option_append intro: iptables_bigstep.intros split: option.split)
    done
  next
    assume ?lhs
    from this assms show ?rhs
    apply(induction f rs arbitrary: s rule: optimize_matches_option.induct)
     apply(simp; fail)
    apply(simp split: option.split_asm)
     apply(subgoal_tac "\<not> matches \<gamma> m p")
     prefer 2 apply blast
    apply (metis decision nomatch seq'_cons state.exhaust)
    apply(erule seqE_cons)
    apply(rule_tac t=ti in seq'_cons)
     apply (meson matches_rule_iptables_bigstep)
    by blast
  qed

lemma optimize_matches_generic: "\<forall> r \<in> set rs. P (get_match r) \<Longrightarrow> 
      (\<And>m. P m \<Longrightarrow> matches \<gamma> (f m) p = matches \<gamma> m p) \<Longrightarrow>
      \<Gamma>,\<gamma>,p\<turnstile> \<langle>optimize_matches f rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_generic)
    apply(simp; fail)
   apply(simp split: if_split_asm)
   apply blast
  apply(simp split: if_split_asm)
  using matcheq_matchNone_not_matches by fast
end
