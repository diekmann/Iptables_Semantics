theory Matching_Embeddings
imports "Semantics_Ternary/Matching_Ternary" Matching "Semantics_Ternary/Unknown_Match_Tacs"
begin

section\<open>Boolean Matching vs. Ternary Matching\<close>

term Semantics.matches
term Matching_Ternary.matches
(*'a is the primitive match condition, e.g. IpSrc \<dots>*)


text\<open>The two matching semantics are related. However, due to the ternary logic, we cannot directly translate one to the other.
The problem are @{const MatchNot} expressions which evaluate to @{const TernaryUnknown} because @{text "MatchNot TernaryUnknown"} and
@{text TernaryUnknown} are semantically equal!\<close>
lemma "\<exists>m \<beta> \<alpha> a. Matching_Ternary.matches (\<beta>, \<alpha>) m a p \<noteq> 
  Semantics.matches (\<lambda> atm p. case \<beta> atm p of TernaryTrue \<Rightarrow> True | TernaryFalse \<Rightarrow> False | TernaryUnknown \<Rightarrow> \<alpha> a p) m p"
apply(rule_tac x="MatchNot (Match X)" in exI) --\<open>any @{term "X::'a"}\<close>
by (auto split: ternaryvalue.split ternaryvalue.split_asm simp add: matches_case_ternaryvalue_tuple)

text\<open>the @{const the} in the next definition is always defined\<close>
lemma "\<forall>m \<in> {m. approx m p \<noteq> TernaryUnknown}. ternary_to_bool (approx m p) \<noteq> None"
  by(simp add: ternary_to_bool_None)


text\<open>
The Boolean and the ternary matcher agree (where the ternary matcher is defined)
\<close>
definition matcher_agree_on_exact_matches :: "('a, 'p) matcher \<Rightarrow> ('a \<Rightarrow> 'p \<Rightarrow> ternaryvalue) \<Rightarrow> bool" where
  "matcher_agree_on_exact_matches exact approx \<equiv> \<forall>p m. approx m p \<noteq> TernaryUnknown \<longrightarrow> exact m p = the (ternary_to_bool (approx m p))"

text\<open>We say the Boolean and ternary matchers agree iff they return the same result or the ternary matcher returns @{const TernaryUnknown}.\<close>
lemma "matcher_agree_on_exact_matches exact approx \<longleftrightarrow> (\<forall>p m. exact m p = the (ternary_to_bool (approx m p)) \<or> approx m p = TernaryUnknown)"
  unfolding matcher_agree_on_exact_matches_def by blast
lemma matcher_agree_on_exact_matches_alt: (*no `the`*)
  "matcher_agree_on_exact_matches exact approx \<longleftrightarrow> (\<forall>p m. approx m p \<noteq> TernaryUnknown \<longrightarrow> bool_to_ternary (exact m p) = approx m p)"
  unfolding matcher_agree_on_exact_matches_def
  by (metis (full_types) bool_to_ternary.simps(1) bool_to_ternary.simps(2) option.sel ternary_to_bool.simps(1)
                         ternary_to_bool.simps(2) ternaryvalue.exhaust)

lemma eval_ternary_Not_TrueD: "eval_ternary_Not m = TernaryTrue \<Longrightarrow> m = TernaryFalse"
  by (metis eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)


lemma matches_comply_exact: "ternary_ternary_eval (map_match_tac \<beta> p m) \<noteq> TernaryUnknown \<Longrightarrow>
       matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
        Semantics.matches \<gamma> m p = Matching_Ternary.matches (\<beta>, \<alpha>) m a p"
  proof(unfold matches_case_ternaryvalue_tuple,induction m)
  case Match thus ?case
       by(simp split: ternaryvalue.split add: matcher_agree_on_exact_matches_def)
  next
  case (MatchNot m) thus ?case
      apply(simp split: ternaryvalue.split add: matcher_agree_on_exact_matches_def)
      apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m)")
        by(simp_all)
  next
  case (MatchAnd m1 m2)
    thus ?case
     apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m1)")
       apply(case_tac [!] "ternary_ternary_eval (map_match_tac \<beta> p m2)")
                by(simp_all)
  next
  case MatchAny thus ?case by simp
  qed


lemma matcher_agree_on_exact_matches_gammaE:
  "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> \<beta> X p = TernaryTrue \<Longrightarrow> \<gamma> X p"
  apply(simp add: matcher_agree_on_exact_matches_alt)
  apply(erule_tac x=p in allE)
  apply(erule_tac x=X in allE)
  apply(simp add: bool_to_ternary_simps)
  done




lemma in_doubt_allow_allows_Accept: "a = Accept \<Longrightarrow> matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
        Semantics.matches \<gamma> m p \<Longrightarrow> Matching_Ternary.matches (\<beta>, in_doubt_allow) m a p"
  apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m) \<noteq> TernaryUnknown")
   using matches_comply_exact apply fast
  apply(simp add: matches_case_ternaryvalue_tuple)
  done

lemma not_exact_match_in_doubt_allow_approx_match: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> a = Accept \<or> a = Reject \<or> a = Drop \<Longrightarrow>
  \<not> Semantics.matches \<gamma> m p \<Longrightarrow> 
  (a = Accept \<and> Matching_Ternary.matches (\<beta>, in_doubt_allow) m a p) \<or> \<not> Matching_Ternary.matches (\<beta>, in_doubt_allow) m a p"
  apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m) \<noteq> TernaryUnknown")
   apply(drule(1) matches_comply_exact[where \<alpha>=in_doubt_allow and a=a])
   apply(rule disjI2)
   apply fast
  apply(simp)
  apply(clarify)
  apply(simp add: matches_case_ternaryvalue_tuple)
  apply(cases a)
         apply(simp_all)
  done




lemma in_doubt_deny_denies_DropReject: "a = Drop \<or> a = Reject \<Longrightarrow> matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow>
        Semantics.matches \<gamma> m p \<Longrightarrow> Matching_Ternary.matches (\<beta>, in_doubt_deny) m a p"
  apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m) \<noteq> TernaryUnknown")
   using matches_comply_exact apply fast
   apply(simp)
  apply(auto simp add: matches_case_ternaryvalue_tuple)
  done

lemma not_exact_match_in_doubt_deny_approx_match: "matcher_agree_on_exact_matches \<gamma> \<beta> \<Longrightarrow> a = Accept \<or> a = Reject \<or> a = Drop \<Longrightarrow>
  \<not> Semantics.matches \<gamma> m p \<Longrightarrow> 
  ((a = Drop \<or> a = Reject) \<and> Matching_Ternary.matches (\<beta>, in_doubt_deny) m a p) \<or> \<not> Matching_Ternary.matches (\<beta>, in_doubt_deny) m a p"
  apply(case_tac "ternary_ternary_eval (map_match_tac \<beta> p m) \<noteq> TernaryUnknown")
   apply(drule(1) matches_comply_exact[where \<alpha>=in_doubt_deny and a=a])
   apply(rule disjI2)
   apply fast
  apply(simp)
  apply(clarify)
  apply(simp add: matches_case_ternaryvalue_tuple)
  apply(cases a)
         apply(simp_all)
  done

text\<open>The ternary primitive matcher can return exactly the result of the Boolean primitive matcher\<close>
definition \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c :: "('a, 'p) matcher \<Rightarrow> ('a \<Rightarrow> 'p \<Rightarrow> ternaryvalue)" where
  "\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma> \<equiv> (\<lambda> a p. if \<gamma> a p then TernaryTrue else TernaryFalse)"

lemma "matcher_agree_on_exact_matches \<gamma> (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>)"
  by(simp add: matcher_agree_on_exact_matches_def \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_def)

lemma \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_not_Unknown: "ternary_ternary_eval (map_match_tac (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>) p m) \<noteq> TernaryUnknown"
  proof(induction m)
  case MatchNot thus ?case using eval_ternary_Not_UnknownD \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_def
     by (simp) blast
  case (MatchAnd m1 m2) thus ?case
    apply(case_tac "ternary_ternary_eval (map_match_tac (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>) p m1)")
      apply(case_tac [!] "ternary_ternary_eval (map_match_tac (\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>) p m2)")
            by(simp_all add: \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_def)
  qed (simp_all add: \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_def)

lemma \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_matching: "Matching_Ternary.matches ((\<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c \<gamma>), \<alpha>) m a p \<longleftrightarrow> Semantics.matches \<gamma> m p"
  proof(induction m)
  case Match thus ?case 
    by(simp add: \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_def matches_case_ternaryvalue_tuple)
  case MatchNot thus ?case
    by(simp add: matches_case_ternaryvalue_tuple \<beta>\<^sub>m\<^sub>a\<^sub>g\<^sub>i\<^sub>c_not_Unknown split: ternaryvalue.split_asm)
  qed (simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split ternaryvalue.split_asm)
  


end
