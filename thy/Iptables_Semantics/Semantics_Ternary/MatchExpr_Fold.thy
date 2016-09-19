section\<open>Combine Match Expressions\<close>
theory MatchExpr_Fold
imports Primitive_Normalization
begin

fun andfold_MatchExp :: "'a match_expr list \<Rightarrow> 'a match_expr" where
  "andfold_MatchExp [] = MatchAny" |
  "andfold_MatchExp [e] = e" |
  "andfold_MatchExp (e#es) = MatchAnd e (andfold_MatchExp es)"

lemma andfold_MatchExp_alist_and: "alist_and' (map Pos ls) = andfold_MatchExp (map Match ls)"
  apply(induction ls)
   apply(simp)
  apply(simp)
  apply(rename_tac l ls)
  apply(case_tac "ls")
   by(simp)+

lemma andfold_MatchExp_matches:
  "matches \<gamma> (andfold_MatchExp ms) a p \<longleftrightarrow> (\<forall>m \<in> set ms. matches \<gamma> m a p)"
  apply(induction ms rule: andfold_MatchExp.induct)
    apply(simp add: bunch_of_lemmata_about_matches)+
  done

lemma andfold_MatchExp_not_discI:
  "\<forall>m \<in> set ms. \<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (andfold_MatchExp ms)"
  by(induction ms rule: andfold_MatchExp.induct) (simp)+

lemma andfold_MatchExp_not_disc_negatedI:
  "\<forall>m \<in> set ms. \<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (andfold_MatchExp ms)"
  by(induction ms rule: andfold_MatchExp.induct) (simp)+

lemma andfold_MatchExp_not_disc_negated_mapMatch:
  "\<not> has_disc_negated disc False (andfold_MatchExp (map (Match \<circ> C) ls))"
  apply(induction ls)
   apply(simp; fail)
  apply(simp)
   apply(rename_tac ls, case_tac ls)
  by(simp)+

lemma andfold_MatchExp_not_disc_mapMatch:
  "\<forall>a. \<not> disc (C a) \<Longrightarrow> \<not> has_disc disc (andfold_MatchExp (map (Match \<circ> C) ls))"
  apply(induction ls)
   apply(simp; fail)
  apply(simp)
   apply(rename_tac ls, case_tac ls)
  by(simp)+

lemma andfold_MatchExp_normalized_nnf: "\<forall>m \<in> set ms. normalized_nnf_match m \<Longrightarrow>
    normalized_nnf_match (andfold_MatchExp ms)"
  by(induction ms rule: andfold_MatchExp.induct)(simp)+

lemma andfold_MatchExp_normalized_n_primitive: "\<forall>m \<in> set ms. normalized_n_primitive (disc, sel) f m \<Longrightarrow>
    normalized_n_primitive (disc, sel) f (andfold_MatchExp ms)"
  by(induction ms rule: andfold_MatchExp.induct)(simp)+

lemma andfold_MatchExp_normalized_normalized_n_primitive_single:
    "\<forall>a. \<not> disc (C a) \<Longrightarrow>
      s \<in> set (normalize_match (andfold_MatchExp (map (Match \<circ> C) xs))) \<Longrightarrow>
         normalized_n_primitive (disc, sel) f s"
  apply(rule normalized_n_primitive_if_no_primitive)
   using normalized_nnf_match_normalize_match apply blast
  apply(rule normalize_match_preserves_nodisc[where m="(andfold_MatchExp (map (Match \<circ> C) xs))"])
   apply simp_all
  by (simp add: andfold_MatchExp_not_discI)

lemma normalize_andfold_MatchExp_normalized_n_primitive:
  "\<forall> m \<in> set ms. \<forall> s' \<in> set (normalize_match m). normalized_n_primitive (disc, sel) f s' \<Longrightarrow>
        s \<in> set (normalize_match (andfold_MatchExp ms)) \<Longrightarrow>
          normalized_n_primitive (disc, sel) f s"
  proof(induction ms arbitrary: s rule: andfold_MatchExp.induct)
  case 1 thus ?case by simp
  next
  case 2 thus ?case by simp
  next
  case (3 v1 v2 va)
    have IH: "s' \<in> set (normalize_match (andfold_MatchExp (v2 # va))) \<Longrightarrow>
            normalized_n_primitive (disc, sel) f s'" for s'
    using 3(1)[of s'] (*without this, simp loops*)
    apply(simp)
    using 3(2) by force
    from 3(2,3) IH show ?case by(clarsimp)
  qed
end