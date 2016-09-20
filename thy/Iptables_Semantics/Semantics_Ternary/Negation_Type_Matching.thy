theory Negation_Type_Matching
imports  "../Common/Negation_Type" Matching_Ternary "../Datatype_Selectors" Normalized_Matches
begin

section\<open>Negation Type Matching\<close>


text\<open>Transform a @{typ "'a negation_type list"} to a @{typ "'a match_expr"} via conjunction.\<close>
fun alist_and :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "alist_and [] = MatchAny" |
  "alist_and ((Pos e)#es) = MatchAnd (Match e) (alist_and es)" |
  "alist_and ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and es)"

lemma normalized_nnf_match_alist_and: "normalized_nnf_match (alist_and as)"
  by(induction as rule: alist_and.induct) simp_all

lemma alist_and_append: "matches \<gamma> (alist_and (l1 @ l2)) a p \<longleftrightarrow> matches \<gamma>  (MatchAnd (alist_and l1)  (alist_and l2)) a p"
  proof(induction l1)
  case Nil thus ?case by (simp add: bunch_of_lemmata_about_matches)
  next
  case (Cons l l1) thus ?case by (cases l) (simp_all add: bunch_of_lemmata_about_matches)
  qed

  text\<open>This version of @{const alist_and} avoids the trailing @{const MatchAny}. Only intended for code.\<close>
  fun alist_and' :: "'a negation_type list \<Rightarrow> 'a match_expr" where
    "alist_and' [] = MatchAny" |
    "alist_and' [Pos e] = Match e" |
    "alist_and' [Neg e] = MatchNot (Match e)"|
    "alist_and' ((Pos e)#es) = MatchAnd (Match e) (alist_and' es)" |
    "alist_and' ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and' es)"

  lemma alist_and': "matches (\<gamma>, \<alpha>) (alist_and' as) = matches (\<gamma>, \<alpha>) (alist_and as)"
    by(induction as rule: alist_and'.induct) (simp_all add: bunch_of_lemmata_about_matches)
 
  lemma normalized_nnf_match_alist_and': "normalized_nnf_match (alist_and' as)"
    by(induction as rule: alist_and'.induct) simp_all

  lemma matches_alist_and_alist_and':
    "matches \<gamma> (alist_and' ls) a p \<longleftrightarrow> matches \<gamma> (alist_and ls) a p"
    apply(induction ls rule: alist_and'.induct)
    by(simp add: bunch_of_lemmata_about_matches)+

  lemma alist_and'_append: "matches \<gamma> (alist_and' (l1 @ l2)) a p \<longleftrightarrow> matches \<gamma> (MatchAnd (alist_and' l1) (alist_and' l2)) a p"
    proof(induction l1)
    case Nil thus ?case by (simp add: bunch_of_lemmata_about_matches)
    next
    case (Cons l l1) thus ?case
      apply (cases l)
       by(simp_all add: matches_alist_and_alist_and' bunch_of_lemmata_about_matches)
    qed

lemma alist_and_NegPos_map_getNeg_getPos_matches: 
  "(\<forall>m\<in>set (getNeg spts). matches \<gamma> (MatchNot (Match (C m))) a p) \<and>
   (\<forall>m\<in>set (getPos spts). matches \<gamma> (Match (C m)) a p)
    \<longleftrightarrow>
    matches \<gamma> (alist_and (NegPos_map C spts)) a p"
  proof(induction spts rule: alist_and.induct)
  qed(auto simp add: bunch_of_lemmata_about_matches)


fun negation_type_to_match_expr_f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type \<Rightarrow> 'b match_expr" where
  "negation_type_to_match_expr_f f (Pos a) = Match (f a)" |
  "negation_type_to_match_expr_f f (Neg a) = MatchNot (Match (f a))"

lemma alist_and_negation_type_to_match_expr_f_matches:
    "matches \<gamma> (alist_and (NegPos_map C spts)) a p \<longleftrightarrow>
        (\<forall>m\<in>set spts. matches \<gamma> (negation_type_to_match_expr_f C m) a p)"
  proof(induction spts rule: alist_and.induct)
  qed(auto simp add: bunch_of_lemmata_about_matches)

definition negation_type_to_match_expr :: "'a negation_type \<Rightarrow> 'a match_expr" where
  "negation_type_to_match_expr m \<equiv> negation_type_to_match_expr_f id m"

lemma negation_type_to_match_expr_simps:
  "negation_type_to_match_expr (Pos e) = (Match e)"
  "negation_type_to_match_expr (Neg e) = (MatchNot (Match e))"
by(simp_all add: negation_type_to_match_expr_def)

lemma alist_and_negation_type_to_match_expr: "alist_and (n#es) =  MatchAnd (negation_type_to_match_expr n) (alist_and es)"
  by(cases n, simp_all add: negation_type_to_match_expr_simps)


fun to_negation_type_nnf :: "'a match_expr \<Rightarrow> 'a negation_type list" where
 "to_negation_type_nnf MatchAny = []" |
 "to_negation_type_nnf (Match a) = [Pos a]" |
 "to_negation_type_nnf (MatchNot (Match a)) = [Neg a]" |
 "to_negation_type_nnf (MatchAnd a b) = (to_negation_type_nnf a) @ (to_negation_type_nnf b)" |
 "to_negation_type_nnf _ = undefined"


lemma "normalized_nnf_match m \<Longrightarrow> matches \<gamma> (alist_and (to_negation_type_nnf m)) a p  = matches \<gamma> m a p"
  proof(induction m rule: to_negation_type_nnf.induct)
  qed(simp_all add: bunch_of_lemmata_about_matches alist_and_append)


text\<open>Isolating the matching semantics\<close>
fun nt_match_list :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "nt_match_list _ _ _ [] = True" |
  "nt_match_list \<gamma> a p ((Pos x)#xs) \<longleftrightarrow> matches \<gamma> (Match x) a p \<and> nt_match_list \<gamma> a p xs" |
  "nt_match_list \<gamma> a p ((Neg x)#xs) \<longleftrightarrow> matches \<gamma> (MatchNot (Match x)) a p \<and> nt_match_list \<gamma> a p xs"

lemma nt_match_list_matches: "nt_match_list \<gamma> a p l \<longleftrightarrow> matches \<gamma> (alist_and l) a p"
  apply(induction l rule: alist_and.induct)
    apply(case_tac [!] \<gamma>)
    apply(simp_all add: bunch_of_lemmata_about_matches)
  done


lemma nt_match_list_simp: "nt_match_list \<gamma> a p ms \<longleftrightarrow> 
      (\<forall>m \<in> set (getPos ms). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg ms). matches \<gamma> (MatchNot (Match m)) a p)"
  proof(induction \<gamma> a p ms rule: nt_match_list.induct)
  case 3 thus ?case by fastforce
  qed(simp_all)

lemma matches_alist_and: "matches \<gamma> (alist_and l) a p \<longleftrightarrow> (\<forall>m \<in> set (getPos l). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg l). matches \<gamma> (MatchNot (Match m)) a p)"
  using nt_match_list_matches nt_match_list_simp by fast




end
