theory Packet_Set
imports Fixed_Action "Primitive_Matchers/Negation_Type"
begin

fun negation_type_to_match_expr :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "negation_type_to_match_expr [] = MatchAny" |
  "negation_type_to_match_expr (Pos a#as) = MatchAnd (Match a) (negation_type_to_match_expr as)" |
  "negation_type_to_match_expr (Neg a#as) = MatchAnd (MatchNot (Match a)) (negation_type_to_match_expr as)"



(*TODO unify with Format_Ln*)

fun to_negation_type_nnf :: "'a match_expr \<Rightarrow> 'a negation_type list" where
 "to_negation_type_nnf MatchAny = []" |
 "to_negation_type_nnf (Match a) = [Pos a]" |
 "to_negation_type_nnf (MatchNot (Match a)) = [Neg a]" |
 "to_negation_type_nnf (MatchAnd a b) = (to_negation_type_nnf a) @ (to_negation_type_nnf b)"


lemma x:"matches \<gamma> (negation_type_to_match_expr (as @ bs)) a p = matches \<gamma> (MatchAnd (negation_type_to_match_expr as) (negation_type_to_match_expr bs)) a p"
  apply(induction as arbitrary: bs)
   apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(case_tac aa)
   apply(simp_all add: bunch_of_lemmata_about_matches)
   done

lemma "normalized_match m \<Longrightarrow> matches \<gamma> (negation_type_to_match_expr (to_negation_type_nnf m)) a p  = matches \<gamma> m a p"
  apply(induction m rule: to_negation_type_nnf.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches x)
  done
  
  

text{*inner is and, outer is or*}
definition to_negation_type :: "'a match_expr \<Rightarrow> ('a negation_type list) list" where
 "to_negation_type m = map to_negation_type_nnf (normalize_match m)"

term normalize_match
thm normalized_match_normalize_match


(*probably wants a simple ruleset*)

definition to_packet_set :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> ('a negation_type list) list \<Rightarrow> 'packet set" where
  "to_packet_set \<gamma> a ms \<equiv> {p. \<exists> m \<in> set ms. matches \<gamma> (negation_type_to_match_expr m) a p}"


end
