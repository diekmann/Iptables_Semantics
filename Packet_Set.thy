theory Packet_Set
imports Fixed_Action "Primitive_Matchers/Negation_Type" Datatype_Selectors
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


lemma negation_type_to_match_expr_app: "matches \<gamma> (negation_type_to_match_expr (as @ bs)) a p \<longleftrightarrow>
         matches \<gamma> (MatchAnd (negation_type_to_match_expr as) (negation_type_to_match_expr bs)) a p"
  apply(induction as arbitrary: bs)
   apply(simp_all add: bunch_of_lemmata_about_matches)
   apply(case_tac aa)
   apply(simp_all add: bunch_of_lemmata_about_matches)
   done

lemma "normalized_match m \<Longrightarrow> matches \<gamma> (negation_type_to_match_expr (to_negation_type_nnf m)) a p  = matches \<gamma> m a p"
  apply(induction m rule: to_negation_type_nnf.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches negation_type_to_match_expr_app)
  done
  
  

text{*inner is and, outer is or*}
definition to_negation_type :: "'a match_expr \<Rightarrow> ('a negation_type list) list" where
 "to_negation_type m = map to_negation_type_nnf (normalize_match m)"

term normalize_match
term normalized_match
thm normalized_match_normalize_match


(*probably wants a simple ruleset*)

definition to_packet_set :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> ('a negation_type list) list \<Rightarrow> 'packet set" where
  "to_packet_set \<gamma> a ms \<equiv> {p. \<exists> m \<in> set ms. matches \<gamma> (negation_type_to_match_expr m) a p}"



(*TODO create a output_format directory*)

text{*
  The following function takes a tuple of functions and a match expression.
  The passed function tuple must be the discriminator and selector of the datatype package.
  It filters the latter and returns a tuple.
  The first element are the filtered primitive matches, the second element is the remaining match expression.
  *}
fun primitive_extractor :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> 'a match_expr \<Rightarrow> ('b negation_type list \<times> 'a match_expr)" where
 "primitive_extractor _ MatchAny = ([], MatchAny)" |
 "primitive_extractor (disc,sel) (Match a) = (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a))" |
 "primitive_extractor (disc,sel) (MatchNot (Match a)) = (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)))" |
 "primitive_extractor C (MatchAnd ms1 ms2) = (
        let (a1', ms1') = primitive_extractor C ms1; 
            (a2', ms2') = primitive_extractor C ms2
        in (a1'@a2', MatchAnd ms1' ms2'))"



lemma primitive_extractor_correct: "normalized_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> wf_disc_sel (disc, sel) C \<Longrightarrow>
  matches \<gamma> (negation_type_to_match_expr (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
  apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches wf_disc_sel.simps split: split_if_asm)
  apply(simp split: split_if_asm split_split_asm add: NegPos_map_append)
  apply(auto simp add: negation_type_to_match_expr_app bunch_of_lemmata_about_matches)
  done


(*
text{*
  The following function takes a filter function @{text f} and a match expression.
  It filters the latter and returns a tuple.
  The first element are the filtered primitive matches, the second element is the remaining match expression.
  }*}
fun primitive_extractor :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> ('a negation_type list \<times> 'a match_expr)" where
 "primitive_extractor _ MatchAny = ([], MatchAny)" |
 "primitive_extractor f (Match a) = (if f a then ([Pos a], MatchAny) else ([], Match a))" |
 "primitive_extractor f (MatchNot (Match a)) = (if f a then ([Neg a], MatchAny) else ([], MatchNot (Match a)))" |
 "primitive_extractor f (MatchAnd ms1 ms2) = (
        let (a1', ms1') = primitive_extractor f ms1; 
            (a2', ms2') = primitive_extractor f ms2
        in (a1'@a2', MatchAnd ms1' ms2'))"


lemma primitive_extractor_correct: "normalized_match m \<Longrightarrow> (as, ms) = primitive_extractor f m \<Longrightarrow> 
  matches \<gamma> (negation_type_to_match_expr as) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
  apply(induction f m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches split: split_if_asm)
  apply(simp split: split_if_asm split_split_asm)
  apply(auto simp add: negation_type_to_match_expr_app bunch_of_lemmata_about_matches)
  done

corollary primitive_extractor_correct': "normalized_match m  \<Longrightarrow> 
  matches \<gamma> (negation_type_to_match_expr (fst (primitive_extractor f m))) a p \<and> matches \<gamma> (snd (primitive_extractor f m)) a p \<longleftrightarrow> matches \<gamma> m a p"
  by(drule primitive_extractor_correct) auto
*)

end
