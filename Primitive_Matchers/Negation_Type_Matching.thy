theory Negation_Type_Matching
imports  Negation_Type "../Matching_Ternary" "../Datatype_Selectors" "../Fixed_Action"
begin

section{*Negation Type Matching*}


text{*Transform a @{typ "'a negation_type list"} to a @{typ "'a match_expr"} via conjunction.*}
fun alist_and :: "'a negation_type list \<Rightarrow> 'a match_expr" where
  "alist_and [] = MatchAny" |
  "alist_and ((Pos e)#es) = MatchAnd (Match e) (alist_and es)" |
  "alist_and ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and es)"


lemma alist_and_append: "matches \<gamma> (alist_and (l1 @ l2)) a p \<longleftrightarrow> matches \<gamma>  (MatchAnd (alist_and l1)  (alist_and l2)) a p"
  apply(induction l1)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  apply(rename_tac l l1)
  apply(case_tac l)
   apply(simp_all add: bunch_of_lemmata_about_matches)
  done


fun to_negation_type_nnf :: "'a match_expr \<Rightarrow> 'a negation_type list" where
 "to_negation_type_nnf MatchAny = []" |
 "to_negation_type_nnf (Match a) = [Pos a]" |
 "to_negation_type_nnf (MatchNot (Match a)) = [Neg a]" |
 "to_negation_type_nnf (MatchAnd a b) = (to_negation_type_nnf a) @ (to_negation_type_nnf b)"


lemma "normalized_match m \<Longrightarrow> matches \<gamma> (alist_and (to_negation_type_nnf m)) a p  = matches \<gamma> m a p"
  apply(induction m rule: to_negation_type_nnf.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches alist_and_append)
  done
  


text{*Isolating the matching semantics*}
fun nt_match_list :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "nt_match_list _ _ _ [] = True" |
  "nt_match_list \<gamma> a p ((Pos x)#xs) \<longleftrightarrow> matches \<gamma> (Match x) a p \<and> nt_match_list \<gamma> a p xs" |
  "nt_match_list \<gamma> a p ((Neg x)#xs) \<longleftrightarrow> matches \<gamma> (MatchNot (Match x)) a p \<and> nt_match_list \<gamma> a p xs"

lemma nt_match_list_matches: "nt_match_list \<gamma> a p l \<longleftrightarrow> matches \<gamma> (alist_and l) a p"
  apply(induction l rule: alist_and.induct)
  apply(simp_all)
  apply(case_tac [!] \<gamma>)
  apply(simp_all add: bunch_of_lemmata_about_matches)
done


lemma nt_match_list_simp: "nt_match_list \<gamma> a p ms \<longleftrightarrow> 
      (\<forall>m \<in> set (getPos ms). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg ms). matches \<gamma> (MatchNot (Match m)) a p)"
apply(induction \<gamma> a p ms rule: nt_match_list.induct)
apply(simp_all)
by fastforce

lemma matches_alist_and: "matches \<gamma> (alist_and l) a p \<longleftrightarrow> (\<forall>m \<in> set (getPos l). matches \<gamma> (Match m) a p) \<and> (\<forall>m \<in> set (getNeg l). matches \<gamma> (MatchNot (Match m)) a p)"
by (metis (poly_guards_query) nt_match_list_matches nt_match_list_simp)



text{*
  The following function takes a tuple of functions and a match expression.
  The passed function tuple must be the discriminator and selector of the datatype package.
  It filters the latter and returns a tuple.
  The first element are the filtered primitive matches, the second element is the remaining match expression.

  It requires a @{const normalized_match}.
  *}
fun primitive_extractor :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> 'a match_expr \<Rightarrow> ('b negation_type list \<times> 'a match_expr)" where
 "primitive_extractor _ MatchAny = ([], MatchAny)" |
 "primitive_extractor (disc,sel) (Match a) = (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a))" |
 "primitive_extractor (disc,sel) (MatchNot (Match a)) = (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)))" |
 "primitive_extractor C (MatchAnd ms1 ms2) = (
        let (a1', ms1') = primitive_extractor C ms1; 
            (a2', ms2') = primitive_extractor C ms2
        in (a1'@a2', MatchAnd ms1' ms2'))"


text{*
  The first part returned by @{const primitive_extractor}, here @{text as}:
    A list of primitive match expressions.
    For example, let @{text "m = MatchAnd (Src ip1) (Dst ip2)"} then, using the src @{text "(disc, sel)"}, the result is @{text "[ip1]"}.
    Note that @{text Src} is stripped from the result.

    The second part, here @{text ms} is the match expression which was not extracted.

    Together, the first and second part match iff @{text m} matches.
*}
lemma primitive_extractor_correct_help: "normalized_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> wf_disc_sel (disc, sel) C \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
  apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp_all add: bunch_of_lemmata_about_matches wf_disc_sel.simps split: split_if_asm)
  apply(simp split: split_if_asm split_split_asm add: NegPos_map_append)
  apply(auto simp add: alist_and_append bunch_of_lemmata_about_matches)
  done

lemma primitive_extractor_correct: "normalized_match m \<Longrightarrow> wf_disc_sel (disc, sel) C \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> 
  matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
using primitive_extractor_correct_help by metis

theorem primitive_extractor_correct': "normalized_match m \<Longrightarrow> wf_disc_sel discsel C \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C (fst (primitive_extractor discsel m)))) a p \<and> matches \<gamma> (snd (primitive_extractor discsel m)) a p \<longleftrightarrow> matches \<gamma> m a p"
apply(cases discsel)
apply(drule primitive_extractor_correct)
apply auto
done


text{*
  You can apply @{const primitive_extractor} iteratively on the returned match expression (second part of tuple) to extract all desired match fields.
*}


lemma primitive_extractor_normalized_helper: "normalized_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> normalized_match ms"
  apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp)
  apply(simp)
  apply(simp split: split_if_asm)
  apply(simp split: split_if_asm)
  apply(clarify) (*if i don't clarify, the simplifier loops*)
  apply(simp split: split_split_asm)
  apply(simp)
  apply(simp)
  apply(simp)
  done
  
lemma primitive_extractor_normalized: "normalized_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> normalized_match ms"
using primitive_extractor_normalized_helper by metis


fun has_disc :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_disc _ MatchAny = False" |
  "has_disc disc (Match a) = disc a" |
  "has_disc disc (MatchNot m) = has_disc disc m" |
  "has_disc disc (MatchAnd m1 m2) = (has_disc disc m1 \<or> has_disc disc m2)"



lemma primitive_extractor_has_disc_helper: "normalized_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> \<not> has_disc disc ms"
  apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp_all split: split_if_asm split_split_asm)
  done

lemma primitive_extractor_has_disc: "normalized_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)\<Longrightarrow> \<not> has_disc disc ms"
using primitive_extractor_has_disc_helper by metis


lemma primitive_extractor_has_disc2: "\<not> has_disc disc2 m \<Longrightarrow> normalized_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> \<not> has_disc disc ms \<and> \<not> has_disc disc2 ms"
apply(rule conjI)
using primitive_extractor_has_disc_helper apply(metis)
apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
apply(simp)
apply(simp split: split_if_asm)
apply(simp split: split_if_asm)
apply(clarify) (*the simplifier loops*)
apply(frule primitive_extractor_normalized)
sorry

end
