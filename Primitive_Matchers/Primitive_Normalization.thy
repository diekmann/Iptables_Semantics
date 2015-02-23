theory Primitive_Normalization
imports  "../Output_Format/Negation_Type_Matching" 
begin

section{*Primitive Normalization*}

text{*
  Test if a @{text disc} is in the match expression.
  For example, it call tell whether there are some matches for @{text "Src ip"}.
*}
fun has_disc :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_disc _ MatchAny = False" |
  "has_disc disc (Match a) = disc a" |
  "has_disc disc (MatchNot m) = has_disc disc m" |
  "has_disc disc (MatchAnd m1 m2) = (has_disc disc m1 \<or> has_disc disc m2)"



fun normalized_n_primitive :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "normalized_n_primitive _ _ MatchAny = True" |
  "normalized_n_primitive (disc, sel) n (Match (P)) = (if disc P then n (sel P) else True)" |
  "normalized_n_primitive (disc, sel) n (MatchNot (Match (P))) = (if disc P then False else True)" |
  "normalized_n_primitive (disc, sel) n (MatchAnd m1 m2) = (normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2)" |
  "normalized_n_primitive _ _ (MatchNot (MatchAnd _ _)) = False" |
  (*"normalized_n_primitive _ _ (MatchNot _) = True" *)
  "normalized_n_primitive _ _ (MatchNot (MatchNot _)) = False" | (*not nnf normalized*)
  "normalized_n_primitive _ _ (MatchNot MatchAny) = True"


text{*
  The following function takes a tuple of functions (@{typ "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b))"}) and a @{typ "'a match_expr"}.
  The passed function tuple must be the discriminator and selector of the datatype package.
  @{text primitive_extractor} filters the @{typ "'a match_expr"} and returns a tuple.
  The first element of the returned tuple is the filtered primitive matches, the second element is the remaining match expression.

  It requires a @{const normalized_nnf_match}.
  *}
fun primitive_extractor :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> 'a match_expr \<Rightarrow> ('b negation_type list \<times> 'a match_expr)" where
 "primitive_extractor _ MatchAny = ([], MatchAny)" |
 "primitive_extractor (disc,sel) (Match a) = (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a))" |
 "primitive_extractor (disc,sel) (MatchNot (Match a)) = (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)))" |
 "primitive_extractor C (MatchAnd ms1 ms2) = (
        let (a1', ms1') = primitive_extractor C ms1; 
            (a2', ms2') = primitive_extractor C ms2
        in (a1'@a2', MatchAnd ms1' ms2'))" |
 "primitive_extractor _ _ = undefined"

text{*
  The first part returned by @{const primitive_extractor}, here @{text as}:
    A list of primitive match expressions.
    For example, let @{text "m = MatchAnd (Src ip1) (Dst ip2)"} then, using the src @{text "(disc, sel)"}, the result is @{text "[ip1]"}.
    Note that @{text Src} is stripped from the result.

    The second part, here @{text ms} is the match expression which was not extracted.

    Together, the first and second part match iff @{text m} matches.
*}

theorem primitive_extractor_correct: assumes 
  "normalized_nnf_match m" and "wf_disc_sel (disc, sel) C" and "primitive_extractor (disc, sel) m = (as, ms)" 
  shows "matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
  and "normalized_nnf_match ms"
  and "\<not> has_disc disc ms"
  and "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms"
  and "\<forall>disc2 sel2. normalized_n_primitive (disc2, sel2) P m \<longrightarrow> normalized_n_primitive (disc2, sel2) P ms"
proof -
  --"better simplification rule"
  from assms have assm3': "(as, ms) = primitive_extractor (disc, sel) m" by simp
  with assms(1) assms(2) show "matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          apply(simp_all add: bunch_of_lemmata_about_matches wf_disc_sel.simps split: split_if_asm)
    apply(simp split: split_if_asm split_split_asm add: NegPos_map_append)
    apply(auto simp add: alist_and_append bunch_of_lemmata_about_matches)
    done

  from assms(1) assm3' show "normalized_nnf_match ms"
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

  from assms(1) assm3' show "\<not> has_disc disc ms"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          by(simp_all split: split_if_asm split_split_asm)

  from assms(1) assm3' show "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          apply(simp)
         apply(simp split: split_if_asm)
        apply(simp split: split_if_asm)
       apply(clarify) (*the simplifier loops*)
       apply(simp split: split_split_asm)
      apply(simp_all)
    done


  from assms(1) assm3' show "\<forall>disc2 sel2. normalized_n_primitive (disc2, sel2) P m \<longrightarrow> normalized_n_primitive (disc2, sel2) P ms"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          apply(simp)
         apply(simp split: split_if_asm)
        apply(simp split: split_if_asm)
       apply(clarify) (*the simplifier loops*)
       apply(simp split: split_split_asm)
      apply(simp_all)
    done
qed

(*
theorem primitive_extractor_correct': "normalized_nnf_match m \<Longrightarrow> wf_disc_sel discsel C \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C (fst (primitive_extractor discsel m)))) a p \<and> matches \<gamma> (snd (primitive_extractor discsel m)) a p \<longleftrightarrow> matches \<gamma> m a p"
apply(cases discsel)
apply(drule primitive_extractor_correct)
apply auto
done


text{*
  You can apply @{const primitive_extractor} iteratively on the returned match expression (second part of tuple) to extract all desired match fields.
*}


lemma primitive_extractor_normalized_helper: "normalized_nnf_match m \<Longrightarrow> (as, ms) = primitive_extractor discsel m \<Longrightarrow> normalized_nnf_match ms"
  apply(induction discsel m  arbitrary: as ms rule: primitive_extractor.induct)
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
  
lemma primitive_extractor_normalized: "normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> normalized_nnf_match ms"
using primitive_extractor_normalized_helper by metis



lemma primitive_extractor_has_disc_helper: "normalized_nnf_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> \<not> has_disc disc ms"
  apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  apply(simp_all split: split_if_asm split_split_asm)
  done

lemma primitive_extractor_has_disc: "normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)\<Longrightarrow> \<not> has_disc disc ms"
using primitive_extractor_has_disc_helper by metis


lemma primitive_extractor_has_disc2_helper: "\<not> has_disc disc2 m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> (as, ms) = primitive_extractor (disc, sel) m \<Longrightarrow> \<not> has_disc disc2 ms"
apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
apply(simp)
apply(simp split: split_if_asm)
apply(simp split: split_if_asm)
apply(clarify) (*the simplifier loops*)
apply(simp split: split_split_asm)
apply(simp_all)
done

lemma primitive_extractor_has_disc2: "\<not> has_disc disc2 m \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> \<not> has_disc disc ms \<and> \<not> has_disc disc2 ms"
apply(rule conjI)
using primitive_extractor_has_disc_helper apply(metis)
using primitive_extractor_has_disc2_helper apply metis
done
*)


lemma primitive_extractor_matchesE: "wf_disc_sel (disc,sel) C \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)
  \<Longrightarrow>
  (normalized_nnf_match ms \<Longrightarrow> \<not> has_disc disc ms \<Longrightarrow> (\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms) \<Longrightarrow> matches_other \<longleftrightarrow>  matches \<gamma> ms a p)
  \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches_other \<longleftrightarrow>  matches \<gamma> m a p"
using primitive_extractor_correct by metis

lemma primitive_extractor_matches_lastE: "wf_disc_sel (disc,sel) C \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)
  \<Longrightarrow>
  (normalized_nnf_match ms \<Longrightarrow> \<not> has_disc disc ms \<Longrightarrow> (\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms) \<Longrightarrow> matches \<gamma> ms a p)
  \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C as)) a p  \<longleftrightarrow>  matches \<gamma> m a p"
using primitive_extractor_correct by metis

text{*The lemmas @{thm primitive_extractor_matchesE} and @{thm primitive_extractor_matches_lastE} can be used as
  erule to solve goals about consecutive application of @{const primitive_extractor}.
  They should be used as @{text "primitive_extractor_matchesE[OF wf_disc_sel_for_first_extracted_thing]"}.
  *}



subsection{*Normalizing and Optimizing Primitives*}
  text{*
    Normalize primitives by a function @{text f} with type @{typ "'b negation_type list \<Rightarrow> 'b list"}.
    @{typ "'b"} is a primitive type, e.g. ipt_ipv4range.
    @{text f} takes a conjunction list of negated primitives and must compress them such that:
      * no negation occurs in the output
      * the output is a disjunction of the primitives, i.e. multiple primitives in one rule are compressed to at most one primitive (leading to multiple rules)

    Example with IP addresses:
      f [10.8.0.0/16, 10.0.0.0/8] = [10.0.0.0/8]  f compresses to one range
      f [10.0.0.0, 192.168.0.01] = []    range is empty, rule can be dropped
      f [Neg 41] = [{0..40}, {42..ipv4max}]   one rule is translated into multiple rules to translate negation
      f [Neg 41, {20..50}, {30..50}] = [{30..40}, {42..50}]   input: conjunction list, output disjunction list!
  *}
  definition normalize_primitive_extract :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow>
                               ('b \<Rightarrow> 'a) \<Rightarrow>
                               ('b negation_type list \<Rightarrow> 'b list) \<Rightarrow>
                               'a match_expr \<Rightarrow> 
                               'a match_expr list" where 
    "normalize_primitive_extract (disc_sel) C f m = (case primitive_extractor (disc_sel) m 
                of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C spt))) rst) (f spts))"
  
                (*TODO: if f spts is empty, we get back an empty list. problem? *)
  
  text{*
    If @{text f} has the properties described above, then @{const normalize_primitive_extract} is a valid transformation of a match expression*}
  lemma normalize_primitive_extract: assumes "normalized_nnf_match m" and "wf_disc_sel disc_sel C" and
        "\<forall>ml. (match_list \<gamma> (map (Match \<circ> C) (f ml)) a p \<longleftrightarrow> matches \<gamma> (alist_and (NegPos_map C ml)) a p)"
        shows "match_list \<gamma> (normalize_primitive_extract disc_sel C f m) a p \<longleftrightarrow> matches \<gamma> m a p"
    proof -
      obtain as ms where pe: "primitive_extractor disc_sel m = (as, ms)" by fastforce

      from pe primitive_extractor_correct(1)[OF assms(1), where \<gamma>=\<gamma> and  a=a and p=p] assms(2) have 
        "matches \<gamma> m a p \<longleftrightarrow> matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p" by(cases disc_sel, blast)
      also have "\<dots> \<longleftrightarrow> match_list \<gamma> (map (Match \<circ> C) (f as)) a p \<and> matches \<gamma> ms a p" using assms(3) by simp
      also have "\<dots> \<longleftrightarrow> match_list \<gamma> (map (\<lambda>spt. MatchAnd (Match (C spt)) ms) (f as)) a p"
        by(simp add: match_list_matches bunch_of_lemmata_about_matches)
      also have "... \<longleftrightarrow> match_list \<gamma> (normalize_primitive_extract disc_sel C f m) a p"
        by(simp add: normalize_primitive_extract_def pe) 
      finally show ?thesis by simp
    qed

  thm match_list_semantics[of \<gamma> "(map (Match \<circ> C) (f ml))" a p "[(alist_and (NegPos_map C ml))]"]

  corollary normalize_primitive_extract_semantics:  assumes "normalized_nnf_match m" and "wf_disc_sel disc_sel C" and
        "\<forall>ml. (match_list \<gamma> (map (Match \<circ> C) (f ml)) a p \<longleftrightarrow> matches \<gamma> (alist_and (NegPos_map C ml)) a p)"
        shows "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (normalize_primitive_extract disc_sel C f m)) s = 
              approximating_bigstep_fun \<gamma> p [Rule m a] s"
  proof -
    from normalize_primitive_extract[OF assms(1) assms(2) assms(3)] have
      "match_list \<gamma> (normalize_primitive_extract disc_sel C f m) a p = matches \<gamma> m a p" .
    also have "\<dots> \<longleftrightarrow> match_list \<gamma> [m] a p" by simp
    finally show ?thesis using match_list_semantics[of \<gamma> "(normalize_primitive_extract disc_sel C f m)" a p "[m]"] by simp
  qed

  lemma normalize_primitive_extract_maintains_normalized:
  assumes "normalized_nnf_match m"
      and "normalized_n_primitive (disc2, sel2) P m"
      and "wf_disc_sel (disc1, sel1) C"
      and "\<forall>a. \<not> disc2 (C a)" --"disc1 and disc2 match for different stuff. e.g. Src_Ports and Dst_Ports"
    shows "\<forall>mn \<in> set (normalize_primitive_extract (disc1, sel1) C f m). normalized_n_primitive (disc2, sel2) P mn \<and> normalized_nnf_match mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_primitive_extract (disc1, sel1) C f m)"
      obtain as ms where as_ms: "primitive_extractor (disc1, sel1) m = (as, ms)" by fastforce
      from as_ms primitive_extractor_correct[OF assms(1) assms(3)] have "normalized_nnf_match ms"
                  and "\<not> has_disc disc1 ms"
                  and "normalized_n_primitive (disc2, sel2) P ms"
        apply -
        apply(fast, fast)
        using assms(2) by(fast)
      from assm2 as_ms have normalize_primitive_extract_unfolded: "mn \<in> ((\<lambda>spt. MatchAnd (Match (C spt)) ms) ` set (f as))"
        unfolding normalize_primitive_extract_def by force
      with `normalized_nnf_match ms` have "normalized_nnf_match mn" by fastforce
      
      from normalize_primitive_extract_unfolded obtain Casms where Casms: "mn = (MatchAnd (Match (C Casms)) ms)" (*and "Casms \<in> set (f as)"*) by blast

      from `normalized_n_primitive (disc2, sel2) P ms` assms(4) have "normalized_n_primitive (disc2, sel2) P (MatchAnd (Match (C Casms)) ms)"
        by(simp)

      with Casms have "normalized_n_primitive (disc2, sel2) P mn" by blast
      with `normalized_nnf_match mn` show "normalized_n_primitive (disc2, sel2) P mn \<and> normalized_nnf_match mn" by simp
    qed



lemma "normalized_n_primitive disc_sel f m \<Longrightarrow>  normalized_nnf_match m"
  apply(induction disc_sel f m rule: normalized_n_primitive.induct)
        apply(simp_all)
        oops


lemma remove_unknowns_generic_not_has_disc: "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (remove_unknowns_generic \<gamma> a m)"
  by(induction \<gamma> a m rule: remove_unknowns_generic.induct) (simp_all)

lemma remove_unknowns_generic_normalized_n_primitive: "normalized_n_primitive disc_sel f m \<Longrightarrow> 
    normalized_n_primitive disc_sel f (remove_unknowns_generic \<gamma> a m)"
  apply(induction \<gamma> a m rule: remove_unknowns_generic.induct)
        apply(simp_all)
  by(case_tac disc_sel, simp)

end
