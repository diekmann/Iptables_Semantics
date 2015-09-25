theory Primitive_Normalization
imports Negation_Type_Matching
begin

section{*Primitive Normalization*}

subsection{*Normalized Primitives*}

text{*
  Test if a @{text disc} is in the match expression.
  For example, it call tell whether there are some matches for @{text "Src ip"}.
*}
fun has_disc :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_disc _ MatchAny = False" |
  "has_disc disc (Match a) = disc a" |
  "has_disc disc (MatchNot m) = has_disc disc m" |
  "has_disc disc (MatchAnd m1 m2) = (has_disc disc m1 \<or> has_disc disc m2)"

fun has_disc_negated :: "('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_disc_negated _    _   MatchAny = False" |
  "has_disc_negated disc neg (Match a) = (if disc a then neg else False)" |
  "has_disc_negated disc neg (MatchNot m) = has_disc_negated disc (\<not> neg) m" |
  "has_disc_negated disc neg (MatchAnd m1 m2) = (has_disc_negated disc neg m1 \<or> has_disc_negated disc neg m2)"

lemma "\<not> has_disc_negated (\<lambda>x::nat. x = 0) False (MatchAnd (Match 0) (MatchNot (Match 1)))" by eval
lemma "has_disc_negated (\<lambda>x::nat. x = 0) False (MatchAnd (Match 0) (MatchNot (Match 0)))" by eval
lemma "has_disc_negated (\<lambda>x::nat. x = 0) True (MatchAnd (Match 0) (MatchNot (Match 1)))" by eval
lemma "\<not> has_disc_negated (\<lambda>x::nat. x = 0) True (MatchAnd (Match 1) (MatchNot (Match 0)))" by eval
lemma "has_disc_negated (\<lambda>x::nat. x = 0) True (MatchAnd (Match 0) (MatchNot (Match 0)))" by eval

-- "We want false on the right hand side, because this is how the algorithm should be started"
lemma has_disc_negated_MatchNot:
  "has_disc_negated disc True (MatchNot m) \<longleftrightarrow> has_disc_negated disc False m"
  "has_disc_negated disc True m \<longleftrightarrow> has_disc_negated disc False (MatchNot m)"
  by(induction m) (simp_all)

lemma has_disc_negated_has_disc: "has_disc_negated disc neg m \<Longrightarrow> has_disc disc m"
  apply(induction m arbitrary: neg)
     apply(simp_all split: split_if_asm)
  by blast

lemma has_disc_negated_positiv_has_disc: "has_disc_negated disc neg m \<or> has_disc_negated disc (\<not> neg) m \<longleftrightarrow> has_disc disc m"
by(induction disc neg m arbitrary: neg rule:has_disc_negated.induct) auto


fun normalized_n_primitive :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "normalized_n_primitive _ _ MatchAny = True" |
  "normalized_n_primitive (disc, sel) n (Match (P)) = (if disc P then n (sel P) else True)" |
  "normalized_n_primitive (disc, sel) n (MatchNot (Match (P))) = (if disc P then False else True)" |
  "normalized_n_primitive (disc, sel) n (MatchAnd m1 m2) = (normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2)" |
  "normalized_n_primitive _ _ (MatchNot (MatchAnd _ _)) = False" |
  (*"normalized_n_primitive _ _ (MatchNot _) = True" *)
  "normalized_n_primitive _ _ (MatchNot (MatchNot _)) = False" | (*not nnf normalized*)
  "normalized_n_primitive _ _ (MatchNot MatchAny) = True"



lemma normalized_n_primitive_opt_MatchAny_match_expr: "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (opt_MatchAny_match_expr m)"
  proof-
  { fix disc::"('a \<Rightarrow> bool)" and sel::"('a \<Rightarrow> 'b)" and n m1 m2
    have "normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr m1) \<Longrightarrow>
         normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr m2) \<Longrightarrow>
         normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2 \<Longrightarrow>
         normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr (MatchAnd m1 m2))"
  by(induction "(MatchAnd m1 m2)" rule: opt_MatchAny_match_expr.induct) (auto)
  }note x=this
  assume "normalized_n_primitive disc_sel f m"
  thus ?thesis
    apply(induction disc_sel f m rule: normalized_n_primitive.induct)
          apply simp_all
    using x by simp
  qed


subsection{*Primitive Extractor*}

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
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    case 4 thus ?case
      apply(simp split: split_if_asm split_split_asm add: NegPos_map_append)
      apply(auto simp add: alist_and_append bunch_of_lemmata_about_matches)
      done
    qed(simp_all add: bunch_of_lemmata_about_matches wf_disc_sel.simps split: split_if_asm)

  from assms(1) assm3' show "normalized_nnf_match ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
         case 2 thus ?case by(simp split: split_if_asm)
         next
         case 3 thus ?case by(simp split: split_if_asm)
         next
         case 4 thus ?case 
           apply(clarify) (*if i don't clarify, the simplifier loops*)
           apply(simp split: split_split_asm)
           done
    qed(simp_all)

  from assms(1) assm3' show "\<not> has_disc disc ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    qed(simp_all split: split_if_asm split_split_asm)

  from assms(1) assm3' show "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
         case 2 thus ?case by(simp split: split_if_asm)
         next
         case 3 thus ?case by(simp split: split_if_asm)
         next
         case 4 thus ?case by(simp split: split_split_asm)
    qed(simp_all)


  from assms(1) assm3' show "\<forall>disc2 sel2. normalized_n_primitive (disc2, sel2) P m \<longrightarrow> normalized_n_primitive (disc2, sel2) P ms"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          apply(simp)
         apply(simp split: split_if_asm)
        apply(simp split: split_if_asm)
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
    @{typ "'b"} is a primitive type, e.g. ipt-ipv4range.
    @{text f} takes a conjunction list of negated primitives and must compress them such that:
    \begin{enumerate}
      \item no negation occurs in the output
      \item the output is a disjunction of the primitives, i.e. multiple primitives in one rule are compressed to at most one primitive (leading to multiple rules)
    \end{enumerate}
    Example with IP addresses:
    \begin{verbatim}
      f [10.8.0.0/16, 10.0.0.0/8] = [10.0.0.0/8]  f compresses to one range
      f [10.0.0.0, 192.168.0.01] = []    range is empty, rule can be dropped
      f [Neg 41] = [{0..40}, {42..ipv4max}]   one rule is translated into multiple rules to translate negation
      f [Neg 41, {20..50}, {30..50}] = [{30..40}, {42..50}]   input: conjunction list, output disjunction list!
    \end{verbatim}
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

  (*lemma normalize_primitive_extract_preserves_normalized:
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
    qed*)


  lemma normalize_primitive_extract_preserves_nnf_normalized:
  assumes "normalized_nnf_match m"
      and "wf_disc_sel (disc, sel) C"
    shows "\<forall>mn \<in> set (normalize_primitive_extract (disc, sel) C f m). normalized_nnf_match mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_primitive_extract (disc, sel) C f m)"
      obtain as ms where as_ms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
      from as_ms primitive_extractor_correct[OF assms(1) assms(2)] have "normalized_nnf_match ms" by simp
      from assm2 as_ms have normalize_primitive_extract_unfolded: "mn \<in> ((\<lambda>spt. MatchAnd (Match (C spt)) ms) ` set (f as))"
        unfolding normalize_primitive_extract_def by force
      with `normalized_nnf_match ms` show "normalized_nnf_match mn" by fastforce
    qed

  lemma normalize_rules_primitive_extract_preserves_nnf_normalized:
    "\<forall>m\<in>get_match ` set rs. normalized_nnf_match m \<Longrightarrow> wf_disc_sel disc_sel C \<Longrightarrow>
     \<forall>m\<in>get_match ` set (normalize_rules (normalize_primitive_extract disc_sel C f) rs). normalized_nnf_match m"
  apply(rule normalize_rules_preserves[where P="normalized_nnf_match" and f="(normalize_primitive_extract disc_sel C f)"])
   apply(simp)
  apply(cases disc_sel)
  using normalize_primitive_extract_preserves_nnf_normalized by fast

  text{*If something is normalized for disc2 and disc2 @{text \<noteq>} disc1 and we do something on disc1, then disc2 remains normalized*}
  lemma normalize_primitive_extract_preserves_unrelated_normalized_n_primitive:
  assumes "normalized_nnf_match m"
      and "normalized_n_primitive (disc2, sel2) P m"
      and "wf_disc_sel (disc1, sel1) C"
      and "\<forall>a. \<not> disc2 (C a)" --{*disc1 and disc2 match for different stuff. e.g. @{text Src_Ports} and @{text Dst_Ports}*}
    shows "\<forall>mn \<in> set (normalize_primitive_extract (disc1, sel1) C f m). normalized_n_primitive (disc2, sel2) P mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_primitive_extract (disc1, sel1) C f m)"
      obtain as ms where as_ms: "primitive_extractor (disc1, sel1) m = (as, ms)" by fastforce
      from as_ms primitive_extractor_correct[OF assms(1) assms(3)] have 
                      "\<not> has_disc disc1 ms"
                  and "normalized_n_primitive (disc2, sel2) P ms"
        apply -
        apply(fast)
        using assms(2) by(fast)
      from assm2 as_ms have normalize_primitive_extract_unfolded: "mn \<in> ((\<lambda>spt. MatchAnd (Match (C spt)) ms) ` set (f as))"
        unfolding normalize_primitive_extract_def by force
      
      from normalize_primitive_extract_unfolded obtain Casms where Casms: "mn = (MatchAnd (Match (C Casms)) ms)" by blast

      from `normalized_n_primitive (disc2, sel2) P ms` assms(4) have "normalized_n_primitive (disc2, sel2) P (MatchAnd (Match (C Casms)) ms)"
        by(simp)

      with Casms show "normalized_n_primitive (disc2, sel2) P mn" by blast
    qed


(*those should hold*)
thm wf_disc_sel.simps 
lemma "wf_disc_sel (disc, sel) C \<Longrightarrow> \<forall>x. disc (C x)" quickcheck oops
lemma "wf_disc_sel (disc, sel) C \<Longrightarrow> disc (C x) \<longrightarrow> sel (C x) = x"
  by(simp add: wf_disc_sel.simps)
  
  lemma normalize_primitive_extract_normalizes_n_primitive:
  fixes disc::"('a \<Rightarrow> bool)" and sel::"('a \<Rightarrow> 'b)" and f::"('b negation_type list \<Rightarrow> 'b list)"
  assumes "normalized_nnf_match m"
      and "wf_disc_sel (disc, sel) C"
      and np: "\<forall>as. (\<forall> a' \<in> set (f as). P a')" (*not quite, sel f   \<forall>as \<in> {x. disc (v x)}. *)
    shows "\<forall>m' \<in> set (normalize_primitive_extract (disc, sel) C f m). normalized_n_primitive (disc, sel) P m'"
    proof
    fix m' assume a: "m'\<in>set (normalize_primitive_extract (disc, sel) C f m)"

    have nnf: "\<forall>m' \<in> set (normalize_primitive_extract (disc, sel) C f m). normalized_nnf_match m'"
      using normalize_primitive_extract_preserves_nnf_normalized assms by blast
    with a have normalized_m': "normalized_nnf_match m'" by simp

    from a obtain as ms where as_ms: "primitive_extractor (disc, sel) m = (as, ms)"
      unfolding normalize_primitive_extract_def by fastforce
    with a have prems: "m' \<in> set (map (\<lambda>spt. MatchAnd (Match (C spt)) ms) (f as))"
      unfolding normalize_primitive_extract_def by simp


    from primitive_extractor_correct(2)[OF assms(1) assms(2) as_ms] have "normalized_nnf_match ms" .
    
    show "normalized_n_primitive (disc, sel) P m'"
    proof(cases "f as = []")
    case True thus "normalized_n_primitive (disc, sel) P m'" using prems by simp
    next
    case False
      with prems obtain spt where "m' = MatchAnd (Match (C spt)) ms" and "spt \<in> set (f as)" by auto

      from primitive_extractor_correct(3)[OF assms(1) assms(2) as_ms] have "\<not> has_disc disc ms" .
      with `normalized_nnf_match ms` have "normalized_n_primitive (disc, sel) P ms"
        by(induction "(disc, sel)" P ms rule: normalized_n_primitive.induct) simp_all

      (*
      from primitive_extractor_correct(4)[OF assms(1) assms(2) as_ms] have "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms" .*)

      from `wf_disc_sel (disc, sel) C` have "(sel (C spt)) = spt" by(simp add: wf_disc_sel.simps)
      with np `spt \<in> set (f as)` have "P (sel (C spt))" by simp

      show "normalized_n_primitive (disc, sel) P m'"
      apply(simp add: `m' = MatchAnd (Match (C spt)) ms`)
      apply(rule conjI)
       apply(simp_all add: `normalized_n_primitive (disc, sel) P ms`)
      apply(simp add: `P (sel (C spt))`)
      done
    qed
  qed


text{*@{const normalized_n_primitive} does NOT imply @{const normalized_nnf_match}*}
lemma "\<exists>m. normalized_n_primitive disc_sel f m \<longrightarrow> \<not> normalized_nnf_match m"
  apply(rule_tac x="MatchNot MatchAny" in exI)
  apply(simp)
  done


lemma remove_unknowns_generic_not_has_disc: "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (remove_unknowns_generic \<gamma> a m)"
  by(induction \<gamma> a m rule: remove_unknowns_generic.induct) (simp_all)

lemma remove_unknowns_generic_normalized_n_primitive: "normalized_n_primitive disc_sel f m \<Longrightarrow> 
    normalized_n_primitive disc_sel f (remove_unknowns_generic \<gamma> a m)"
  proof(induction \<gamma> a m rule: remove_unknowns_generic.induct)
    case 6 thus ?case by(case_tac disc_sel, simp)
  qed(simp_all)


lemma has_disc_negated_primitive_extractor:
  assumes "normalized_nnf_match m" and "primitive_extractor (disc, sel) m = (as, ms)"
    shows "has_disc_negated disc False m \<longleftrightarrow> (\<exists>a. Neg a \<in> set as)"
    using assms proof(induction m arbitrary: as ms) (*probably rule: primitive_extractor.induct*)
    case Match thus ?case
       apply(simp split: split_if_asm)
       apply fastforce
       done
    next
    case (MatchNot m)
      thus ?case
      proof(induction m)
      case Match thus ?case by (simp, fastforce)
      qed(simp_all)
    next
    case (MatchAnd m1 m2) thus ?case
      apply(cases "primitive_extractor (disc, sel) m1")
      apply(cases "primitive_extractor (disc, sel) m2")
      by auto
  qed(simp_all split: split_if_asm)


lemma primitive_extractor_obtain: obtains as ms  where"primitive_extractor (disc, sel) m = (as, ms)"
  by fastforce

lemma has_disc_negated_primitive_extractor2:
  "normalized_nnf_match m \<Longrightarrow> has_disc_negated disc False m \<longleftrightarrow> (\<exists>a. Neg a \<in> set (fst (primitive_extractor (disc, sel) m)))"
apply(rule primitive_extractor_obtain[of disc sel m])
apply(drule(1) has_disc_negated_primitive_extractor[of m disc sel])
by simp

lemma primitive_extractor_fst_simp: "fst (case primitive_extractor (disc, sel) m_DNF of (as, ms) \<Rightarrow> (as, ms2 ms)) =
       fst (primitive_extractor (disc, sel) m_DNF)"
  by(cases "primitive_extractor (disc, sel) m_DNF", simp)

lemma primitive_extractor_fst_simp2: 
  "fst (case primitive_extractor (disc, sel) m1 of (a1', ms1') \<Rightarrow> case primitive_extractor (disc, sel) m2 of (a2', ms2') \<Rightarrow> (a1' @ a2', m' ms1' ms2')) =
       fst (primitive_extractor (disc, sel) m1) @ fst (primitive_extractor (disc, sel) m2)"
  apply(cases "primitive_extractor (disc, sel) m1", simp)
  apply(cases "primitive_extractor (disc, sel) m2", simp)
  done


lemma normalize_match_not_matcheq_matchNone: "\<forall>m' \<in> set (normalize_match m). \<not> matcheq_matchNone m'"
  apply(induction m rule: normalize_match.induct)
        apply(simp_all)
  by blast
 

lemma normalize_match_empty_iff_matcheq_matchNone: "normalize_match m = [] \<longleftrightarrow> matcheq_matchNone m "
  proof(induction m rule: normalize_match.induct) 
  case 3 thus ?case
    apply simp by fastforce
  qed(simp_all)



lemma dir1:
    shows "(\<exists>m_DNF \<in> set (normalize_match m). \<exists>a. Neg a \<in> set (fst (primitive_extractor (disc, sel) m_DNF))) \<Longrightarrow> has_disc_negated disc False m"
 apply(induction m rule: normalize_match.induct)
       apply(simp_all)
    apply(simp_all split: split_if_asm)
  apply(clarify)
  apply(simp add: primitive_extractor_fst_simp2)
  apply blast
 by blast
(*TODO: the other direction would be nice*)
corollary dir1': 
    shows "(\<exists>m_DNF \<in> set (normalize_match m). has_disc_negated disc neg m_DNF) \<Longrightarrow> has_disc_negated disc neg m"
 apply(induction m rule: normalize_match.induct)
       apply(simp_all)
  apply(clarify)
  apply(simp add: primitive_extractor_fst_simp2)
  apply blast
 by blast




end
