theory Primitive_Normalization
imports Negation_Type_Matching
begin

section\<open>Primitive Normalization\<close>

subsection\<open>Normalized Primitives\<close>

text\<open>
  Test if a @{text disc} is in the match expression.
  For example, it call tell whether there are some matches for @{text "Src ip"}.
\<close>
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
     apply(simp_all split: if_split_asm)
  by blast

lemma has_disc_negated_positiv_has_disc: "has_disc_negated disc neg m \<or> has_disc_negated disc (\<not> neg) m \<longleftrightarrow> has_disc disc m"
by(induction disc neg m arbitrary: neg rule:has_disc_negated.induct) auto


lemma has_disc_negated_disj_split: 
    "has_disc_negated (\<lambda>a. P a \<or> Q a) neg m \<longleftrightarrow> has_disc_negated P neg m \<or> has_disc_negated Q neg m"
  apply(induction "(\<lambda>a. P a \<or> Q a)" neg m rule: has_disc_negated.induct)
     apply(simp_all)
  by blast

lemma has_disc_alist_and: "has_disc disc (alist_and as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc disc (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)
lemma has_disc_negated_alist_and: "has_disc_negated disc neg (alist_and as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc_negated disc neg (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)
  

lemma has_disc_alist_and': "has_disc disc (alist_and' as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc disc (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and'.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)
lemma has_disc_negated_alist_and': "has_disc_negated disc neg (alist_and' as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc_negated disc neg (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and'.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)


lemma has_disc_alist_and'_append:
  "has_disc disc' (alist_and' (ls1 @ ls2)) \<longleftrightarrow>
      has_disc disc' (alist_and' ls1) \<or> has_disc disc' (alist_and' ls2)"
apply(induction ls1 arbitrary: ls2 rule: alist_and'.induct)
    apply(simp_all)
 apply(case_tac [!] ls2)
   apply(simp_all)
done
lemma has_disc_negated_alist_and'_append:
  "has_disc_negated disc' neg (alist_and' (ls1 @ ls2)) \<longleftrightarrow>
      has_disc_negated disc' neg (alist_and' ls1) \<or> has_disc_negated disc' neg (alist_and' ls2)"
apply(induction ls1 arbitrary: ls2 rule: alist_and'.induct)
    apply(simp_all)
 apply(case_tac [!] ls2)
   apply(simp_all)
done

lemma match_list_to_match_expr_not_has_disc: 
    "\<forall>a. \<not> disc (X a) \<Longrightarrow> \<not> has_disc disc (match_list_to_match_expr (map (Match \<circ> X) ls))"
  apply(induction ls)
   apply(simp; fail)
  by(simp add: MatchOr_def)


lemma "matches ((\<lambda>x _. bool_to_ternary (disc x)), (\<lambda>_ _. False)) (Match x) a p \<longleftrightarrow> has_disc disc (Match x)"
by(simp add: match_raw_ternary bool_to_ternary_simps split: ternaryvalue.split )


fun normalized_n_primitive :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "normalized_n_primitive _ _ MatchAny = True" |
  "normalized_n_primitive (disc, sel) n (Match P) = (if disc P then n (sel P) else True)" |
  "normalized_n_primitive (disc, sel) n (MatchNot (Match P)) = (if disc P then False else True)" |
  "normalized_n_primitive (disc, sel) n (MatchAnd m1 m2) = (normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2)" |
  "normalized_n_primitive _ _ (MatchNot (MatchAnd _ _)) = False" |
  (*"normalized_n_primitive _ _ (MatchNot _) = True" *)
  "normalized_n_primitive _ _ (MatchNot (MatchNot _)) = False" | (*not nnf normalized*)
  "normalized_n_primitive _ _ (MatchNot MatchAny) = True"


lemma normalized_nnf_match_opt_MatchAny_match_expr:
  "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr m)"
  proof-
  have "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr_once m)"
  for m :: "'a match_expr"
  by(induction m rule: opt_MatchAny_match_expr_once.induct) (simp_all)
  thus "normalized_nnf_match m \<Longrightarrow> normalized_nnf_match (opt_MatchAny_match_expr m)"
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(induction rule: repeat_stabilize_induct)
     by(simp)+
  qed

lemma normalized_n_primitive_opt_MatchAny_match_expr:
  "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (opt_MatchAny_match_expr m)"
  proof-

  have "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (opt_MatchAny_match_expr_once m)"
  for m
    proof-
    { fix disc::"('a \<Rightarrow> bool)" and sel::"('a \<Rightarrow> 'b)" and n m1 m2
      have "normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr_once m1) \<Longrightarrow>
           normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr_once m2) \<Longrightarrow>
           normalized_n_primitive (disc, sel) n m1 \<and> normalized_n_primitive (disc, sel) n m2 \<Longrightarrow>
           normalized_n_primitive (disc, sel) n (opt_MatchAny_match_expr_once (MatchAnd m1 m2))"
    by(induction "(MatchAnd m1 m2)" rule: opt_MatchAny_match_expr_once.induct) (auto)
    }note x=this
    assume "normalized_n_primitive disc_sel f m"
    thus ?thesis
      apply(induction disc_sel f m rule: normalized_n_primitive.induct)
            apply simp_all
      using x by simp
    qed
  from this show
    "normalized_n_primitive disc_sel f m \<Longrightarrow> normalized_n_primitive disc_sel f (opt_MatchAny_match_expr m)"
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(induction rule: repeat_stabilize_induct)
     by(simp)+ 
  qed


lemma normalized_n_primitive_imp_not_disc_negated:
  "wf_disc_sel (disc,sel) C \<Longrightarrow> normalized_n_primitive (disc,sel) f m \<Longrightarrow> \<not> has_disc_negated disc False m"
  apply(induction "(disc,sel)" f m rule: normalized_n_primitive.induct)
  by(simp add: wf_disc_sel.simps split: if_split_asm)+

lemma normalized_n_primitive_alist_and: "normalized_n_primitive disc_sel P (alist_and as) \<longleftrightarrow>
      (\<forall> a \<in> set as. normalized_n_primitive disc_sel P (negation_type_to_match_expr a))"
  proof(induction as)
  case Nil thus ?case by simp
  next
  case (Cons a as) thus ?case
    apply(cases disc_sel, cases a)
    by(simp_all add: negation_type_to_match_expr_simps)
  qed

lemma normalized_n_primitive_alist_and': "normalized_n_primitive disc_sel P (alist_and' as) \<longleftrightarrow>
      (\<forall> a \<in> set as. normalized_n_primitive disc_sel P (negation_type_to_match_expr a))"
  apply(cases disc_sel)
  apply(induction as rule: alist_and'.induct)
      by(simp_all add: negation_type_to_match_expr_simps)

lemma not_has_disc_NegPos_map: "\<forall>a. \<not> disc (C a) \<Longrightarrow> \<forall>a\<in>set (NegPos_map C ls).
        \<not> has_disc disc (negation_type_to_match_expr a)"
by(induction C ls rule: NegPos_map.induct) (simp add: negation_type_to_match_expr_def)+

lemma not_has_disc_negated_NegPos_map: "\<forall>a. \<not> disc (C a) \<Longrightarrow> \<forall>a\<in>set (NegPos_map C ls).
        \<not> has_disc_negated disc False (negation_type_to_match_expr a)"
by(induction C ls rule: NegPos_map.induct) (simp add: negation_type_to_match_expr_def)+

lemma normalized_n_primitive_impossible_map: "\<forall>a. \<not> disc (C a) \<Longrightarrow>
  \<forall>m\<in>set (map (Match \<circ> (C \<circ> x)) ls).
     normalized_n_primitive (disc, sel) f m"
  apply(intro ballI)
  apply(induction ls)
   apply(simp; fail)
  apply(simp)
  apply(case_tac m, simp_all) (*3 cases are impossible*)
   apply(fastforce)
  by force

lemma normalized_n_primitive_alist_and'_append:
  "normalized_n_primitive (disc, sel) f (alist_and' (ls1 @ ls2)) \<longleftrightarrow>
      normalized_n_primitive (disc, sel) f (alist_and' ls1) \<and> normalized_n_primitive (disc, sel) f (alist_and' ls2)"
apply(induction ls1 arbitrary: ls2 rule: alist_and'.induct)
    apply(simp_all)
 apply(case_tac [!] ls2)
   apply(simp_all)
done

lemma normalized_n_primitive_if_no_primitive: "normalized_nnf_match m \<Longrightarrow> \<not> has_disc disc m \<Longrightarrow> 
       normalized_n_primitive (disc, sel) f m"
  by(induction "(disc, sel)" f m rule: normalized_n_primitive.induct) (simp)+

lemma normalized_n_primitive_MatchAnd_combine_map: "normalized_n_primitive disc_sel f rst \<Longrightarrow>
       \<forall>m' \<in> (\<lambda>spt. Match (C spt)) ` set pts. normalized_n_primitive disc_sel f m' \<Longrightarrow>
        m' \<in> (\<lambda>spt. MatchAnd (Match (C spt)) rst) ` set pts \<Longrightarrow> normalized_n_primitive disc_sel f m'"
  by(induction disc_sel f m' rule: normalized_n_primitive.induct)
     fastforce+

subsection\<open>Primitive Extractor\<close>

text\<open>
  The following function takes a tuple of functions (@{typ "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b))"}) and a @{typ "'a match_expr"}.
  The passed function tuple must be the discriminator and selector of the datatype package.
  @{text primitive_extractor} filters the @{typ "'a match_expr"} and returns a tuple.
  The first element of the returned tuple is the filtered primitive matches, the second element is the remaining match expression.

  It requires a @{const normalized_nnf_match}.
\<close>
fun primitive_extractor :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> 'a match_expr \<Rightarrow> ('b negation_type list \<times> 'a match_expr)" where
 "primitive_extractor _ MatchAny = ([], MatchAny)" |
 "primitive_extractor (disc,sel) (Match a) = (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a))" |
 "primitive_extractor (disc,sel) (MatchNot (Match a)) = (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)))" |
 "primitive_extractor C (MatchAnd ms1 ms2) = (
        let (a1', ms1') = primitive_extractor C ms1; 
            (a2', ms2') = primitive_extractor C ms2
        in (a1'@a2', MatchAnd ms1' ms2'))" |
 "primitive_extractor _ _ = undefined"

text\<open>
  The first part returned by @{const primitive_extractor}, here @{text as}:
    A list of primitive match expressions.
    For example, let @{text "m = MatchAnd (Src ip1) (Dst ip2)"} then, using the src @{text "(disc, sel)"}, the result is @{text "[ip1]"}.
    Note that @{text Src} is stripped from the result.

    The second part, here @{text ms} is the match expression which was not extracted.

    Together, the first and second part match iff @{text m} matches.
\<close>


(*unused*)
lemma primitive_extractor_fst_simp2:
  fixes m'::"'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr"
  shows "fst (case primitive_extractor (disc, sel) m1 of (a1', ms1') \<Rightarrow> case primitive_extractor (disc, sel) m2 of (a2', ms2') \<Rightarrow> (a1' @ a2', m' ms1' ms2')) =
           fst (primitive_extractor (disc, sel) m1) @ fst (primitive_extractor (disc, sel) m2)"
      apply(cases "primitive_extractor (disc, sel) m1", simp)
      apply(cases "primitive_extractor (disc, sel) m2", simp)
      done

theorem primitive_extractor_correct: assumes 
  "normalized_nnf_match m" and "wf_disc_sel (disc, sel) C" and "primitive_extractor (disc, sel) m = (as, ms)" 
  shows "matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
  and "normalized_nnf_match ms"
  and "\<not> has_disc disc ms"
  and "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms"
  and "\<forall>disc2 sel2. normalized_n_primitive (disc2, sel2) P m \<longrightarrow> normalized_n_primitive (disc2, sel2) P ms"
  and "\<forall>disc2. \<not> has_disc_negated disc2 neg m \<longrightarrow> \<not> has_disc_negated disc2 neg ms"
  and "\<not> has_disc disc m \<Longrightarrow> as = [] \<and> ms = m"
  and "\<not> has_disc_negated disc False m \<longleftrightarrow> getNeg as = []"
proof -
  --"better simplification rule"
  from assms have assm3': "(as, ms) = primitive_extractor (disc, sel) m" by simp
  with assms(1) assms(2) show "matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> ms a p \<longleftrightarrow> matches \<gamma> m a p"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    case 4 thus ?case
      apply(simp split: if_split_asm prod.split_asm add: NegPos_map_append)
      apply(auto simp add: alist_and_append bunch_of_lemmata_about_matches)
      done
    qed(simp_all add: bunch_of_lemmata_about_matches wf_disc_sel.simps split: if_split_asm)

  from assms(1) assm3' show "normalized_nnf_match ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
         case 2 thus ?case by(simp split: if_split_asm)
         next
         case 3 thus ?case by(simp split: if_split_asm)
         next
         case 4 thus ?case 
           apply(clarify) (*if i don't clarify, the simplifier loops*)
           apply(simp split: prod.split_asm)
           done
    qed(simp_all)

  from assms(1) assm3' show "\<not> has_disc disc ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    qed(simp_all split: if_split_asm prod.split_asm)


  from assms(1) assm3' show "\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
         case 2 thus ?case by(simp split: if_split_asm)
         next
         case 3 thus ?case by(simp split: if_split_asm)
         next
         case 4 thus ?case by(simp split: prod.split_asm)
    qed(simp_all)


  from assms(1) assm3' show "\<forall>disc2. \<not> has_disc_negated disc2 neg m \<longrightarrow> \<not> has_disc_negated disc2 neg ms"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
         case 2 thus ?case by(simp split: if_split_asm)
         next
         case 3 thus ?case by(simp split: if_split_asm)
         next
         case 4 thus ?case by(simp split: prod.split_asm)
    qed(simp_all)


  from assms(1) assm3' show "\<forall>disc2 sel2. normalized_n_primitive (disc2, sel2) P m \<longrightarrow> normalized_n_primitive (disc2, sel2) P ms"
    apply(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
          apply(simp)
         apply(simp split: if_split_asm)
        apply(simp split: if_split_asm)
       apply(simp split: prod.split_asm)
      apply(simp_all)
    done

   from assms(1) assm3' show "\<not> has_disc disc m \<Longrightarrow> as = [] \<and> ms = m"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    case 4 thus ?case by(simp split: prod.split_asm)
    qed(simp_all)

   from assms(1) assm3' show "\<not> has_disc_negated disc False m \<longleftrightarrow> getNeg as = []"
    proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
    case 2 thus ?case by(simp split: if_split_asm)
    next
    case 3 thus ?case by(simp split: if_split_asm)
    next
    case 4 thus ?case by(simp add: getNeg_append split: prod.split_asm)
    qed(simp_all)
qed


lemma has_disc_negated_primitive_extractor:
  assumes "normalized_nnf_match m"
  shows "has_disc_negated disc False m \<longleftrightarrow> (\<exists>a. Neg a \<in> set (fst (primitive_extractor (disc, sel) m)))"
proof -
  obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
  hence "has_disc_negated disc False m \<longleftrightarrow> (\<exists>a. Neg a \<in> set as)"
    using assms proof(induction m arbitrary: as ms)
    case Match thus ?case
       by(simp split: if_split_asm) fastforce
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
  qed(simp_all split: if_split_asm)
  thus ?thesis using asms by simp
qed



(*if i extract something and put it together again unchanged, things do not change*)
lemma primitive_extractor_reassemble_preserves:
  "wf_disc_sel (disc, sel) C \<Longrightarrow>
   normalized_nnf_match m \<Longrightarrow>
   P m \<Longrightarrow>
   P MatchAny \<Longrightarrow>
   primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> (*turn eqality around to simplify proof*)
   (\<And>m1 m2. P (MatchAnd m1 m2) \<longleftrightarrow> P m1 \<and> P m2) \<Longrightarrow>
   (\<And>ls1 ls2. P (alist_and' (ls1 @ ls2)) \<longleftrightarrow> P (alist_and' ls1) \<and> P (alist_and' ls2)) \<Longrightarrow>
   P (alist_and' (NegPos_map C as))"
  proof(induction "(disc, sel)" m  arbitrary: as ms rule: primitive_extractor.induct)
  case 2 thus ?case
    apply(simp split: if_split_asm)
    apply(clarify)
    by(simp add: wf_disc_sel.simps)
  next
  case 3 thus ?case
    apply(simp split: if_split_asm)
    apply(clarify)
    by(simp add: wf_disc_sel.simps)
  next
  case (4 m1 m2 as ms)
    from 4 show ?case
      apply(simp)
      apply(simp split: prod.split_asm)
      apply(clarify)
      apply(simp add: NegPos_map_append)
    done
qed(simp_all split: if_split_asm)

lemma primitive_extractor_reassemble_not_has_disc:
  "wf_disc_sel (disc, sel) C \<Longrightarrow>
   normalized_nnf_match m \<Longrightarrow> \<not> has_disc disc' m \<Longrightarrow>
   primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow>
     \<not> has_disc disc' (alist_and' (NegPos_map C as))"
  apply(rule primitive_extractor_reassemble_preserves)
        by(simp_all add: NegPos_map_append has_disc_alist_and'_append)

lemma primitive_extractor_reassemble_not_has_disc_negated:
  "wf_disc_sel (disc, sel) C \<Longrightarrow>
   normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc' neg m \<Longrightarrow>
   primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow> 
     \<not> has_disc_negated disc' neg (alist_and' (NegPos_map C as))"
  apply(rule primitive_extractor_reassemble_preserves)
        by(simp_all add: NegPos_map_append has_disc_negated_alist_and'_append)

lemma primitive_extractor_reassemble_normalized_n_primitive:
  "wf_disc_sel (disc, sel) C \<Longrightarrow>
   normalized_nnf_match m \<Longrightarrow> normalized_n_primitive (disc1, sel1) f m \<Longrightarrow>
   primitive_extractor (disc, sel) m = (as, ms) \<Longrightarrow>
     normalized_n_primitive (disc1, sel1) f (alist_and' (NegPos_map C as))"
  apply(rule primitive_extractor_reassemble_preserves)
        by(simp_all add: NegPos_map_append normalized_n_primitive_alist_and'_append)



lemma primitive_extractor_matchesE: "wf_disc_sel (disc,sel) C \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)
  \<Longrightarrow>
  (normalized_nnf_match ms \<Longrightarrow> \<not> has_disc disc ms \<Longrightarrow> (\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms) \<Longrightarrow> matches_other \<longleftrightarrow>  matches \<gamma> ms a p)
  \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches_other \<longleftrightarrow>  matches \<gamma> m a p"
using primitive_extractor_correct(1,2,3,4) by metis

lemma primitive_extractor_matches_lastE: "wf_disc_sel (disc,sel) C \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> primitive_extractor (disc, sel) m = (as, ms)
  \<Longrightarrow>
  (normalized_nnf_match ms \<Longrightarrow> \<not> has_disc disc ms \<Longrightarrow> (\<forall>disc2. \<not> has_disc disc2 m \<longrightarrow> \<not> has_disc disc2 ms) \<Longrightarrow> matches \<gamma> ms a p)
  \<Longrightarrow>
  matches \<gamma> (alist_and (NegPos_map C as)) a p  \<longleftrightarrow>  matches \<gamma> m a p"
using primitive_extractor_correct(1,2,3,4) by metis

text\<open>The lemmas @{thm primitive_extractor_matchesE} and @{thm primitive_extractor_matches_lastE} can be used as
  erule to solve goals about consecutive application of @{const primitive_extractor}.
  They should be used as @{text "primitive_extractor_matchesE[OF wf_disc_sel_for_first_extracted_thing]"}.
\<close>



subsection\<open>Normalizing and Optimizing Primitives\<close>
  text\<open>
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
\<close>
  definition normalize_primitive_extract :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow>
                               ('b \<Rightarrow> 'a) \<Rightarrow>
                               ('b negation_type list \<Rightarrow> 'b list) \<Rightarrow>
                               'a match_expr \<Rightarrow> 
                               'a match_expr list" where 
    "normalize_primitive_extract (disc_sel) C f m \<equiv> (case primitive_extractor (disc_sel) m 
                of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C spt))) rst) (f spts))"
  
                (*if f spts is empty, we get back an empty list. *)
  
  text\<open>
    If @{text f} has the properties described above, then @{const normalize_primitive_extract} is a valid transformation of a match expression\<close>
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


  lemma normalize_primitive_extract_preserves_nnf_normalized:
  assumes "normalized_nnf_match m"
      and "wf_disc_sel (disc, sel) C"
    shows "\<forall>mn \<in> set (normalize_primitive_extract (disc, sel) C f m). normalized_nnf_match mn"
    proof
      fix mn
      assume assm2: "mn \<in> set (normalize_primitive_extract (disc, sel) C f m)"
      obtain as ms where as_ms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
      from primitive_extractor_correct(2)[OF assms(1) assms(2) as_ms] have "normalized_nnf_match ms" by simp
      from assm2 as_ms have normalize_primitive_extract_unfolded: "mn \<in> ((\<lambda>spt. MatchAnd (Match (C spt)) ms) ` set (f as))"
        unfolding normalize_primitive_extract_def by force
      with \<open>normalized_nnf_match ms\<close> show "normalized_nnf_match mn" by fastforce
    qed

  lemma normalize_rules_primitive_extract_preserves_nnf_normalized:
    "\<forall>r \<in> set rs. normalized_nnf_match (get_match r) \<Longrightarrow> wf_disc_sel disc_sel C \<Longrightarrow>
     \<forall>r \<in> set (normalize_rules (normalize_primitive_extract disc_sel C f) rs). normalized_nnf_match (get_match r)"
  apply(rule normalize_rules_preserves[where P="normalized_nnf_match" and f="(normalize_primitive_extract disc_sel C f)"])
   apply(simp; fail)
  apply(cases disc_sel)
  using normalize_primitive_extract_preserves_nnf_normalized by fast

  text\<open>If something is normalized for disc2 and disc2 @{text \<noteq>} disc1 and we do something on disc1, then disc2 remains normalized\<close>
  lemma normalize_primitive_extract_preserves_unrelated_normalized_n_primitive:
  assumes "normalized_nnf_match m"
      and "normalized_n_primitive (disc2, sel2) P m"
      and "wf_disc_sel (disc1, sel1) C"
      and "\<forall>a. \<not> disc2 (C a)" --\<open>disc1 and disc2 match for different stuff. e.g. @{text Src_Ports} and @{text Dst_Ports}\<close>
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

      from \<open>normalized_n_primitive (disc2, sel2) P ms\<close> assms(4) have "normalized_n_primitive (disc2, sel2) P (MatchAnd (Match (C Casms)) ms)"
        by(simp)

      with Casms show "normalized_n_primitive (disc2, sel2) P mn" by blast
    qed

  
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
      with \<open>normalized_nnf_match ms\<close> have "normalized_n_primitive (disc, sel) P ms"
        by(induction "(disc, sel)" P ms rule: normalized_n_primitive.induct) simp_all

      from \<open>wf_disc_sel (disc, sel) C\<close> have "(sel (C spt)) = spt" by(simp add: wf_disc_sel.simps)
      with np \<open>spt \<in> set (f as)\<close> have "P (sel (C spt))" by simp

      show "normalized_n_primitive (disc, sel) P m'"
      apply(simp add: \<open>m' = MatchAnd (Match (C spt)) ms\<close>)
      apply(rule conjI)
       apply(simp_all add: \<open>normalized_n_primitive (disc, sel) P ms\<close>)
      apply(simp add: \<open>P (sel (C spt))\<close>)
      done
    qed
  qed

 lemma primitive_extractor_negation_type_matching1:
    assumes wf: "wf_disc_sel (disc, sel) C"
        and normalized: "normalized_nnf_match m"
        and a1: "primitive_extractor (disc, sel) m = (as, rest)"
        and a2: "matches \<gamma> m a p"
    shows "(\<forall>m\<in>set (map C (getPos as)). matches \<gamma> (Match m) a p) \<and> 
           (\<forall>m\<in>set (map C (getNeg as)). matches \<gamma> (MatchNot (Match m)) a p)"
  proof -
      from primitive_extractor_correct(1)[OF normalized wf a1] a2 have
        "matches \<gamma> (alist_and (NegPos_map C as)) a p \<and> matches \<gamma> rest a p" by fast
      hence "matches \<gamma> (alist_and (NegPos_map C as)) a p" by blast
      with Negation_Type_Matching.matches_alist_and have
        "(\<forall>m\<in>set (getPos (NegPos_map C as)). matches \<gamma> (Match m) a p) \<and> 
         (\<forall>m\<in>set (getNeg (NegPos_map C as)). matches \<gamma> (MatchNot (Match m)) a p)" by metis
      with getPos_NegPos_map_simp2 getNeg_NegPos_map_simp2 show ?thesis by metis
  qed


text\<open>@{const normalized_n_primitive} does NOT imply @{const normalized_nnf_match}\<close>
lemma "\<exists>m. normalized_n_primitive disc_sel f m \<longrightarrow> \<not> normalized_nnf_match m"
  by(rule_tac x="MatchNot MatchAny" in exI) (simp)


lemma remove_unknowns_generic_not_has_disc: "\<not> has_disc C m \<Longrightarrow> \<not> has_disc C (remove_unknowns_generic \<gamma> a m)"
  by(induction \<gamma> a m rule: remove_unknowns_generic.induct) (simp_all add: remove_unknowns_generic_simps2)

lemma remove_unknowns_generic_not_has_disc_negated: "\<not> has_disc_negated C neg m \<Longrightarrow> \<not> has_disc_negated C neg (remove_unknowns_generic \<gamma> a m)"
  by(induction \<gamma> a m rule: remove_unknowns_generic.induct) (simp_all add: remove_unknowns_generic_simps2)

lemma remove_unknowns_generic_normalized_n_primitive: "normalized_n_primitive disc_sel f m \<Longrightarrow> 
    normalized_n_primitive disc_sel f (remove_unknowns_generic \<gamma> a m)"
  proof(induction \<gamma> a m rule: remove_unknowns_generic.induct)
    case 6 thus ?case by(case_tac disc_sel, simp add: remove_unknowns_generic_simps2)
  qed(simp_all add: remove_unknowns_generic_simps2)



lemma normalize_match_preserves_disc_negated: 
    shows "(\<exists>m_DNF \<in> set (normalize_match m). has_disc_negated disc neg m_DNF) \<Longrightarrow> has_disc_negated disc neg m"
  proof(induction m rule: normalize_match.induct)
  case 3 thus ?case by (simp) blast
  next
  case 4
    from 4 show ?case by(simp) blast
  qed(simp_all)
text\<open>@{const has_disc_negated} is a structural property and @{const normalize_match} is a semantical property.
  @{const normalize_match} removes subexpressions which cannot match. Thus, we cannot show (without complicated assumptions)
  the opposite direction of @{thm normalize_match_preserves_disc_negated}, because a negated primitive
  might occur in a subexpression which will be optimized away.\<close>


corollary i_m_giving_this_a_funny_name_so_i_can_thank_my_future_me_when_sledgehammer_will_find_this_one_day:
  "\<not> has_disc_negated disc neg m \<Longrightarrow> \<forall> m_DNF \<in> set (normalize_match m). \<not> has_disc_negated disc neg m_DNF"
using normalize_match_preserves_disc_negated by blast


lemma not_has_disc_opt_MatchAny_match_expr:
  "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (opt_MatchAny_match_expr m)"
  proof -
    have "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (opt_MatchAny_match_expr_once m)" for m
    by(induction m rule: opt_MatchAny_match_expr_once.induct) simp_all
  thus "\<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (opt_MatchAny_match_expr m)"
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(rule repeat_stabilize_induct)
     by(simp)+
  qed
lemma not_has_disc_negated_opt_MatchAny_match_expr:
  "\<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (opt_MatchAny_match_expr m)"
  proof -
    have "\<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (opt_MatchAny_match_expr_once m)"
    for m
    by(induction m arbitrary: neg rule:opt_MatchAny_match_expr_once.induct) (simp_all)
  thus "\<not> has_disc_negated disc neg m \<Longrightarrow> \<not> has_disc_negated disc neg (opt_MatchAny_match_expr m)"
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(rule repeat_stabilize_induct)
     by(simp)+
  qed

lemma normalize_match_preserves_nodisc:
  "\<not> has_disc disc m \<Longrightarrow> m' \<in> set (normalize_match m) \<Longrightarrow> \<not> has_disc disc m'"
  proof - 
    (*no idea why this statement is necessary*)
    have "\<not> has_disc disc m \<longrightarrow> (\<forall>m' \<in> set (normalize_match m). \<not> has_disc disc m')"
    by(induction m rule: normalize_match.induct) (safe,auto) --"need safe, otherwise simplifier loops"
  thus "\<not> has_disc disc m \<Longrightarrow> m' \<in> set (normalize_match m) \<Longrightarrow> \<not> has_disc disc m'" by blast
qed

lemma not_has_disc_normalize_match:
  "\<not> has_disc_negated disc neg  m \<Longrightarrow> m' \<in> set (normalize_match m) \<Longrightarrow> \<not> has_disc_negated disc neg m'"
  using i_m_giving_this_a_funny_name_so_i_can_thank_my_future_me_when_sledgehammer_will_find_this_one_day by blast

lemma normalize_match_preserves_normalized_n_primitive:
  "normalized_n_primitive disc_sel f rst \<Longrightarrow>
        \<forall> m \<in> set (normalize_match rst). normalized_n_primitive disc_sel f m"
apply(cases disc_sel, simp)
apply(induction rst rule: normalize_match.induct)
      apply(simp; fail)
     apply(simp; fail)
    apply(simp; fail)
   using normalized_n_primitive.simps(5) apply metis (*simp loops*)
  by simp+




subsection\<open>Optimizing a match expression\<close>

  text\<open>Optimizes a match expression with a function that takes @{typ "'b negation_type list"}
  and returns @{typ "('b list \<times> 'b list) option"}.
  The function should return @{const None} if the match expression cannot match.
  It returns @{term "Some (as_pos, as_neg)"} where @{term as_pos} and @{term as_neg} are lists of
  primitives. Positive and Negated.
  The result is one match expression.

  In contrast @{const normalize_primitive_extract} returns a list of match expression, to be read es their disjunction.\<close>

  definition compress_normalize_primitive :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow>
                                              ('b negation_type list \<Rightarrow> ('b list \<times> 'b list) option) \<Rightarrow> 
                                              'a match_expr \<Rightarrow> 'a match_expr option" where 
    "compress_normalize_primitive disc_sel C f m \<equiv> (case primitive_extractor disc_sel m of (as, rst) \<Rightarrow>
      (map_option (\<lambda>(as_pos, as_neg). MatchAnd
                                       (alist_and' (NegPos_map C ((map Pos as_pos)@(map Neg as_neg))))
                                       rst
                  ) (f as)))"



  lemma compress_normalize_primitive_nnf: "wf_disc_sel disc_sel C \<Longrightarrow> 
      normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive disc_sel C f m = Some m' \<Longrightarrow>
    normalized_nnf_match m'"
    apply(case_tac "primitive_extractor disc_sel m")
    apply(simp add: compress_normalize_primitive_def)
    apply(clarify)
    apply (simp add: normalized_nnf_match_alist_and')
    apply(cases disc_sel, simp)
    using primitive_extractor_correct(2) by blast


  lemma compress_normalize_primitive_not_introduces_C:
    assumes notdisc: "\<not> has_disc disc m"
        and wf: "wf_disc_sel (disc,sel) C'" (*C is allowed to be different from C'*)
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
        and f_preserves: "\<And>as_pos as_neg. f [] = Some (as_pos, as_neg) \<Longrightarrow> as_pos = [] \<and> as_neg = []"
     shows "\<not> has_disc disc m'"
   proof -
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(4)[OF nm wf asms] have 1: "\<not> has_disc disc ms" by simp
        from notdisc primitive_extractor_correct(7)[OF nm wf asms] have 2: "as = [] \<and> ms = m" by simp
        from 1 2 some show ?thesis by(auto dest: f_preserves simp add: compress_normalize_primitive_def asms)
   qed

  lemma compress_normalize_primitive_not_introduces_C_negated:
    assumes notdisc: "\<not> has_disc_negated disc False m"
        and wf: "wf_disc_sel (disc,sel) C"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
        and f_preserves: "\<And>as as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow> getNeg as = [] \<Longrightarrow> as_neg = []"
     shows "\<not> has_disc_negated disc False m'"
   proof -
        obtain as ms where asms: "primitive_extractor (disc,sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(6)[OF nm wf asms] have 1: "\<not> has_disc_negated disc False ms" by simp
        from asms notdisc has_disc_negated_primitive_extractor[OF nm, where disc=disc and sel=sel] have
          "\<forall>a. Neg a \<notin> set as" by(simp)
        hence "getNeg as = []" by (meson NegPos_set(5) image_subset_iff last_in_set)
        with f_preserves have f_preserves': "\<And>as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow> as_neg = []" by simp
        from 1 have "\<And> a b.\<not> has_disc_negated disc False (MatchAnd (alist_and' (NegPos_map C (map Pos a))) ms)"
          by(simp add: has_disc_negated_alist_and' NegPos_map_map_Pos negation_type_to_match_expr_simps)
        with some show ?thesis by(auto dest: f_preserves' simp add: compress_normalize_primitive_def asms)
   qed




  lemma compress_normalize_primitive_Some:
  assumes normalized: "normalized_nnf_match m"
      and wf: "wf_disc_sel (disc,sel) C"
      and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
      and f_correct: "\<And>as as_pos as_neg. f as = Some (as_pos, as_neg) \<Longrightarrow>
            matches \<gamma> (alist_and (NegPos_map C ((map Pos as_pos)@(map Neg as_neg)))) a p \<longleftrightarrow>
            matches \<gamma> (alist_and (NegPos_map C as)) a p"
    shows "matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
    using some
    apply(simp add: compress_normalize_primitive_def)
    apply(case_tac "primitive_extractor (disc,sel) m")
    apply(rename_tac as rst, simp)
    apply(drule primitive_extractor_correct(1)[OF normalized wf, where \<gamma>=\<gamma> and a=a and p=p])
    apply(elim exE conjE)
    apply(drule f_correct)
    by (meson matches_alist_and_alist_and' bunch_of_lemmata_about_matches(1))
    

  lemma compress_normalize_primitive_None:
  assumes normalized: "normalized_nnf_match m"
      and wf: "wf_disc_sel (disc,sel) C"
      and none: "compress_normalize_primitive (disc,sel) C f m = None"
      and f_correct: "\<And>as. f as = None \<Longrightarrow> \<not> matches \<gamma> (alist_and (NegPos_map C as)) a p"
    shows "\<not> matches \<gamma> m a p"
    using none
    apply(simp add: compress_normalize_primitive_def)
    apply(case_tac "primitive_extractor (disc, sel) m")
    apply(auto dest: primitive_extractor_correct(1)[OF assms(1) wf] f_correct)
    done



  (* only for arbitrary discs that do not match C*)
  lemma compress_normalize_primitive_hasdisc:
    assumes am: "\<not> has_disc disc2 m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc disc2 m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(4)[OF nm wf asms] have 1: "\<not> has_disc disc2 ms" by simp
        { fix is_pos is_neg
          from disc have x1: "\<not> has_disc disc2 (alist_and' (NegPos_map C (map Pos is_pos)))"
            by(simp add: has_disc_alist_and' NegPos_map_map_Pos negation_type_to_match_expr_simps)
          from disc have x2: "\<not> has_disc disc2 (alist_and' (NegPos_map C (map Neg is_neg)))"
            by(simp add: has_disc_alist_and' NegPos_map_map_Neg negation_type_to_match_expr_simps)
          from x1 x2 have "\<not> has_disc disc2 (alist_and' (NegPos_map C (map Pos is_pos @ map Neg is_neg)))"
            apply(simp add: NegPos_map_append has_disc_alist_and') by blast
        }
        with some have "\<not> has_disc disc2 m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 by fastforce
        with goal1 show ?thesis by simp
   qed
  lemma compress_normalize_primitive_hasdisc_negated:
    assumes am: "\<not> has_disc_negated disc2 neg m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc_negated disc2 neg m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(6)[OF nm wf asms] have 1: "\<not> has_disc_negated disc2 neg ms" by simp
        { fix is_pos is_neg
          from disc have x1: "\<not> has_disc_negated disc2 neg (alist_and' (NegPos_map C (map Pos is_pos)))"
            by(simp add: has_disc_negated_alist_and' NegPos_map_map_Pos negation_type_to_match_expr_simps)
          from disc have x2: "\<not> has_disc_negated disc2 neg (alist_and' (NegPos_map C (map Neg is_neg)))"
            by(simp add: has_disc_negated_alist_and' NegPos_map_map_Neg negation_type_to_match_expr_simps)
          from x1 x2 have "\<not> has_disc_negated disc2 neg (alist_and' (NegPos_map C (map Pos is_pos @ map Neg is_neg)))"
            apply(simp add: NegPos_map_append has_disc_negated_alist_and') by blast
        }
        with some have "\<not> has_disc_negated disc2 neg m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 by fastforce
          
        with goal1 show ?thesis by simp
   qed


  thm normalize_primitive_extract_preserves_unrelated_normalized_n_primitive (*is similar*)
  lemma compress_normalize_primitve_preserves_normalized_n_primitive:
    assumes am: "normalized_n_primitive (disc2, sel2) P m"
        and wf: "wf_disc_sel (disc,sel) C"
        and disc: "(\<forall>a. \<not> disc2 (C a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_primitive (disc,sel) C f m = Some m'"
     shows "normalized_nnf_match m' \<and> normalized_n_primitive (disc2, sel2) P m'"
   proof -
        from compress_normalize_primitive_nnf[OF wf nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (disc, sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct[OF nm wf asms] have 1: "normalized_n_primitive (disc2, sel2) P ms" by fast
        { fix iss
          from disc have "normalized_n_primitive (disc2, sel2) P (alist_and (NegPos_map C iss))"
            apply(induction iss)
             apply(simp_all)
            apply(rename_tac i iss, case_tac i)
             apply(simp_all)
            done
        }
        with some have "normalized_n_primitive (disc2, sel2) P m'"
          apply(simp add: compress_normalize_primitive_def asms)
          apply(elim exE conjE)
          using 1 normalized_n_primitive_alist_and' normalized_n_primitive_alist_and
                 normalized_n_primitive.simps(4) by blast 
        with goal1 show ?thesis by simp
   qed



subsection\<open>Processing a list of normalization functions\<close>

fun compress_normalize_primitive_monad :: "('a match_expr \<Rightarrow> 'a match_expr option) list \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr option" where
  "compress_normalize_primitive_monad [] m = Some m" |
  "compress_normalize_primitive_monad (f#fs) m = (case f m of None \<Rightarrow> None
                                                           |  Some m' \<Rightarrow> compress_normalize_primitive_monad fs m')"

lemma compress_normalize_primitive_monad: 
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "normalized_nnf_match m"
          and "(compress_normalize_primitive_monad fs m) = Some m'"
      shows "matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p" (is ?goal1)
        and "normalized_nnf_match m'"              (is ?goal2)
  proof -
    (*everything in one big induction*)
    have goals: "?goal1 \<and> ?goal2"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs)
      from Cons.prems(1) have IH_prem1:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p = matches \<gamma> m a p)" by auto
      from Cons.prems(2) have IH_prem2:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m')" by auto
      from Cons.IH IH_prem1 IH_prem2 have
        IH: "\<And>m. normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive_monad fs m = Some m' \<Longrightarrow>
                  (matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p) \<and> ?goal2" by fast
      show ?case
        proof(cases "f m")
          case None thus ?thesis using Cons.prems by auto
        next
          case(Some m'')
            from Some Cons.prems(1)[of f] Cons.prems(3) have 1: "matches \<gamma> m'' a p = matches \<gamma> m a p" by simp
            from Some Cons.prems(2)[of f] Cons.prems(3) have 2: "normalized_nnf_match m''" by simp
            from Some have "compress_normalize_primitive_monad (f # fs) m = compress_normalize_primitive_monad fs m''" by simp
            thus ?thesis using Cons.prems(4) IH 1 2 by auto 
        qed
    qed
    from goals show ?goal1 by simp
    from goals show ?goal2 by simp
  qed

(*proof is a bit sledgehammered*)
lemma compress_normalize_primitive_monad_None: 
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p \<longleftrightarrow> matches \<gamma> m a p"
          and "\<And>m f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a p"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "normalized_nnf_match m"
          and "(compress_normalize_primitive_monad fs m) = None"
      shows "\<not> matches \<gamma> m a p"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs)
      from Cons.prems(1) have IH_prem1:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p = matches \<gamma> m a p)" by auto
      from Cons.prems(2) have IH_prem2:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a p)" by auto
      from Cons.prems(3) have IH_prem3:
        "(\<And>f m m'. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m')" by auto
      from Cons.IH IH_prem1 IH_prem2 IH_prem3 have
        IH: "\<And>m. normalized_nnf_match m \<Longrightarrow> compress_normalize_primitive_monad fs m = None \<Longrightarrow> \<not>  matches \<gamma> m a p" by blast
      show ?case
        proof(cases "f m")
          case None thus ?thesis using Cons.prems(4) Cons.prems(2) Cons.prems(3) by auto
        next
          case(Some m'')
            from Some Cons.prems(3)[of f] Cons.prems(4) have 2: "normalized_nnf_match m''" by simp
            from Some have "compress_normalize_primitive_monad (f # fs) m = compress_normalize_primitive_monad fs m''" by simp
            hence "\<not> matches \<gamma> m'' a p" using Cons.prems(5) IH 2 by simp
            thus ?thesis using Cons.prems(1) Cons.prems(4) Some by auto 
        qed
    qed


lemma compress_normalize_primitive_monad_preserves:
      assumes "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> f m = Some m' \<Longrightarrow> normalized_nnf_match m'"
          and "\<And>m m' f. f \<in> set fs \<Longrightarrow> normalized_nnf_match m \<Longrightarrow> P m \<Longrightarrow> f m = Some m' \<Longrightarrow> P m'"
          and "normalized_nnf_match m"
          and "P m"
          and "(compress_normalize_primitive_monad fs m) = Some m'"
      shows "normalized_nnf_match m' \<and> P m'"
    using assms proof(induction fs arbitrary: m)
    case Nil thus ?case by simp
    next
    case (Cons f fs) thus ?case by(simp split: option.split_asm) blast (*1s*)
    qed




(*TODO: move to generic place and use? ? ? *)
datatype 'a match_compress = CannotMatch | MatchesAll | MatchExpr 'a


end
