theory Matching_Ternary
imports "../Common/Ternary" "../Firewall_Common"
begin


section\<open>Packet Matching in Ternary Logic\<close>

text\<open>The matcher for a primitive match expression @{typ "'a"}\<close>
type_synonym ('a, 'packet) exact_match_tac="'a \<Rightarrow> 'packet \<Rightarrow> ternaryvalue"

text\<open>
If the matching is @{const TernaryUnknown}, it can be decided by the action whether this rule matches.
E.g. in doubt, we allow packets
\<close>
type_synonym 'packet unknown_match_tac="action \<Rightarrow> 'packet \<Rightarrow> bool"

type_synonym ('a, 'packet) match_tac="(('a, 'packet) exact_match_tac \<times> 'packet unknown_match_tac)"

text\<open>
For a given packet, map a firewall @{typ "'a match_expr"} to a @{typ ternaryformula}
Evaluating the formula gives whether the packet/rule matches (or unknown).
\<close>
fun map_match_tac :: "('a, 'packet) exact_match_tac \<Rightarrow> 'packet \<Rightarrow> 'a match_expr \<Rightarrow> ternaryformula" where
  "map_match_tac \<beta> p (MatchAnd m1 m2) = TernaryAnd (map_match_tac \<beta> p m1) (map_match_tac \<beta> p m2)" |
  "map_match_tac \<beta> p (MatchNot m) = TernaryNot (map_match_tac \<beta> p m)" |
  "map_match_tac \<beta> p (Match m) = TernaryValue (\<beta> m p)" |
  "map_match_tac _ _ MatchAny = TernaryValue TernaryTrue"


context
begin
  text\<open>the @{term ternaryformula}s we construct never have Or expressions.\<close>
  private fun ternary_has_or :: "ternaryformula \<Rightarrow> bool" where
    "ternary_has_or (TernaryOr _ _) \<longleftrightarrow> True" |
    "ternary_has_or (TernaryAnd t1 t2) \<longleftrightarrow> ternary_has_or t1 \<or> ternary_has_or t2" |
    "ternary_has_or (TernaryNot t) \<longleftrightarrow> ternary_has_or t" |
    "ternary_has_or (TernaryValue _) \<longleftrightarrow> False"
  private lemma map_match_tac__does_not_use_TernaryOr: "\<not> (ternary_has_or (map_match_tac \<beta> p m))"
    by(induction m, simp_all)
  declare ternary_has_or.simps[simp del]
end


fun ternary_to_bool_unknown_match_tac :: "'packet unknown_match_tac \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> ternaryvalue \<Rightarrow> bool" where
  "ternary_to_bool_unknown_match_tac _ _ _ TernaryTrue = True" |
  "ternary_to_bool_unknown_match_tac _ _ _ TernaryFalse = False" |
  "ternary_to_bool_unknown_match_tac \<alpha> a p TernaryUnknown = \<alpha> a p"

text\<open>
Matching a packet and a rule:
\begin{enumerate}
  \item Translate @{typ "'a match_expr"} to ternary formula
  \item Evaluate this formula
  \item If @{const TernaryTrue}/@{const TernaryFalse}, return this value
  \item If @{const TernaryUnknown}, apply the @{typ "'a unknown_match_tac"} to get a Boolean result
\end{enumerate}
\<close>
definition matches :: "('a, 'packet) match_tac \<Rightarrow> 'a match_expr \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> bool" where
  "matches \<gamma> m a p \<equiv> ternary_to_bool_unknown_match_tac (snd \<gamma>) a p (ternary_ternary_eval (map_match_tac (fst \<gamma>) p m))"


text\<open>Alternative matches definitions, some more or less convenient\<close>

lemma matches_tuple: "matches (\<beta>, \<alpha>) m a p = ternary_to_bool_unknown_match_tac \<alpha> a p (ternary_ternary_eval (map_match_tac \<beta> p m))"
unfolding matches_def by simp

lemma matches_case: "matches \<gamma> m a p \<longleftrightarrow> (case ternary_eval (map_match_tac (fst \<gamma>) p m) of None \<Rightarrow> (snd \<gamma>) a p | Some b \<Rightarrow> b)"
unfolding matches_def ternary_eval_def
by (cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m))") auto

lemma matches_case_tuple: "matches (\<beta>, \<alpha>) m a p \<longleftrightarrow> (case ternary_eval (map_match_tac \<beta> p m) of None \<Rightarrow> \<alpha> a p | Some b \<Rightarrow> b)"
by (auto simp: matches_case split: option.splits)

lemma matches_case_ternaryvalue_tuple: "matches (\<beta>, \<alpha>) m a p \<longleftrightarrow> (case ternary_ternary_eval (map_match_tac \<beta> p m) of 
        TernaryUnknown \<Rightarrow> \<alpha> a p | 
        TernaryTrue \<Rightarrow> True |
        TernaryFalse \<Rightarrow> False)"
  by(simp split: option.split ternaryvalue.split add: matches_case ternary_to_bool_None ternary_eval_def)
(*use together: matches_case_ternaryvalue_tuple ternaryvalue.split *)


lemma matches_casesE:
  "matches (\<beta>, \<alpha>) m a p \<Longrightarrow> 
    (ternary_ternary_eval (map_match_tac \<beta> p m) = TernaryUnknown \<Longrightarrow> \<alpha> a p \<Longrightarrow> P) \<Longrightarrow> 
    (ternary_ternary_eval (map_match_tac \<beta> p m) = TernaryTrue \<Longrightarrow> P)
  \<Longrightarrow> P"
proof(induction m)
qed(auto split: option.split_asm simp: matches_case_tuple ternary_eval_def ternary_to_bool_bool_to_ternary elim: ternary_to_bool.elims)


text\<open>
Example: @{text "\<not> Unknown"} is as good as @{text Unknown}
\<close>
lemma "\<lbrakk> ternary_ternary_eval (map_match_tac \<beta> p expr) = TernaryUnknown \<rbrakk> \<Longrightarrow> matches (\<beta>, \<alpha>) expr a p \<longleftrightarrow> matches (\<beta>, \<alpha>) (MatchNot expr) a p"
by(simp add: matches_case_ternaryvalue_tuple)


lemma bunch_of_lemmata_about_matches:
  "matches \<gamma> (MatchAnd m1 m2) a p \<longleftrightarrow> matches \<gamma> m1 a p \<and> matches \<gamma> m2 a p" (*split AND*)
  "matches \<gamma> MatchAny a p" (*MatchAny is True*)
  "matches \<gamma> (MatchNot MatchAny) a p \<longleftrightarrow> False" (*Not True*)
  "matches \<gamma> (MatchNot (MatchNot m)) a p \<longleftrightarrow> matches \<gamma> m a p" (*idempotence*)
proof(case_tac [!] \<gamma>)
qed (simp_all split: ternaryvalue.split add: matches_case_ternaryvalue_tuple)

lemma match_raw_bool:
  "matches (\<beta>, \<alpha>) (Match expr) a p = (case ternary_to_bool (\<beta> expr p) of Some r \<Rightarrow> r | None \<Rightarrow> (\<alpha> a p))" (*Match raw*)
by(simp_all split: ternaryvalue.split add: matches_case_ternaryvalue_tuple)
lemma match_raw_ternary:
  "matches (\<beta>, \<alpha>) (Match expr) a p = (case (\<beta> expr p) of TernaryTrue \<Rightarrow> True | TernaryFalse \<Rightarrow> False | TernaryUnknown \<Rightarrow> (\<alpha> a p))" (*Match raw explicit*)
by(simp_all split: ternaryvalue.split add: matches_case_ternaryvalue_tuple)

(*kind of the DeMorgan Rule for matches*)
lemma matches_DeMorgan: "matches \<gamma> (MatchNot (MatchAnd m1 m2)) a p \<longleftrightarrow> (matches \<gamma> (MatchNot m1) a p) \<or> (matches \<gamma> (MatchNot m2) a p)"
by (cases \<gamma>) (simp split: ternaryvalue.split add: matches_case_ternaryvalue_tuple eval_ternary_DeMorgan)


subsection\<open>Ternary Matcher Algebra\<close>

lemma matches_and_comm: "matches \<gamma> (MatchAnd m m') a p \<longleftrightarrow> matches \<gamma> (MatchAnd m' m) a p"
apply(cases \<gamma>, rename_tac \<beta> \<alpha>, clarify)
by(simp add: matches_case_ternaryvalue_tuple eval_ternary_And_comm)

lemma matches_not_idem: "matches \<gamma> (MatchNot (MatchNot m)) a p \<longleftrightarrow> matches \<gamma> m a p"
by (fact bunch_of_lemmata_about_matches)


lemma MatchOr: "matches \<gamma> (MatchOr m1 m2) a p \<longleftrightarrow> matches \<gamma> m1 a p \<or> matches \<gamma> m2 a p"
  by(simp add: MatchOr_def matches_DeMorgan matches_not_idem)

lemma MatchOr_MatchNot: "matches \<gamma> (MatchNot (MatchOr m1 m2)) a p \<longleftrightarrow> matches \<gamma> (MatchNot m1) a p \<and> matches \<gamma> (MatchNot m2) a p"
  by(simp add: MatchOr_def matches_DeMorgan bunch_of_lemmata_about_matches)


lemma "(TernaryNot (map_match_tac \<beta> p (m))) = (map_match_tac \<beta> p (MatchNot m))"
by (metis map_match_tac.simps(2))

context
begin
  private lemma matches_simp1: "matches \<gamma> m a p \<Longrightarrow> matches \<gamma> (MatchAnd m m') a p \<longleftrightarrow> matches \<gamma> m' a p"
    apply(cases \<gamma>, rename_tac \<beta> \<alpha>, clarify)
    apply(simp split: ternaryvalue.split_asm ternaryvalue.split add: matches_case_ternaryvalue_tuple)
    done
  
  private lemma matches_simp11: "matches \<gamma> m a p \<Longrightarrow> matches \<gamma> (MatchAnd m' m) a p \<longleftrightarrow> matches \<gamma> m' a p"
    by(simp_all add: matches_and_comm matches_simp1)
  
  private lemma matches_simp2: "matches \<gamma> (MatchAnd m m') a p \<Longrightarrow> \<not> matches \<gamma> m a p \<Longrightarrow> False"
    by (simp add: bunch_of_lemmata_about_matches)
  private lemma matches_simp22: "matches \<gamma> (MatchAnd m m') a p \<Longrightarrow> \<not> matches \<gamma> m' a p \<Longrightarrow> False"
    by (simp add: bunch_of_lemmata_about_matches)
  
  (*m simplifies to MatchUnknown*)
 private  lemma matches_simp3: "matches \<gamma> (MatchNot m) a p \<Longrightarrow> matches \<gamma> m a p \<Longrightarrow> (snd \<gamma>) a p"
    apply(cases \<gamma>, rename_tac \<beta> \<alpha>, clarify)
    apply(simp split: ternaryvalue.split_asm ternaryvalue.split add: matches_case_ternaryvalue_tuple)
    done
  private lemma "matches \<gamma> (MatchNot m) a p \<Longrightarrow> matches \<gamma> m a p \<Longrightarrow> (ternary_eval (map_match_tac (fst \<gamma>) p m)) = None"
    apply(cases \<gamma>, rename_tac \<beta> \<alpha>, clarify)
    apply(simp split: ternaryvalue.split_asm ternaryvalue.split add: matches_case_ternaryvalue_tuple ternary_eval_def)
    done
  
  lemmas matches_simps = matches_simp1 matches_simp11
  lemmas matches_dest = matches_simp2 matches_simp22
end


lemma matches_iff_apply_f_generic: "ternary_ternary_eval (map_match_tac \<beta> p (f (\<beta>,\<alpha>) a m)) = ternary_ternary_eval (map_match_tac \<beta> p m) \<Longrightarrow> matches (\<beta>,\<alpha>) (f (\<beta>,\<alpha>) a m) a p \<longleftrightarrow> matches (\<beta>,\<alpha>) m a p"
  by(simp split: ternaryvalue.split_asm ternaryvalue.split add: matches_case_ternaryvalue_tuple)

lemma matches_iff_apply_f: "ternary_ternary_eval (map_match_tac \<beta> p (f m)) = ternary_ternary_eval (map_match_tac \<beta> p m) \<Longrightarrow> matches (\<beta>,\<alpha>) (f m) a p \<longleftrightarrow> matches (\<beta>,\<alpha>) m a p"
  by(fact matches_iff_apply_f_generic)



lemma opt_MatchAny_match_expr_correct: "matches \<gamma> (opt_MatchAny_match_expr m) = matches \<gamma> m"
  proof(case_tac \<gamma>, rename_tac \<beta> \<alpha>, clarify)
  fix \<beta> \<alpha>
  assume "\<gamma> = (\<beta>, \<alpha>)"
  have "ternary_ternary_eval (map_match_tac \<beta> p (opt_MatchAny_match_expr_once m)) =
          ternary_ternary_eval (map_match_tac \<beta> p m)" for p m
    proof(induction m rule: opt_MatchAny_match_expr_once.induct)
    qed(simp_all add: eval_ternary_simps eval_ternary_idempotence_Not)
  thus "matches (\<beta>, \<alpha>) (opt_MatchAny_match_expr m) = matches (\<beta>, \<alpha>) m"
    apply(simp add: fun_eq_iff)
    apply(clarify, rename_tac a p)
    apply(rule_tac f="opt_MatchAny_match_expr" in matches_iff_apply_f)
    apply(simp)
    apply(simp add: opt_MatchAny_match_expr_def)
    apply(rule repeat_stabilize_induct)
     by(simp)+
  qed



text\<open>An @{typ "'p unknown_match_tac"} is wf if it behaves equal for @{const Reject} and @{const Drop}\<close>
definition wf_unknown_match_tac :: "'p unknown_match_tac \<Rightarrow> bool" where
  "wf_unknown_match_tac \<alpha> \<equiv> (\<alpha> Drop = \<alpha> Reject)"


lemma wf_unknown_match_tacD_False1: "wf_unknown_match_tac \<alpha> \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m Reject p \<Longrightarrow> matches (\<beta>, \<alpha>) m Drop p \<Longrightarrow> False"
unfolding wf_unknown_match_tac_def by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split_asm)

lemma wf_unknown_match_tacD_False2: "wf_unknown_match_tac \<alpha> \<Longrightarrow> matches (\<beta>, \<alpha>) m Reject p \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m Drop p \<Longrightarrow> False"
unfolding wf_unknown_match_tac_def by(simp add: matches_case_ternaryvalue_tuple split: ternaryvalue.split_asm)


subsection\<open>Removing Unknown Primitives\<close>

definition unknown_match_all :: "'a unknown_match_tac \<Rightarrow> action \<Rightarrow> bool" where
   "unknown_match_all \<alpha> a = (\<forall>p. \<alpha> a p)"
definition unknown_not_match_any :: "'a unknown_match_tac \<Rightarrow> action \<Rightarrow> bool" where
   "unknown_not_match_any \<alpha> a = (\<forall>p. \<not> \<alpha> a p)"

(*see upper_closure_matchexpr*)
fun remove_unknowns_generic :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "remove_unknowns_generic _ _ MatchAny = MatchAny" |
  "remove_unknowns_generic _ _ (MatchNot MatchAny) = MatchNot MatchAny" |
  "remove_unknowns_generic (\<beta>, \<alpha>) a (Match A) = (if
      (\<forall>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)
    then
      if unknown_match_all \<alpha> a then MatchAny else if unknown_not_match_any \<alpha> a then MatchNot MatchAny else Match A
    else (Match A))" |
  "remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (Match A)) = (if
      (\<forall>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)
    then
      if unknown_match_all \<alpha> a then MatchAny else if unknown_not_match_any \<alpha> a then MatchNot MatchAny else MatchNot (Match A)
    else MatchNot (Match A))" |
  "remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (MatchNot m)) = remove_unknowns_generic (\<beta>, \<alpha>) a m" |
  "remove_unknowns_generic (\<beta>, \<alpha>) a (MatchAnd m1 m2) = MatchAnd
      (remove_unknowns_generic (\<beta>, \<alpha>) a m1)
      (remove_unknowns_generic (\<beta>, \<alpha>) a m2)" |

  --\<open>@{text "\<not> (a \<and> b) = \<not> b \<or> \<not> a"}   and   @{text "\<not> Unknown = Unknown"}\<close>
  "remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (MatchAnd m1 m2)) = 
    (if (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m1)) = MatchAny \<or>
        (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m2)) = MatchAny
        then MatchAny else 
        (if (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m1)) = MatchNot MatchAny then 
          remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m2) else
         if (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m2)) = MatchNot MatchAny then 
          remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m1) else
         MatchNot (MatchAnd (MatchNot (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m1))) (MatchNot (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot m2)))))
       )"

lemma[code_unfold]: "remove_unknowns_generic \<gamma> a (MatchNot (MatchAnd m1 m2)) = 
    (let m1' = remove_unknowns_generic \<gamma>  a (MatchNot m1); m2' = remove_unknowns_generic \<gamma>  a (MatchNot m2) in
    (if m1' = MatchAny \<or> m2' = MatchAny
     then MatchAny
     else 
        if m1' = MatchNot MatchAny then m2' else
        if m2' = MatchNot MatchAny then m1'
     else
        MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
       )"
by(cases \<gamma>)(simp)


lemma remove_unknowns_generic_simp_3_4_unfolded: "remove_unknowns_generic (\<beta>, \<alpha>) a (Match A) = (if
      (\<forall>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)
    then
      if (\<forall>p. \<alpha> a p) then MatchAny else if (\<forall>p. \<not> \<alpha> a p) then MatchNot MatchAny else Match A
    else (Match A))" 
 "remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (Match A)) = (if
      (\<forall>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)
    then
      if (\<forall>p. \<alpha> a p) then MatchAny else if (\<forall>p. \<not> \<alpha> a p) then MatchNot MatchAny else MatchNot (Match A)
    else MatchNot (Match A))"
  by(auto simp add: unknown_match_all_def unknown_not_match_any_def)

declare remove_unknowns_generic.simps[simp del]

lemmas remove_unknowns_generic_simps2 = remove_unknowns_generic.simps(1) remove_unknowns_generic.simps(2) 
            remove_unknowns_generic_simp_3_4_unfolded
            remove_unknowns_generic.simps(5) remove_unknowns_generic.simps(6) remove_unknowns_generic.simps(7)


lemma "matches (\<beta>, \<alpha>) (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (Match A))) a p = matches (\<beta>, \<alpha>) (MatchNot (Match A)) a p"
by(simp add: remove_unknowns_generic_simps2 matches_case_ternaryvalue_tuple)



lemma remove_unknowns_generic: "matches \<gamma> (remove_unknowns_generic \<gamma> a m) a = matches \<gamma> m a"
proof -
  have "matches \<gamma> (remove_unknowns_generic \<gamma> a m) a p = matches \<gamma> m a p"
  for p
  proof(induction \<gamma> a m rule: remove_unknowns_generic.induct)
  case 3 thus ?case
      by(simp add: bunch_of_lemmata_about_matches match_raw_ternary remove_unknowns_generic_simps2)
  next
  case 4 thus ?case
     by(simp add: matches_case_ternaryvalue_tuple remove_unknowns_generic_simps2)
  next
  case 7 thus ?case
    apply(simp add: bunch_of_lemmata_about_matches matches_DeMorgan remove_unknowns_generic_simps2)
    apply(simp add: matches_case_ternaryvalue_tuple)
    by fastforce
  qed(simp_all add: bunch_of_lemmata_about_matches remove_unknowns_generic_simps2)
  thus ?thesis by(simp add: fun_eq_iff)
qed





fun has_unknowns :: " ('a, 'p) exact_match_tac \<Rightarrow> 'a match_expr \<Rightarrow> bool" where
  "has_unknowns \<beta> (Match A) = (\<exists>p. ternary_ternary_eval (map_match_tac \<beta> p (Match A)) = TernaryUnknown)" |
  "has_unknowns \<beta> (MatchNot m) = has_unknowns \<beta> m" |
  "has_unknowns \<beta> MatchAny = False" |
  "has_unknowns \<beta> (MatchAnd m1 m2) = (has_unknowns \<beta> m1 \<or> has_unknowns \<beta> m2)"

(* assumes simple_ruleset, thus we only care about Accept/Drop *)
definition packet_independent_\<alpha> :: "'p unknown_match_tac \<Rightarrow> bool" where
  "packet_independent_\<alpha> \<alpha> = (\<forall>a p1 p2. a = Accept \<or> a = Drop \<longrightarrow> \<alpha> a p1 \<longleftrightarrow> \<alpha> a p2)"

lemma packet_independent_unknown_match: "a = Accept \<or> a = Drop \<Longrightarrow> packet_independent_\<alpha> \<alpha> \<Longrightarrow> \<not> unknown_not_match_any \<alpha> a \<longleftrightarrow> unknown_match_all \<alpha> a"
  by(auto simp add: packet_independent_\<alpha>_def unknown_match_all_def unknown_not_match_any_def)

text\<open>If for some type the exact matcher returns unknown, then it returns unknown for all these types\<close>
definition packet_independent_\<beta>_unknown :: "('a, 'packet) exact_match_tac \<Rightarrow> bool" where
  "packet_independent_\<beta>_unknown \<beta> \<equiv> \<forall>A. (\<exists>p. \<beta> A p \<noteq> TernaryUnknown) \<longrightarrow> (\<forall>p. \<beta> A p \<noteq> TernaryUnknown)"


lemma remove_unknowns_generic_specification: "a = Accept \<or> a = Drop \<Longrightarrow> packet_independent_\<alpha> \<alpha> \<Longrightarrow>
  packet_independent_\<beta>_unknown \<beta> \<Longrightarrow>
   \<not> has_unknowns \<beta> (remove_unknowns_generic (\<beta>, \<alpha>) a m)"
  proof(induction "(\<beta>, \<alpha>)" a m rule: remove_unknowns_generic.induct)
  case 3 thus ?case by(simp add: packet_independent_unknown_match packet_independent_\<beta>_unknown_def remove_unknowns_generic.simps)
  next
  case 4 thus ?case by(simp add: packet_independent_unknown_match packet_independent_\<beta>_unknown_def remove_unknowns_generic.simps)
  qed(simp_all add: remove_unknowns_generic.simps)





text\<open>Checking is something matches unconditionally\<close>
context
begin
  private lemma no_primitives_no_unknown: "\<not> has_primitive m  \<Longrightarrow> (ternary_ternary_eval (map_match_tac \<beta> p m)) \<noteq> TernaryUnknown"
  proof(induction m)
  case Match thus ?case by auto
  next
  case MatchAny thus ?case by simp
  next
  case MatchAnd thus ?case by(auto elim: eval_ternary_And.elims)
  next
  case MatchNot thus ?case by(auto dest: eval_ternary_Not_UnknownD)
  qed


  private lemma no_primitives_matchNot: assumes "\<not> has_primitive m" shows "matches \<gamma> (MatchNot m) a p \<longleftrightarrow> \<not> matches \<gamma> m a p"
  proof -
    obtain \<beta> \<alpha> where "(\<beta>, \<alpha>) = \<gamma>" by (cases \<gamma>, simp)
    thm no_primitives_no_unknown
    from assms have "matches (\<beta>, \<alpha>) (MatchNot m) a p \<longleftrightarrow> \<not> matches (\<beta>, \<alpha>) m a p"
      apply(induction m)
         apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split )
      apply(rename_tac m1 m2)
      by(simp split: ternaryvalue.split_asm)
    with \<open>(\<beta>, \<alpha>) = \<gamma>\<close> assms show ?thesis by simp
  qed
  

  lemma matcheq_matchAny: "\<not> has_primitive m \<Longrightarrow> matcheq_matchAny m \<longleftrightarrow> matches \<gamma> m a p"
  proof(induction m)
  case Match hence False by auto
    thus ?case ..
  next
  case (MatchNot m)
    from MatchNot.prems have "\<not> has_primitive m" by simp
    with no_primitives_matchNot have "matches \<gamma> (MatchNot m) a p = (\<not> matches \<gamma> m a p)" by metis
    with MatchNot show ?case by(simp)
  next
  case (MatchAnd m1 m2)
    thus ?case by(simp add: bunch_of_lemmata_about_matches)
  next
  case MatchAny show ?case by(simp add: Matching_Ternary.bunch_of_lemmata_about_matches)
  qed

  lemma matcheq_matchNone: "\<not> has_primitive m \<Longrightarrow> matcheq_matchNone m \<longleftrightarrow> \<not> matches \<gamma> m a p"
    by(auto dest: matcheq_matchAny matachAny_matchNone)

  lemma matcheq_matchNone_not_matches: "matcheq_matchNone m \<Longrightarrow> \<not> matches \<gamma> m a p"
    proof(induction m rule: matcheq_matchNone.induct)
    qed(auto simp add: bunch_of_lemmata_about_matches matches_DeMorgan)
    
end



text\<open>Lemmas about @{const MatchNot} in ternary logic.\<close>

lemma matches_MatchNot_no_unknowns:
   assumes "\<not> has_unknowns \<beta> m"
   shows "matches (\<beta>,\<alpha>) (MatchNot m) a p \<longleftrightarrow> \<not> matches (\<beta>,\<alpha>) m a p"
proof -
  { fix m have "\<not> has_unknowns \<beta> m \<Longrightarrow>
       ternary_to_bool (ternary_ternary_eval (map_match_tac \<beta> p m)) \<noteq> None"
    apply(induction m)
       apply(simp_all)
      using ternary_to_bool.elims apply blast
     using ternary_to_bool_Some apply fastforce
    using ternary_lift(6) ternary_to_bool_Some by auto
  } note no_unknowns_ternary_to_bool_Some=this
    from assms show ?thesis
      by(auto split: option.split_asm
              simp: matches_case_tuple no_unknowns_ternary_to_bool_Some ternary_to_bool_Some  ternary_eval_def ternary_to_bool_bool_to_ternary
              elim: ternary_to_bool.elims)
qed

lemma MatchNot_ternary_ternary_eval: "(ternary_ternary_eval (map_match_tac \<beta> p m')) = (ternary_ternary_eval (map_match_tac \<beta> p m)) \<Longrightarrow>
    matches (\<beta>,\<alpha>) (MatchNot m') a p = matches (\<beta>,\<alpha>) (MatchNot m) a p"
by(simp add: matches_tuple)



text\<open>For our @{typ "'p unknown_match_tac"}s @{text in_doubt_allow} and @{text in_doubt_deny},
      when doing an induction over some function that modifies @{term "m::'a match_expr"},
      we get the @{const MatchNot} case for free (if we can set arbitrary @{term "p::'p"}).
      This does not hold for arbitrary @{typ "'p unknown_match_tac"}s.\<close>
lemma matches_induction_case_MatchNot:
      assumes "\<alpha> Drop \<noteq> \<alpha> Accept" and "packet_independent_\<alpha> \<alpha>"
      and     "\<forall> a. matches (\<beta>,\<alpha>) m' a p = matches (\<beta>,\<alpha>) m a p"
      shows   "matches (\<beta>,\<alpha>) (MatchNot m') a p = matches (\<beta>,\<alpha>) (MatchNot m) a p"
proof -
  from assms(1) assms(2) have xxxx_xxX: "\<And>b. \<forall>a. \<alpha> a p = (\<not> b) \<Longrightarrow> False"
    apply(simp add: packet_independent_\<alpha>_def)
    apply(case_tac "\<alpha> Accept p")
     apply(simp_all)
     apply(case_tac [!] "\<alpha> Drop p")
       apply(simp_all add: fun_eq_iff)
     apply blast+
    done

  have xx2: "\<And>t. ternary_eval (TernaryNot t) = None \<Longrightarrow> ternary_eval t = None"
  by (simp add: eval_ternary_Not_UnknownD ternary_eval_def ternary_to_bool_None)
  
  have xx3: "\<And>t b. ternary_eval (TernaryNot t) = Some b \<Longrightarrow>  ternary_eval t = Some (\<not> b)"
  by (metis eval_ternary_Not.simps(1) eval_ternary_Not.simps(2) ternary_eval_def ternary_ternary_eval.simps(3) ternary_ternary_eval_idempotence_Not ternary_to_bool_Some)

  from assms show ?thesis
    apply(simp add: matches_case_tuple)
    apply(case_tac "ternary_eval (TernaryNot (map_match_tac \<beta> p m'))")
     apply(case_tac [!] "ternary_eval (TernaryNot (map_match_tac \<beta> p m))")
       apply(simp_all)
      apply(drule xx2)
      apply(drule xx3)
      apply(simp)
      using xxxx_xxX apply metis
     apply(drule xx2)
     apply(drule xx3)
     apply(simp)
     using xxxx_xxX apply metis
    apply(drule xx3)+
    apply(simp)
    done
qed



end
