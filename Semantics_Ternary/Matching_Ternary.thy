theory Matching_Ternary
imports "../Common/Ternary" "../Firewall_Common"
begin


section{*Packet Matching in Ternary Logic*}

text{* The matcher for a primitive match expression @{typ "'a"}*}
type_synonym ('a, 'packet) exact_match_tac="'a \<Rightarrow> 'packet \<Rightarrow> ternaryvalue"

text{*
If the matching is @{const TernaryUnknown}, it can be decided by the action whether this rule matches.
E.g. in doubt, we allow packets
*}
type_synonym 'packet unknown_match_tac="action \<Rightarrow> 'packet \<Rightarrow> bool"

type_synonym ('a, 'packet) match_tac="(('a, 'packet) exact_match_tac \<times> 'packet unknown_match_tac)"

text{*
For a given packet, map a firewall @{typ "'a match_expr"} to a @{typ ternaryformula}
Evaluating the formula gives whether the packet/rule matches (or unknown).
*}
fun map_match_tac :: "('a, 'packet) exact_match_tac \<Rightarrow> 'packet \<Rightarrow> 'a match_expr \<Rightarrow> ternaryformula" where
  "map_match_tac \<beta> p (MatchAnd m1 m2) = TernaryAnd (map_match_tac \<beta> p m1) (map_match_tac \<beta> p m2)" |
  "map_match_tac \<beta> p (MatchNot m) = TernaryNot (map_match_tac \<beta> p m)" |
  "map_match_tac \<beta> p (Match m) = TernaryValue (\<beta> m p)" |
  "map_match_tac _ _ MatchAny = TernaryValue TernaryTrue"


context
begin
  text{*the @{term ternaryformula}s we construct never have Or expressions.*}
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

text{*
Matching a packet and a rule:
\begin{enumerate}
  \item Translate @{typ "'a match_expr"} to ternary formula
  \item Evaluate this formula
  \item If @{const TernaryTrue}/@{const TernaryFalse}, return this value
  \item If @{const TernaryUnknown}, apply the @{typ "'a unknown_match_tac"} to get a Boolean result
\end{enumerate}
*}
definition matches :: "('a, 'packet) match_tac \<Rightarrow> 'a match_expr \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> bool" where
  "matches \<gamma> m a p \<equiv> ternary_to_bool_unknown_match_tac (snd \<gamma>) a p (ternary_ternary_eval (map_match_tac (fst \<gamma>) p m))"

(*TODO:
 should \<alpha> really be that free or should it be a fixed mapping:
 Unknown, return, call should throw an exception

 Reject Drop \<rightarrow> something
 Allow \<rightarrow> something
*)


text{*Alternative matches definitions, some more or less convenient*}

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


text{*
Example: @{text "\<not> Unknown"} is as good as @{text Unknown}
*}
lemma "\<lbrakk> ternary_ternary_eval (map_match_tac \<beta> p expr) = TernaryUnknown \<rbrakk> \<Longrightarrow> matches (\<beta>, \<alpha>) expr a p \<longleftrightarrow> matches (\<beta>, \<alpha>) (MatchNot expr) a p"
by(simp add: matches_case_ternaryvalue_tuple)


lemma bunch_of_lemmata_about_matches:
  "matches \<gamma> (MatchAnd m1 m2) a p \<longleftrightarrow> matches \<gamma> m1 a p \<and> matches \<gamma> m2 a p" (*split AND*)
  "matches \<gamma> MatchAny a p" (*MatchAny is True*)
  "matches \<gamma> (MatchNot MatchAny) a p \<longleftrightarrow> False" (*Not True*) 
  "matches (\<beta>, \<alpha>) (Match expr) a p = (case ternary_to_bool (\<beta> expr p) of Some r \<Rightarrow> r | None \<Rightarrow> (\<alpha> a p))" (*Match raw*)
  "matches (\<beta>, \<alpha>) (Match expr) a p = (case (\<beta> expr p) of TernaryTrue \<Rightarrow> True | TernaryFalse \<Rightarrow> False | TernaryUnknown \<Rightarrow> (\<alpha> a p))" (*Match raw explicit*)
  "matches \<gamma> (MatchNot (MatchNot m)) a p \<longleftrightarrow> matches \<gamma> m a p" (*idempotence*)
proof(case_tac [!] \<gamma>)
qed (simp_all split: ternaryvalue.split add: matches_case_ternaryvalue_tuple)


(*kind of the DeMorgan Rule for matches*)
lemma matches_DeMorgan: "matches \<gamma> (MatchNot (MatchAnd m1 m2)) a p \<longleftrightarrow> (matches \<gamma> (MatchNot m1) a p) \<or> (matches \<gamma> (MatchNot m2) a p)"
by (cases \<gamma>) (simp split: ternaryvalue.split add: matches_case_ternaryvalue_tuple eval_ternary_DeMorgan)


subsection{*Ternary Matcher Algebra*}

lemma matches_and_comm: "matches \<gamma> (MatchAnd m m') a p \<longleftrightarrow> matches \<gamma> (MatchAnd m' m) a p"
apply(cases \<gamma>, rename_tac \<beta> \<alpha>, clarify)
by(simp split: ternaryvalue.split add: matches_case_ternaryvalue_tuple eval_ternary_And_comm)

lemma matches_not_idem: "matches \<gamma> (MatchNot (MatchNot m)) a p \<longleftrightarrow> matches \<gamma> m a p"
by (metis bunch_of_lemmata_about_matches(6))


lemma MatchOr: "matches \<gamma> (MatchOr m1 m2) a p \<longleftrightarrow> matches \<gamma> m1 a p \<or> matches \<gamma> m2 a p"
  by(simp add: MatchOr_def matches_DeMorgan matches_not_idem)
  


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
    by (metis bunch_of_lemmata_about_matches(1))
  private lemma matches_simp22: "matches \<gamma> (MatchAnd m m') a p \<Longrightarrow> \<not> matches \<gamma> m' a p \<Longrightarrow> False"
    by (metis bunch_of_lemmata_about_matches(1))
  
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
  by(simp split: ternaryvalue.split_asm ternaryvalue.split add: matches_case_ternaryvalue_tuple)




text{*Optimize away MatchAny matches*}
fun opt_MatchAny_match_expr :: "'a match_expr \<Rightarrow> 'a match_expr" where
  "opt_MatchAny_match_expr MatchAny = MatchAny" |
  "opt_MatchAny_match_expr (Match a) = (Match a)" |
  "opt_MatchAny_match_expr (MatchNot (MatchNot m)) = (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchNot m) = MatchNot (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchAnd MatchAny MatchAny) = MatchAny" |
  "opt_MatchAny_match_expr (MatchAnd MatchAny m) = (opt_MatchAny_match_expr m)" | (*TODO: remove recursive call to opt_MatchAny_match_expr to make it faster*)
  "opt_MatchAny_match_expr (MatchAnd m MatchAny) = (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchAnd _ (MatchNot MatchAny)) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) _) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr (MatchAnd m1 m2) = MatchAnd (opt_MatchAny_match_expr m1) (opt_MatchAny_match_expr m2)"
(* without recursive call: need to apply multiple times until it stabelizes *)

lemma opt_MatchAny_match_expr_correct: "matches \<gamma> (opt_MatchAny_match_expr m) = matches \<gamma> m"
  apply(case_tac \<gamma>, rename_tac \<beta> \<alpha>, clarify)
  apply(simp add: fun_eq_iff, clarify, rename_tac a p)
  apply(rule_tac f="opt_MatchAny_match_expr" in matches_iff_apply_f)
  apply(simp)
  apply(induction m rule: opt_MatchAny_match_expr.induct)
                              apply(simp_all add: eval_ternary_simps eval_ternary_idempotence_Not)
  done

text{*It is still a good idea to apply @{const opt_MatchAny_match_expr} multiple times. Example:*}
lemma "MatchNot (opt_MatchAny_match_expr (MatchAnd MatchAny (MatchNot MatchAny))) = MatchNot (MatchNot MatchAny)" by simp
lemma "m = (MatchAnd (MatchAnd MatchAny MatchAny) (MatchAnd MatchAny MatchAny)) \<Longrightarrow> 
  (opt_MatchAny_match_expr^^2) m \<noteq> opt_MatchAny_match_expr m" by(simp add: funpow_def)


text{*An @{typ "'p unknown_match_tac"} is wf if it behaves equal for @{const Reject} and @{const Drop} *}
definition wf_unknown_match_tac :: "'p unknown_match_tac \<Rightarrow> bool" where
  "wf_unknown_match_tac \<alpha> \<equiv> (\<alpha> Drop = \<alpha> Reject)"


lemma wf_unknown_match_tacD_False1: "wf_unknown_match_tac \<alpha> \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m Reject p \<Longrightarrow> matches (\<beta>, \<alpha>) m Drop p \<Longrightarrow> False"
apply(simp add: wf_unknown_match_tac_def)
apply(simp add: matches_def)
apply(case_tac "(ternary_ternary_eval (map_match_tac \<beta> p m))")
  apply(simp)
 apply(simp)
apply(simp)
done

lemma wf_unknown_match_tacD_False2: "wf_unknown_match_tac \<alpha> \<Longrightarrow> matches (\<beta>, \<alpha>) m Reject p \<Longrightarrow> \<not> matches (\<beta>, \<alpha>) m Drop p \<Longrightarrow> False"
apply(simp add: wf_unknown_match_tac_def)
apply(simp add: matches_def)
apply(case_tac "(ternary_ternary_eval (map_match_tac \<beta> p m))")
  apply(simp)
 apply(simp)
apply(simp)
done

thm eval_ternary_simps_simple


subsection{*Removing Unknown Primitives*}

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

  --{*@{text "\<not> (a \<and> b) = \<not> b \<or> \<not> a"}   and   @{text "\<not> Unknown = Unknown"}*}
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

lemmas remove_unknowns_generic_simps2 = remove_unknowns_generic.simps(1) remove_unknowns_generic.simps(2) 
            remove_unknowns_generic_simp_3_4_unfolded
            remove_unknowns_generic.simps(5) remove_unknowns_generic.simps(6) remove_unknowns_generic.simps(7)


lemma "a = Accept \<or> a = Drop \<Longrightarrow> matches (\<beta>, \<alpha>) (remove_unknowns_generic (\<beta>, \<alpha>) a (MatchNot (Match A))) a p = matches (\<beta>, \<alpha>) (MatchNot (Match A)) a p"
apply(simp del: remove_unknowns_generic.simps add: remove_unknowns_generic_simps2)
apply(simp add: bunch_of_lemmata_about_matches matches_case_ternaryvalue_tuple)
by presburger



lemma remove_unknowns_generic: "a = Accept \<or> a = Drop \<Longrightarrow>
      matches \<gamma> (remove_unknowns_generic \<gamma> a m) a = matches \<gamma> m a"
  apply(simp add: fun_eq_iff, clarify)
  apply(rename_tac p)
  apply(induction \<gamma> a m rule: remove_unknowns_generic.induct)
        apply(simp_all add: bunch_of_lemmata_about_matches)[2]
      apply(simp_all add: bunch_of_lemmata_about_matches del: remove_unknowns_generic.simps add: remove_unknowns_generic_simps2)[1]
     apply(simp add: matches_case_ternaryvalue_tuple  del: remove_unknowns_generic.simps  add: remove_unknowns_generic_simps2)
    apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
  apply(simp_all add: matches_case_ternaryvalue_tuple)
  apply safe
               apply(simp_all add : ternary_to_bool_Some ternary_to_bool_None)
done





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

text{*If for some type the exact matcher returns unknown, then it returns unknown for all these types*}
definition packet_independent_\<beta>_unknown :: "('a, 'packet) exact_match_tac \<Rightarrow> bool" where
  "packet_independent_\<beta>_unknown \<beta> \<equiv> \<forall>A. (\<exists>p. \<beta> A p \<noteq> TernaryUnknown) \<longrightarrow> (\<forall>p. \<beta> A p \<noteq> TernaryUnknown)"


lemma remove_unknowns_generic_specification: "a = Accept \<or> a = Drop \<Longrightarrow> packet_independent_\<alpha> \<alpha> \<Longrightarrow> packet_independent_\<beta>_unknown \<beta> \<Longrightarrow>
   \<not> has_unknowns \<beta> (remove_unknowns_generic (\<beta>, \<alpha>) a m)"
  proof(induction "(\<beta>, \<alpha>)" a m rule: remove_unknowns_generic.induct)
  case 3 thus ?case by(simp add: packet_independent_unknown_match packet_independent_\<beta>_unknown_def)
  next
  case 4 thus ?case by(simp add: packet_independent_unknown_match packet_independent_\<beta>_unknown_def)
  qed(simp_all)



end
