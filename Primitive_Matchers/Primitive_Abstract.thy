theory Primitive_Abstract
imports "../Examples/Code_Interface"
begin

(*UNFINISHED DRAFT*)

  fun abstract_negated_interfaces_protocols :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "abstract_negated_interfaces_protocols MatchAny = MatchAny" |
    "abstract_negated_interfaces_protocols (Match a) = Match a" |
    "abstract_negated_interfaces_protocols (MatchNot (Match (IIface (Iface ifce)))) = Match (Extra (''! -i ''@ifce))" |
    "abstract_negated_interfaces_protocols (MatchNot (Match (OIface (Iface ifce)))) = Match (Extra (''! -o ''@ifce))" |
    "abstract_negated_interfaces_protocols (MatchNot (Match (Prot ProtoAny))) = MatchNot MatchAny" |
    "abstract_negated_interfaces_protocols (MatchNot (Match (Prot (Proto p)))) = Match (Extra (''! -p ''@protocol_toString (Proto p)))" |
    "abstract_negated_interfaces_protocols (MatchNot m) = MatchNot (abstract_negated_interfaces_protocols m)" |
    "abstract_negated_interfaces_protocols (MatchAnd m1 m2) = MatchAnd (abstract_negated_interfaces_protocols m1) (abstract_negated_interfaces_protocols m2)"

thm match_expr.split
lemma abstract_negated_interfaces_protocols_MatchNot_cases: "abstract_negated_interfaces_protocols (MatchNot m) =
      (case m of (Match (IIface (Iface ifce))) \<Rightarrow> Match (Extra (''! -i ''@ifce))
              |  (Match (OIface (Iface ifce))) \<Rightarrow> Match (Extra (''! -o ''@ifce))
              |  (Match (Prot (ProtoAny))) \<Rightarrow> MatchNot MatchAny
              |  (Match (Prot (Proto p))) \<Rightarrow> Match (Extra (''! -p ''@protocol_toString (Proto p)))
              |  m' \<Rightarrow> MatchNot (abstract_negated_interfaces_protocols m')
      )"
apply(cases m)
apply(simp_all split: common_primitive.split)
apply(safe)
  apply(rename_tac x1 x2, case_tac x2, simp)
 apply(rename_tac x1 x2, case_tac x2, simp)
apply(rename_tac x1 x2, case_tac x2, simp)
apply(rename_tac x3, case_tac x3)
  apply(simp_all)
done


context
begin
  private lemma ternary_lift1: "eval_ternary_Not tv \<noteq> TernaryFalse \<longleftrightarrow> tv = TernaryFalse \<or> tv = TernaryUnknown"
    using eval_ternary_Not.elims by blast
  private lemma ternary_lift2: "eval_ternary_And t1 t2 = TernaryFalse \<longleftrightarrow> t1 = TernaryFalse \<or> t2 = TernaryFalse"
    using eval_ternary_And.elims by blast

  lemmas ternary_lift = ternary_lift1 ternary_lift2
end

context
begin
  private lemma l1: "eval_ternary_Not tv = TernaryTrue \<Longrightarrow> tv = TernaryFalse"
    by (metis eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma l2: "eval_ternary_And t1 t2 = TernaryFalse \<Longrightarrow> t1 = TernaryFalse \<or> t2 = TernaryFalse"
    using eval_ternary_And.elims by blast
  
  lemmas eval_ternaryD = l1 l2
end

lemma
   "matches (common_matcher, in_doubt_allow) m action.Accept p \<Longrightarrow>
    matches (common_matcher, in_doubt_allow) (abstract_negated_interfaces_protocols m) action.Accept p"
   apply(induction m rule: abstract_negated_interfaces_protocols.induct)
   apply(simp_all)
   apply (simp_all add: bunch_of_lemmata_about_matches)
   apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split)
   
   defer
   apply(simp add: matches_case_ternaryvalue_tuple bool_to_ternary_simps  split: ternaryvalue.split ternaryvalue.split_asm)
   apply(simp add: ternary_lift)
oops



end