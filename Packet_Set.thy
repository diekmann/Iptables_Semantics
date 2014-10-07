theory Packet_Set
imports Fixed_Action "Output_Format/Negation_Type_Matching" Datatype_Selectors
begin

section{*Packet Set*}
(*probably wants a simple ruleset*)

text{*@{const alist_and} transforms @{typ "'a negation_type list \<Rightarrow> 'a match_expr"} and uses conjunction as connective. *}


text{*inner is and, outer is or*}
definition to_negation_type :: "'a match_expr \<Rightarrow> ('a negation_type list) list" where
 "to_negation_type m = map to_negation_type_nnf (normalize_match m)"

term normalize_match
term normalized_match
thm normalized_match_normalize_match



definition to_packet_set :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> ('a negation_type list) list \<Rightarrow> 'packet set" where
  "to_packet_set \<gamma> a ms \<equiv> {p. \<exists> m \<in> set ms. matches \<gamma> (alist_and m) a p}"


fun collect_allow :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
  "collect_allow _ [] P = {}" |
  "collect_allow \<gamma> ((Rule m Accept)#rs) P = {p \<in> P. matches \<gamma> m Accept p} \<union> (collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p})" |
  "collect_allow \<gamma> ((Rule m Drop)#rs) P = (collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p})"

lemma collect_allow_subset: "simple_ruleset rs \<Longrightarrow> collect_allow \<gamma> rs P \<subseteq> P"
apply(induction rs arbitrary: P)
 apply(simp)
apply(rename_tac r rs P)
apply(case_tac r, rename_tac m a)
apply(case_tac a)
apply(simp_all add: simple_ruleset_def)
apply(fast)
apply blast
done


lemma "simple_ruleset rs \<Longrightarrow> p \<in> collect_allow \<gamma> rs P \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow"
proof(induction rs arbitrary: P)
case Nil thus ?case by simp
next
case (Cons r rs)
  from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
  from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
  from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
  show ?case (is ?goal)
  proof(cases a)
    case Accept
      from Accept Cons.IH[where P="{p \<in> P. \<not> matches \<gamma> m Accept p}"] simple_rs have IH:
        "p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p} \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" by simp
      from Accept Cons.prems have "(p \<in> P \<and> matches \<gamma> m Accept p) \<or> p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p}"
        by(simp add: r)
      with Accept show ?goal
      apply -
      apply(erule disjE)
       apply(simp add: r)
      apply(simp add: r)
      using IH by blast
    next
    case Drop 
      from Drop Cons.prems have "p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p}"
        by(simp add: r)
      with Cons.IH simple_rs have "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" by simp
      with Cons show ?goal
       apply(simp add: r Drop del: approximating_bigstep_fun.simps)
       apply(simp)
       using collect_allow_subset[OF simple_rs] by fast
    qed(insert a_cases, simp_all)
qed


lemma "simple_ruleset rs \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<Longrightarrow> p \<in> P \<Longrightarrow> p \<in> collect_allow \<gamma> rs P"
apply(induction rs arbitrary: P)
 apply(simp)
apply(rename_tac r rs P)
apply(case_tac r, rename_tac m a)
apply(case_tac a)
apply(simp_all add: simple_ruleset_def del: approximating_bigstep_fun.simps)
apply(case_tac "matches \<gamma> m Accept p")
 apply(simp)
apply(simp)
apply(case_tac "matches \<gamma> m Drop p")
 apply(simp)
apply(simp)
done

(*
lemma "simple_ruleset rs \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<Longrightarrow> p \<in> collect_allow \<gamma> rs UNIV"
proof(induction rs)
case Nil thus ?case by simp
next
case (Cons r rs)
  from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
  from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
  from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
  show ?case (is ?goal)
  proof(cases a)
    case Accept
      from Accept Cons.IH simple_rs have IH:
        "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<Longrightarrow> p \<in> collect_allow \<gamma> rs UNIV" by simp
      from Accept Cons.prems have "matches \<gamma> m Accept p \<or> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow"
        apply(simp add: r) by presburger
      with Accept show ?goal
      apply -
      apply(erule disjE)
      apply(simp add: r)
       apply(simp add: r)
      apply(drule IH)
      
      sorry
    next
    case Drop
      with Cons show ?goal sorry
    qed(insert a_cases, simp_all)
qed
*)


end
