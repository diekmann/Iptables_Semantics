theory Semantics
imports Main Firewall_Common Misc "~~/src/HOL/Library/LaTeXsugar"
begin

section{*Big Step Semantics*}


text{*
The assumption we apply in general is that the firewall does not alter any packets.
*}

type_synonym 'a ruleset = "string \<rightharpoonup> 'a rule list"

type_synonym ('a, 'p) matcher = "'a \<Rightarrow> 'p \<Rightarrow> bool"

fun matches :: "('a, 'p) matcher \<Rightarrow> 'a match_expr \<Rightarrow> 'p \<Rightarrow> bool" where
"matches \<gamma> (MatchAnd e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<and> matches \<gamma> e2 p" |
"matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" | (*does not work for ternary logic. Here: ok*)
"matches \<gamma> (Match e) p \<longleftrightarrow> \<gamma> e p" |
"matches _ MatchAny _ \<longleftrightarrow> True"

fun no_Goto :: "'a rule list \<Rightarrow> bool" where
  "no_Goto [] = True" |
  "no_Goto ((Rule _ (Goto _))#rs) = False" |
  "no_Goto (_#rs) = no_Goto rs"

fun no_matching_Goto :: "('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> bool" where
  "no_matching_Goto _ _ [] \<longleftrightarrow> True" |
  "no_matching_Goto \<gamma> p ((Rule m (Goto _))#rs) \<longleftrightarrow> \<not> matches \<gamma> m p \<and> no_matching_Goto \<gamma> p rs" |
  "no_matching_Goto \<gamma> p (_#rs) \<longleftrightarrow> no_matching_Goto \<gamma> p rs"

inductive iptables_bigstep :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_,_,_\<turnstile> \<langle>_, _\<rangle> \<Rightarrow> _"  [60,60,60,20,98,98] 89)
  for \<Gamma> and \<gamma> and p where
skip:    "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[], t\<rangle> \<Rightarrow> t" |
accept:  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Accept], Undecided\<rangle> \<Rightarrow> Decision FinalAllow" |
drop:    "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Drop], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
reject:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Reject], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
log:     "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Log], Undecided\<rangle> \<Rightarrow> Undecided" |
(*empty does not do anything to the packet. It could update the internal firewall state, e.g. marking a packet for later-on rate limiting*)
empty:   "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Empty], Undecided\<rangle> \<Rightarrow> Undecided" |
nomatch: "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided" |
decision: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Decision X\<rangle> \<Rightarrow> Decision X" |
seq:      "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t'; no_matching_Goto \<gamma> p rs\<^sub>1\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t'" |
call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1@[Rule m' Return]@rs\<^sub>2);
                 matches \<gamma> m' p; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" |
call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t" |
goto_decision:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision X \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> Decision X" |
goto_no_decision:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> Undecided"

text{*
The semantic rules again in pretty format:
\begin{center}
@{thm[mode=Axiom] skip [no_vars]}\\[1ex]
@{thm[mode=Rule] accept [no_vars]}\\[1ex]
@{thm[mode=Rule] drop [no_vars]}\\[1ex]
@{thm[mode=Rule] reject [no_vars]}\\[1ex]
@{thm[mode=Rule] log [no_vars]}\\[1ex]
@{thm[mode=Rule] empty [no_vars]}\\[1ex]
@{thm[mode=Rule] nomatch [no_vars]}\\[1ex]
@{thm[mode=Rule] decision [no_vars]}\\[1ex]
@{thm[mode=Rule] seq [no_vars]} \\[1ex]
@{thm[mode=Rule] call_return [no_vars]}\\[1ex] 
@{thm[mode=Rule] call_result [no_vars]}\\[1ex] 
@{thm[mode=Rule] goto_decision [no_vars]}\\[1ex] 
@{thm[mode=Rule] goto_no_decision [no_vars]}
\end{center}
*}

lemma deny:
  "matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> iptables_bigstep \<Gamma> \<gamma> p [Rule m a] Undecided (Decision FinalDeny)"
by (auto intro: drop reject)


lemma iptables_bigstep_induct
  [case_names Skip Allow Deny Log Nomatch Decision Seq Call_return Call_result Goto_Decision Goto_no_Decision,
   induct pred: iptables_bigstep]:
  "\<lbrakk> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t;
     \<And>t. P [] t t;
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Accept \<Longrightarrow> P [Rule m a] Undecided (Decision FinalAllow);
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> P [Rule m a] Undecided (Decision FinalDeny);
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Log \<or> a = Empty \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>m a. \<not> matches \<gamma> m p \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>rs X. P rs (Decision X) (Decision X);
     \<And>rs rs\<^sub>1 rs\<^sub>2 t t'. rs = rs\<^sub>1 @ rs\<^sub>2 \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs\<^sub>1 Undecided t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t' \<Longrightarrow> P rs\<^sub>2 t t' \<Longrightarrow> no_matching_Goto \<gamma> p rs\<^sub>1 \<Longrightarrow> P rs Undecided t';
     \<And>m a chain rs\<^sub>1 m' rs\<^sub>2. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow> \<Gamma> chain = Some (rs\<^sub>1 @ [Rule m' Return] @ rs\<^sub>2) \<Longrightarrow> matches \<gamma> m' p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> P rs\<^sub>1 Undecided Undecided \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>m a chain rs t. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs Undecided t \<Longrightarrow> P [Rule m a] Undecided t;
     \<And>m a chain rs rest X. matches \<gamma> m p \<Longrightarrow> a = Goto chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,Undecided\<rangle> \<Rightarrow> (Decision X) \<Longrightarrow> P rs Undecided (Decision X) \<Longrightarrow> P (Rule m a#rest) Undecided (Decision X);
     \<And>m a chain rs rest. matches \<gamma> m p \<Longrightarrow> a = Goto chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> P rs Undecided Undecided \<Longrightarrow> P (Rule m a#rest) Undecided Undecided\<rbrakk> \<Longrightarrow>
   P rs s t"
apply (induction rule: iptables_bigstep.induct) by auto


lemma decisionD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> s = Decision X \<Longrightarrow> t = Decision X"
by (induction rule: iptables_bigstep_induct) auto

lemma iptables_bigstep_to_undecided: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> Undecided \<Longrightarrow> s = Undecided"
  by (metis decisionD state.exhaust)

lemma iptables_bigstep_to_decision: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Decision Y\<rangle> \<Rightarrow> Decision X \<Longrightarrow> Y = X"
  by (metis decisionD state.inject)


lemma skipD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [] \<Longrightarrow> s = t"
by (induction rule: iptables_bigstep.induct) auto


lemma gotoD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m (Goto chain)] \<Longrightarrow> s = Undecided \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>
                \<exists> rs. \<Gamma> chain = Some rs \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t"
by (induction rule: iptables_bigstep.induct) (auto dest: skipD elim: list_app_singletonE)

lemma not_no_matching_Goto_singleton_cases: "\<not> no_matching_Goto \<gamma> p [Rule m a] \<longleftrightarrow> (\<exists> chain. a = (Goto chain)) \<and> matches \<gamma> m p"
      by(case_tac a) (simp_all)

lemma no_matching_Goto_Cons: "no_matching_Goto \<gamma> p [r] \<Longrightarrow> no_matching_Goto \<gamma> p rs \<Longrightarrow> no_matching_Goto \<gamma> p (r#rs)"
  by(cases r)(rename_tac m a, case_tac a, simp_all)

(*
lemma not_no_matching_Goto_cases:
  assumes "\<not> no_matching_Goto \<gamma> p rs" "rs \<noteq> []"
  obtains rs1 m chain rs2 where "rs = rs1@(Rule m (Goto chain))#rs2" "no_matching_Goto \<gamma> p rs1" "matches \<gamma> m p"*)

lemma not_no_matching_Goto_cases:
  assumes "\<not> no_matching_Goto \<gamma> p rs" "rs \<noteq> []"
  shows "\<exists>rs1 m chain rs2. rs = rs1@(Rule m (Goto chain))#rs2 \<and> no_matching_Goto \<gamma> p rs1 \<and> matches \<gamma> m p"
    using assms
    proof(induction rs)
    case Nil thus ?case by simp
    next
    case (Cons r rs)
      note Cons_outer=this
      from Cons have "\<not> no_matching_Goto \<gamma> p (r # rs)" by simp
      show ?case
      proof(cases rs)
      case Nil
        obtain m a where "r = Rule m a" by (cases r) simp
        with `\<not> no_matching_Goto \<gamma> p (r # rs)` Nil not_no_matching_Goto_singleton_cases have "(\<exists> chain. a = (Goto chain)) \<and> matches \<gamma> m p" by metis
        from this obtain chain where "a = (Goto chain)" and "matches \<gamma> m p" by blast
        have "r # rs = [] @ Rule m (Goto chain) # []" "no_matching_Goto \<gamma> p []" "matches \<gamma> m p"
          by (simp_all add: `a = Goto chain` `r = Rule m a` Nil `matches \<gamma> m p`)
        thus ?thesis by blast
      next
      case(Cons r' rs')
        with Cons_outer have "r # rs =  r # r' # rs'" by simp
        show ?thesis
        proof(cases"no_matching_Goto \<gamma> p [r]")
        case True 
          with `\<not> no_matching_Goto \<gamma> p (r # rs)` have "\<not> no_matching_Goto \<gamma> p rs" by (meson no_matching_Goto_Cons)
          have "rs \<noteq> []" using Cons by simp
          from Cons_outer(1)[OF `\<not> no_matching_Goto \<gamma> p rs` `rs \<noteq> []`]
            obtain rs1 m chain rs2 where "rs = rs1 @ Rule m (Goto chain) # rs2" "no_matching_Goto \<gamma> p rs1" "matches \<gamma> m p" by blast
          with `r # rs =  r # r' # rs'` `no_matching_Goto \<gamma> p [r]` no_matching_Goto_Cons
              have "r # rs = r # rs1 @ Rule m (Goto chain) # rs2 \<and> no_matching_Goto \<gamma> p (r#rs1) \<and> matches \<gamma> m p" by fast
          thus ?thesis
            apply(rule_tac x="r#rs1" in exI)
            by auto
        next
        case False
          obtain m a where "r = Rule m a" by (cases r) simp
          with False not_no_matching_Goto_singleton_cases have "(\<exists> chain. a = (Goto chain)) \<and> matches \<gamma> m p" by metis
          from this obtain chain where "a = (Goto chain)" and "matches \<gamma> m p" by blast
          have "r # rs = [] @ Rule m (Goto chain) # rs" "no_matching_Goto \<gamma> p []" "matches \<gamma> m p"
            by (simp_all add: `a = Goto chain` `r = Rule m a` `matches \<gamma> m p`)
          thus ?thesis by blast
        qed
      qed
    qed

lemma seq_cons_Goto_Undecided: 
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow>
    (\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided) \<Longrightarrow>
      \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Goto chain) # rs, Undecided\<rangle> \<Rightarrow> Undecided"
  apply(cases "matches \<gamma> m p")
   apply(drule gotoD)
      apply(simp_all)
   using goto_no_decision apply fast
  apply(drule_tac t'=Undecided and rs\<^sub>2=rs in seq)
    apply(simp)
  apply(simp)
 apply(simp)
done

lemma seq_cons_Goto_t: 
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Goto chain) # rs, Undecided\<rangle> \<Rightarrow> t"
   apply(frule gotoD)
      apply(simp_all)
   apply(clarify)
   apply(cases t)
    apply(auto intro: Semantics.iptables_bigstep.intros)
done


lemma no_matching_Goto_append: "no_matching_Goto \<gamma> p (rs1@rs2) \<longleftrightarrow> no_matching_Goto \<gamma> p rs1 \<and>  no_matching_Goto \<gamma> p rs2"
  by(induction \<gamma> p rs1 rule: no_matching_Goto.induct) (simp_all)

lemma no_matching_Goto_append1: "no_matching_Goto \<gamma> p (rs1@rs2) \<Longrightarrow> no_matching_Goto \<gamma> p rs1"
  using no_matching_Goto_append by fast
lemma no_matching_Goto_append2: "no_matching_Goto \<gamma> p (rs1@rs2) \<Longrightarrow> no_matching_Goto \<gamma> p rs2"
  using no_matching_Goto_append by fast




lemma seq_cons:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],Undecided\<rangle> \<Rightarrow> t" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,t\<rangle> \<Rightarrow> t'" and "no_matching_Goto \<gamma> p [r]"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, Undecided\<rangle> \<Rightarrow> t'"
proof -
    from assms have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r] @ rs, Undecided\<rangle> \<Rightarrow> t'" by (rule seq)
    thus ?thesis by simp
qed



context
  notes skipD[dest] list_app_singletonE[elim]
begin

lemma acceptD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Accept] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalAllow"
by (induction rule: iptables_bigstep.induct) auto

lemma dropD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Drop] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalDeny"
by (induction rule: iptables_bigstep.induct) auto

lemma rejectD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Reject] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalDeny"
by (induction rule: iptables_bigstep.induct) auto

lemma logD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Log] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Undecided"
by (induction rule: iptables_bigstep.induct) auto

lemma emptyD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Empty] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Undecided"
by (induction rule: iptables_bigstep.induct) auto

lemma nomatchD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m a] \<Longrightarrow> s = Undecided \<Longrightarrow> \<not> matches \<gamma> m p \<Longrightarrow> t = Undecided"
by (induction rule: iptables_bigstep.induct) auto

lemma callD:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t" "r = [Rule m (Call chain)]" "s = Undecided" "matches \<gamma> m p" "\<Gamma> chain = Some rs"
  obtains "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t"
        | rs\<^sub>1 rs\<^sub>2 m' where "rs = rs\<^sub>1 @ Rule m' Return # rs\<^sub>2" "matches \<gamma> m' p" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> Undecided" "t = Undecided"
  using assms
  proof (induction r s t arbitrary: rs rule: iptables_bigstep.induct)
    case (seq rs\<^sub>1)
    thus ?case by (cases rs\<^sub>1) auto
  qed auto

end

lemmas iptables_bigstepD = skipD acceptD dropD rejectD logD emptyD nomatchD decisionD callD gotoD

lemma seq':
  assumes "rs = rs\<^sub>1 @ rs\<^sub>2" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t'" and "no_matching_Goto \<gamma> p rs\<^sub>1"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t'"
using assms by (cases s) (auto intro: seq decision dest: decisionD)


lemma seq'_cons: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,t\<rangle> \<Rightarrow> t' \<Longrightarrow> no_matching_Goto \<gamma> p [r] \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, s\<rangle> \<Rightarrow> t'"
by (metis decision decisionD state.exhaust seq_cons)


lemma no_matching_Goto_take: "no_matching_Goto \<gamma> p rs \<Longrightarrow> no_matching_Goto \<gamma> p  (take n rs)"
  apply(induction n arbitrary: rs)
   apply(simp_all)
  apply(case_tac rs)
   apply(simp_all)
  apply(rename_tac r' rs')
  apply(case_tac r')
  apply(simp)
  apply(rename_tac m a)
  by(case_tac a) (simp_all)



lemma seq_split:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" "rs = rs\<^sub>1@rs\<^sub>2"
  obtains (no_matching_Goto) t' where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t'" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t'\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p rs\<^sub>1"
        | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
proof -
  have "(\<exists>t'. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t' \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t'\<rangle> \<Rightarrow> t \<and> no_matching_Goto \<gamma> p rs\<^sub>1) \<or> (\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t \<and> \<not> no_matching_Goto \<gamma> p rs\<^sub>1)"
  using assms
  proof (induction rs s t arbitrary: rs\<^sub>1 rs\<^sub>2 rule: iptables_bigstep_induct)
    case Skip thus ?case by (auto intro: iptables_bigstep.intros simp add: accept)
  next
    case Allow thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros simp add: accept)
  next
    case Deny thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros simp add: deny)
  next
    case Log thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros simp add: log empty)
  next
    case Nomatch thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros simp add: not_no_matching_Goto_singleton_cases)
  next
    case Decision thus ?case by (auto intro: iptables_bigstep.intros)
  next
    case (Seq rs rsa rsb t t')
    hence rs: "rsa @ rsb = rs\<^sub>1 @ rs\<^sub>2" by simp
    note List.append_eq_append_conv_if[simp]
    from rs show ?case
      proof (cases rule: list_app_eq_cases)
        case longer
        with Seq have t1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t"
          by simp
        from Seq.IH(2)[OF longer(2)] have IH:
          "(\<exists>t'a. \<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa) rs\<^sub>1, t\<rangle> \<Rightarrow> t'a \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t'a\<rangle> \<Rightarrow> t' \<and> no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)) \<or>
           \<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa) rs\<^sub>1, t\<rangle> \<Rightarrow> t' \<and> \<not> no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)" (is "?IH_no_Goto \<or> ?IH_Goto") by simp
        thus ?thesis
          proof(rule disjE)
            assume IH: ?IH_no_Goto
            from IH obtain t2
              where t2a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa) rs\<^sub>1,t\<rangle> \<Rightarrow> t2"
                and rs_part2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t2\<rangle> \<Rightarrow> t'"
                and "no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)"
              by blast
            with t1 rs_part2 have rs_part1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t2"
              using Seq.hyps(4) longer(1) seq by fastforce
            have "no_matching_Goto \<gamma> p (take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1)"
              using Seq.hyps(4) `no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)` longer(1)
                    no_matching_Goto_append by fastforce 
            with Seq rs_part1 rs_part2 show ?thesis by auto
          next
            assume ?IH_Goto
            thus ?thesis by (metis Seq.hyps(2) Seq.hyps(4) append_take_drop_id longer(1) no_matching_Goto_append2 seq')
          qed
      next
        case shorter
        from shorter rs have rsa': "rsa = rs\<^sub>1 @ take (length rsa - length rs\<^sub>1) rs\<^sub>2"
          by (metis append_eq_conv_conj length_drop)
        from shorter rs have rsb': "rsb = drop (length rsa - length rs\<^sub>1) rs\<^sub>2"
          by (metis append_eq_conv_conj length_drop)

        from Seq.hyps(4) rsa' no_matching_Goto_append2 have
            no_matching_Goto_rs2: "no_matching_Goto \<gamma> p (take (length rsa - length rs\<^sub>1) rs\<^sub>2)" by metis

        from rsb' Seq.hyps have t2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa - length rs\<^sub>1) rs\<^sub>2,t\<rangle> \<Rightarrow> t'"
          by blast

        from Seq.IH(1)[OF rsa'] have IH:
          "(\<exists>t'. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t' \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa - length rs\<^sub>1) rs\<^sub>2, t'\<rangle> \<Rightarrow> t \<and> no_matching_Goto \<gamma> p rs\<^sub>1) \<or>
            \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t \<and> \<not> no_matching_Goto \<gamma> p rs\<^sub>1" (is "?IH_no_Goto \<or> ?IH_Goto") by simp

        thus ?thesis
          proof(rule disjE)
            assume IH: ?IH_no_Goto
            from IH obtain t1
              where t1a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t1"
                and t1b: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa - length rs\<^sub>1) rs\<^sub>2,t1\<rangle> \<Rightarrow> t"
                and "no_matching_Goto \<gamma> p rs\<^sub>1"
              by blast
    
              from no_matching_Goto_rs2 t2 seq' t1b have rs2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t1\<rangle> \<Rightarrow> t'"
                by  fastforce
              from t1a rs2 `no_matching_Goto \<gamma> p rs\<^sub>1` show ?thesis by fast
          next
            assume ?IH_Goto
            thus ?thesis by (metis Seq.hyps(4) no_matching_Goto_append1 rsa') 
          qed
      qed
  next
    case Call_return
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Undecided"
      by (case_tac [!] rs\<^sub>1) (auto intro: iptables_bigstep.skip iptables_bigstep.call_return)
    thus ?case by fast
  next
    case (Call_result _ _ _ _ t)
    show ?case
      proof (cases rs\<^sub>1)
        case Nil
        with Call_result have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis using local.Nil by auto 
      next
        case Cons
        with Call_result have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis by fast
      qed
  next
    case (Goto_Decision m a chain rs rest X)
    thus ?case
      proof (cases rs\<^sub>1)
        case Nil
        with Goto_Decision have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Decision X"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis using local.Nil by auto
      next
        case Cons
        with Goto_Decision have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Decision X" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Decision X\<rangle> \<Rightarrow> Decision X"
          by (auto intro: iptables_bigstep.intros) 
        thus ?thesis by fast
      qed
  next
    case (Goto_no_Decision m a chain rs rest rs\<^sub>1)
    from Goto_no_Decision have rs1rs2: "Rule m (Goto chain) # rest = rs\<^sub>1 @ rs\<^sub>2" by simp
    from goto_no_decision[OF Goto_no_Decision(1)]  Goto_no_Decision(3)  Goto_no_Decision(4)
      have x: "\<And>rest. \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Goto chain) # rest, Undecided\<rangle> \<Rightarrow> Undecided" by simp
    show ?case
      proof (cases rs\<^sub>1)
        case Nil
        with Goto_no_Decision have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Undecided"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis by fast
      next
        case (Cons rs\<^sub>1a rs\<^sub>1s)
        with rs1rs2 have "rs\<^sub>1 = Rule m (Goto chain) # (take (length rs\<^sub>1s) rest)" by simp
        from Cons rs1rs2 have"rs\<^sub>2 = drop (length rs\<^sub>1s) rest" by simp
        
        from Cons Goto_no_Decision have 1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
          using x by auto[1]
        have 2: "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
          by (simp add: Goto_no_Decision.hyps(1) `rs\<^sub>1 = Rule m (Goto chain) # take (length rs\<^sub>1s) rest`) 
        from 1 2 show ?thesis by fast
      qed
  qed
thus ?thesis using matching_Goto no_matching_Goto by blast 
qed

lemma seqE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  obtains (no_matching_Goto) ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,ti\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p rs\<^sub>1"
        | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
  using assms by (force elim: seq_split)

lemma seqE_cons:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, s\<rangle> \<Rightarrow> t"
  obtains (no_matching_Goto)ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,ti\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p [r]"
        | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p [r]"
           (*TODO: explicitely split the r into Rule m (Goto chain)*)
  using assms by (metis append_Cons append_Nil seqE)

lemma nomatch':
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> \<not> matches \<gamma> (get_match r) p"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> s"
  proof(cases s)
    case Undecided (* TODO larsrh nested proof block *)
    have "\<forall>r\<in>set rs. \<not> matches \<gamma> (get_match r) p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
      proof(induction rs)
        case Nil
        thus ?case by (fast intro: skip)
      next
        case (Cons r rs)
        hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], Undecided\<rangle> \<Rightarrow> Undecided"
          by (cases r) (auto intro: nomatch)
        with Cons show ?case
          by (metis list.set_intros(1) list.set_intros(2) not_no_matching_Goto_singleton_cases rule.collapse seq'_cons)
          (*by (fastforce intro: seq_cons)*) (*TODO*)
      qed
    with assms Undecided show ?thesis by simp
  qed (blast intro: decision)


text{*there are only two cases when there can be a Return on top-level:
\begin{enumerate}
  \item the firewall is in a Decision state
  \item the return does not match
\end{enumerate}
In both cases, it is not applied!
*}
lemma no_free_return: assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> t" and "matches \<gamma> m p" shows "False"
  proof -
  { fix a s
    have no_free_return_hlp: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>a,s\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>  s = Undecided \<Longrightarrow> a = [Rule m Return] \<Longrightarrow> False"
    proof (induction rule: iptables_bigstep.induct)
      case (seq rs\<^sub>1)
      thus ?case
        by (cases rs\<^sub>1) (auto dest: skipD)
    qed simp_all
  } with assms show ?thesis by blast
  qed


(* seq_split is elim, seq_progress is dest *)
lemma seq_progress: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> rs = rs\<^sub>1@rs\<^sub>2 \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, s\<rangle> \<Rightarrow> t' \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t'\<rangle> \<Rightarrow> t"
  proof(induction arbitrary: rs\<^sub>1 rs\<^sub>2 t' rule: iptables_bigstep_induct)
    case Allow
    thus ?case
      by (cases "rs\<^sub>1") (auto intro: iptables_bigstep.intros dest: iptables_bigstepD)
  next
    case Deny
    thus ?case
      by (cases "rs\<^sub>1") (auto intro: iptables_bigstep.intros dest: iptables_bigstepD)
  next
    case Log
    thus ?case
      by (cases "rs\<^sub>1") (auto intro: iptables_bigstep.intros dest: iptables_bigstepD)
  next
    case Nomatch
    thus ?case
      by (cases "rs\<^sub>1") (auto intro: iptables_bigstep.intros dest: iptables_bigstepD)
  next
    case Decision
    thus ?case
      by (cases "rs\<^sub>1") (auto intro: iptables_bigstep.intros dest: iptables_bigstepD)
  next
    case(Seq rs rsa rsb t t' rs\<^sub>1 rs\<^sub>2 t'')
    hence rs: "rsa @ rsb = rs\<^sub>1 @ rs\<^sub>2" by simp
    note List.append_eq_append_conv_if[simp]
    (* TODO larsrh custom case distinction rule *)

    from rs show "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t''\<rangle> \<Rightarrow> t'"
      proof(cases rule: list_app_eq_cases)
        case longer
        have "rs\<^sub>1 = take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1"
          by auto
        with Seq longer show ?thesis
          by (metis append_Nil2 skipD seq_split)
      next
        case shorter
        with Seq(7) Seq.hyps(3) Seq.IH(1) rs show ?thesis
          by (metis Seq.hyps(4) Seq.prems(2) append_take_drop_id no_matching_Goto_append2 seq') 
      qed
  next
    case(Call_return m a chain rsa m' rsb)
    have xx: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t' \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>
          \<Gamma> chain = Some (rsa @ Rule m' Return # rsb) \<Longrightarrow>
          matches \<gamma> m' p \<Longrightarrow>
          \<Gamma>,\<gamma>,p\<turnstile> \<langle>rsa, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow>
          t' = Undecided"
      apply(erule callD)
           apply(simp_all)
      apply(erule seqE)
        apply (metis Call_return.IH append_Nil2 no_free_return seqE_cons skipD)
      by (metis Call_return.IH self_append_conv skipD)

    show ?case
      proof (cases rs\<^sub>1)
        case (Cons r rs)
        thus ?thesis
          using Call_return
          apply(case_tac "[Rule m a] = rs\<^sub>2")
           apply(simp)
          apply(simp)
          using xx by blast
      next
        case Nil
        moreover hence "t' = Undecided" using Call_return.prems(2) skipD by fastforce 
        moreover have "\<And>m. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided"
          by (metis (no_types) Call_return(2) Call_return.hyps(3) Call_return.hyps(4) Call_return.hyps(5) call_return nomatch)
        ultimately show ?thesis
          using Call_return.prems(1) by auto
      qed
  next
    case(Call_result m a chain rs t)
    thus ?case
      proof (cases rs\<^sub>1)
        case Cons
        thus ?thesis
          using Call_result
          apply(auto simp add: iptables_bigstep.skip iptables_bigstep.call_result dest: skipD) (*TODO*)
          apply(drule callD, simp_all)
           apply blast
          by (metis Cons_eq_appendI append_self_conv2 no_free_return seq_split)
      qed (fastforce intro: iptables_bigstep.intros dest: skipD)
  next
    case(Goto_no_Decision m a chain rs t)
    thus ?case sorry (*here we will need to split it again whether a matching goto occurs in the first part. it is probably better to make two lemmas out of it*)
  next
    case(Goto_Decision)
    thus ?case sorry
  qed (auto dest: iptables_bigstepD)


theorem iptables_bigstep_deterministic: assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t'" shows "t = t'"
proof -
  { fix r1 r2 m t
    assume a1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r1 @ Rule m Return # r2, Undecided\<rangle> \<Rightarrow> t" and a2: "matches \<gamma> m p" and a3: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r1,Undecided\<rangle> \<Rightarrow> Undecided"
    have False
    proof -
      from a1 a3 have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Return # r2, Undecided\<rangle> \<Rightarrow> t"
        by (blast intro: seq_progress)
      hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return] @ r2, Undecided\<rangle> \<Rightarrow> t"
        by simp
      from seqE[OF this] obtain ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> ti" by blast
      with no_free_return a2 show False by fast (*by (blast intro: no_free_return elim: seq_split)*)
    qed
  } note no_free_return_seq=this
  
  from assms show ?thesis
  proof (induction arbitrary: t' rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (metis seq_progress)
  next
    case Call_result
    thus ?case
      by (metis no_free_return_seq callD)
  next
    case Call_return
    thus ?case
      by (metis append_Cons callD no_free_return_seq)
  next
    case Goto
    thus ?case by (metis gotoD)
  qed (auto dest: iptables_bigstepD)
qed


lemma Rule_UndecidedE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided"
  obtains (nomatch) "\<not> matches \<gamma> m p"
        | (log) "a = Log \<or> a = Empty"
        | (call) c where "a = Call c" "matches \<gamma> m p"
        | (goto) c where "a = Goto c" "matches \<gamma> m p"
  using assms
  proof (induction "[Rule m a]" Undecided Undecided rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (metis append_eq_Cons_conv append_is_Nil_conv iptables_bigstep_to_undecided)
  qed simp_all

lemma Rule_DecisionE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Decision X"
  obtains (call) chain where "matches \<gamma> m p" "a = Call chain \<or> a = Goto chain"
        | (accept_reject) "matches \<gamma> m p" "X = FinalAllow \<Longrightarrow> a = Accept" "X = FinalDeny \<Longrightarrow> a = Drop \<or> a = Reject"
  using assms
  proof (induction "[Rule m a]" Undecided "Decision X" rule: iptables_bigstep_induct)
    case (Seq rs\<^sub>1)
    thus ?case
      by (cases rs\<^sub>1) (auto dest: skipD)
  qed simp_all


lemma log_remove:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1 @ [Rule m Log] @ rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1 @ rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  proof -
    from assms obtain t' where t': "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, s\<rangle> \<Rightarrow> t'" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Log] @ rs\<^sub>2, t'\<rangle> \<Rightarrow> t"
      by (blast elim: seqE)
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Log # rs\<^sub>2, t'\<rangle> \<Rightarrow> t"
      by simp
    then obtain t'' where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Log], t'\<rangle> \<Rightarrow> t''" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t''\<rangle> \<Rightarrow> t"
      by (blast elim: seqE_cons)
    with t' show ?thesis
      by (metis state.exhaust iptables_bigstep_deterministic decision log nomatch seq)
  qed
lemma empty_empty:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1 @ [Rule m Empty] @ rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1 @ rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  proof -
    from assms obtain t' where t': "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, s\<rangle> \<Rightarrow> t'" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Empty] @ rs\<^sub>2, t'\<rangle> \<Rightarrow> t"
      by (blast elim: seqE)
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Empty # rs\<^sub>2, t'\<rangle> \<Rightarrow> t"
      by simp
    then obtain t'' where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Empty], t'\<rangle> \<Rightarrow> t''" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t''\<rangle> \<Rightarrow> t"
      by (blast elim: seqE_cons)
    with t' show ?thesis
      by (metis state.exhaust iptables_bigstep_deterministic decision empty nomatch seq)
  qed


(* TODO: add goto
text{*
The notation we prefer in the paper. The semantics are defined for fixed @{text \<Gamma>} and @{text \<gamma>}
*}
locale iptables_bigstep_fixedbackground =
  fixes \<Gamma>::"'a ruleset"
  and \<gamma>::"('a, 'p) matcher"
  begin

  inductive iptables_bigstep' :: "'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
    ("_\<turnstile>' \<langle>_, _\<rangle> \<Rightarrow> _"  [60,20,98,98] 89)
    for p where
  skip:    "p\<turnstile>' \<langle>[], t\<rangle> \<Rightarrow> t" |
  accept:  "matches \<gamma> m p \<Longrightarrow> p\<turnstile>' \<langle>[Rule m Accept], Undecided\<rangle> \<Rightarrow> Decision FinalAllow" |
  drop:    "matches \<gamma> m p \<Longrightarrow> p\<turnstile>' \<langle>[Rule m Drop], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
  reject:  "matches \<gamma> m p \<Longrightarrow>  p\<turnstile>' \<langle>[Rule m Reject], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
  log:     "matches \<gamma> m p \<Longrightarrow> p\<turnstile>' \<langle>[Rule m Log], Undecided\<rangle> \<Rightarrow> Undecided" |
  empty:   "matches \<gamma> m p \<Longrightarrow> p\<turnstile>' \<langle>[Rule m Empty], Undecided\<rangle> \<Rightarrow> Undecided" |
  nomatch: "\<not> matches \<gamma> m p \<Longrightarrow> p\<turnstile>' \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided" |
  decision: "p\<turnstile>' \<langle>rs, Decision X\<rangle> \<Rightarrow> Decision X" |
  seq:      "\<lbrakk>p\<turnstile>' \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t; p\<turnstile>' \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t'\<rbrakk> \<Longrightarrow> p\<turnstile>' \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t'" |
  call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1@[Rule m' Return]@rs\<^sub>2);
                   matches \<gamma> m' p; p\<turnstile>' \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<rbrakk> \<Longrightarrow>
                 p\<turnstile>' \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" |
  call_result:  "\<lbrakk> matches \<gamma> m p; p\<turnstile>' \<langle>the (\<Gamma> chain), Undecided\<rangle> \<Rightarrow> t \<rbrakk> \<Longrightarrow>
                 p\<turnstile>' \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"

  definition wf_\<Gamma>:: "'a rule list \<Rightarrow> bool" where
    "wf_\<Gamma> rs \<equiv> \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. (\<forall>r \<in> set rsg. \<forall> chain. get_action r = Call chain \<longrightarrow> \<Gamma> chain \<noteq> None)"

  lemma wf_\<Gamma>_append: "wf_\<Gamma> (rs1@rs2) \<longleftrightarrow> wf_\<Gamma> rs1 \<and> wf_\<Gamma> rs2"
    by(simp add: wf_\<Gamma>_def, blast)
  lemma wf_\<Gamma>_tail: "wf_\<Gamma> (r # rs) \<Longrightarrow> wf_\<Gamma> rs" by(simp add: wf_\<Gamma>_def)
  lemma wf_\<Gamma>_Call: "wf_\<Gamma> [Rule m (Call chain)] \<Longrightarrow> wf_\<Gamma> (the (\<Gamma> chain)) \<and> (\<exists>rs. \<Gamma> chain = Some rs)"
    apply(simp add: wf_\<Gamma>_def)
    by (metis option.collapse ranI)
  
  lemma "wf_\<Gamma> rs \<Longrightarrow> p\<turnstile>' \<langle>rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
    apply(rule iffI)
     apply(rotate_tac 1)
     apply(induction rs s t rule: iptables_bigstep'.induct)
               apply(auto intro: iptables_bigstep.intros simp: wf_\<Gamma>_append dest!: wf_\<Gamma>_Call)[11]
    apply(rotate_tac 1)
    apply(induction rs s t rule: iptables_bigstep.induct)
              apply(auto intro: iptables_bigstep'.intros simp: wf_\<Gamma>_append dest!: wf_\<Gamma>_Call)[11]
    done
    
  end
*)

end
