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
seq:      "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t'\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t'" |
call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1@[Rule m' Return]@rs\<^sub>2);
                 matches \<gamma> m' p; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" |
call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"

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
@{thm[mode=Rule] call_result [no_vars]}
\end{center}
*}


(*future work:
  Add abstraction function for unknown actions. At the moment, only the explicitly listed actions are supported.
  This would also require a @{text "Decision FinalUnknown"} state
  Problem: An unknown action may modify a packet.
  Assume that we have a firewall which accepts the packets A->B and rewrites the header to A->C.
  After that firewall, there is another firewall which only accepts packets for A->C.
  A can send through both firewalls.
  
  If our model says that the firewall accepts packets A->B but does not consider packet modification,
  A might not be able to pass the second firewall with this model.
  
  Luckily, our model is correct for the filtering behaviour and explicitly does not support any actions with packet modification.
  Thus, the described scenario is not a counterexample that our model is wrong but a hint for future features
  we may want to support. Luckily, we introduced the @{term Decision} state, which should make adding packet modification states easy.
*)

lemma deny:
  "matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> iptables_bigstep \<Gamma> \<gamma> p [Rule m a] Undecided (Decision FinalDeny)"
by (auto intro: drop reject)

lemma seq_cons:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],Undecided\<rangle> \<Rightarrow> t" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,t\<rangle> \<Rightarrow> t'"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, Undecided\<rangle> \<Rightarrow> t'"
proof -
  from assms have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r] @ rs, Undecided\<rangle> \<Rightarrow> t'" by (rule seq)
  thus ?thesis by simp
qed

lemma iptables_bigstep_induct
  [case_names Skip Allow Deny Log Nomatch Decision Seq Call_return Call_result,
   induct pred: iptables_bigstep]:
  "\<lbrakk> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t;
     \<And>t. P [] t t;
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Accept \<Longrightarrow> P [Rule m a] Undecided (Decision FinalAllow);
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> P [Rule m a] Undecided (Decision FinalDeny);
     \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Log \<or> a = Empty \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>m a. \<not> matches \<gamma> m p \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>rs X. P rs (Decision X) (Decision X);
     \<And>rs rs\<^sub>1 rs\<^sub>2 t t'. rs = rs\<^sub>1 @ rs\<^sub>2 \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs\<^sub>1 Undecided t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t' \<Longrightarrow> P rs\<^sub>2 t t' \<Longrightarrow> P rs Undecided t';
     \<And>m a chain rs\<^sub>1 m' rs\<^sub>2. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow> \<Gamma> chain = Some (rs\<^sub>1 @ [Rule m' Return] @ rs\<^sub>2) \<Longrightarrow> matches \<gamma> m' p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> P rs\<^sub>1 Undecided Undecided \<Longrightarrow> P [Rule m a] Undecided Undecided;
     \<And>m a chain rs t. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs Undecided t \<Longrightarrow> P [Rule m a] Undecided t \<rbrakk> \<Longrightarrow>
   P rs s t"
by (induction rule: iptables_bigstep.induct) auto

lemma skipD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [] \<Longrightarrow> s = t"
by (induction rule: iptables_bigstep.induct) auto

lemma decisionD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> s = Decision X \<Longrightarrow> t = Decision X"
by (induction rule: iptables_bigstep_induct) auto

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

lemmas iptables_bigstepD = skipD acceptD dropD rejectD logD emptyD nomatchD decisionD callD

lemma seq':
  assumes "rs = rs\<^sub>1 @ rs\<^sub>2" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t'"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t'"
using assms by (cases s) (auto intro: seq decision dest: decisionD)

lemma seq'_cons: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,t\<rangle> \<Rightarrow> t' \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, s\<rangle> \<Rightarrow> t'"
by (metis decision decisionD state.exhaust seq_cons)

lemma seq_split:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" "rs = rs\<^sub>1@rs\<^sub>2"
  obtains t' where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t'" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t'\<rangle> \<Rightarrow> t"
  using assms
  proof (induction rs s t arbitrary: rs\<^sub>1 rs\<^sub>2 thesis rule: iptables_bigstep_induct)
    case Allow thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros)
  next
    case Deny thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros)
  next
    case Log thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros)
  next
    case Nomatch thus ?case by (cases rs\<^sub>1) (auto intro: iptables_bigstep.intros)
  next
    case (Seq rs rsa rsb t t')
    hence rs: "rsa @ rsb = rs\<^sub>1 @ rs\<^sub>2" by simp
    note List.append_eq_append_conv_if[simp]
    from rs show ?case
      proof (cases rule: list_app_eq_cases)
        case longer
        with Seq have t1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t"
          by simp
        from Seq longer obtain t2
          where t2a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa) rs\<^sub>1,t\<rangle> \<Rightarrow> t2"
            and rs2_t2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t2\<rangle> \<Rightarrow> t'"
          by blast
        with t1 rs2_t2 have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t2"
          by (blast intro: iptables_bigstep.seq)
        with Seq rs2_t2 show ?thesis
          by simp
      next
        case shorter
        with rs have rsa': "rsa = rs\<^sub>1 @ take (length rsa - length rs\<^sub>1) rs\<^sub>2"
          by (metis append_eq_conv_conj length_drop)
        from shorter rs have rsb': "rsb = drop (length rsa - length rs\<^sub>1) rs\<^sub>2"
          by (metis append_eq_conv_conj length_drop)
        from Seq rsa' obtain t1
          where t1a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t1"
            and t1b: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>take (length rsa - length rs\<^sub>1) rs\<^sub>2,t1\<rangle> \<Rightarrow> t"
          by blast
        from rsb' Seq.hyps have t2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>drop (length rsa - length rs\<^sub>1) rs\<^sub>2,t\<rangle> \<Rightarrow> t'"
          by blast
        with seq' t1b have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,t1\<rangle> \<Rightarrow> t'"
          by fastforce
        with Seq t1a show ?thesis
          by fast
      qed
  next
    case Call_return
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Undecided"
      by (case_tac [!] rs\<^sub>1) (auto intro: iptables_bigstep.skip iptables_bigstep.call_return)
    thus ?case by fact
  next
    case (Call_result _ _ _ _ t)
    show ?case
      proof (cases rs\<^sub>1)
        case Nil
        with Call_result have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis by fact
      next
        case Cons
        with Call_result have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t"
          by (auto intro: iptables_bigstep.intros)
        thus ?thesis by fact
      qed
  qed (auto intro: iptables_bigstep.intros)

lemma seqE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, s\<rangle> \<Rightarrow> t"
  obtains ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2,ti\<rangle> \<Rightarrow> t"
  using assms by (force elim: seq_split)

lemma seqE_cons:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, s\<rangle> \<Rightarrow> t"
  obtains ti where "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r],s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,ti\<rangle> \<Rightarrow> t"
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
          by (fastforce intro: seq_cons)
      qed
    with assms Undecided show ?thesis by simp
  qed (blast intro: decision)

lemma no_free_return_hlp: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>a,s\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>  s = Undecided \<Longrightarrow> a = [Rule m Return] \<Longrightarrow> False"
  proof (induction rule: iptables_bigstep.induct)
    case (seq rs\<^sub>1)
    thus ?case
      by (cases rs\<^sub>1) (auto dest: skipD)
  qed simp_all

lemma no_free_return: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> False"
  by (metis no_free_return_hlp)


(* TODO corny: seq_split?! *)
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
          by (metis seq' append_eq_conv_conj)
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
      apply(erule seqE_cons)
      by (metis Call_return.IH no_free_return self_append_conv skipD)

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
        moreover hence "t' = Undecided"
          by (metis Call_return.hyps(1) Call_return.prems(2) append.simps(1) decision no_free_return seq state.exhaust)
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
          apply(auto simp add: iptables_bigstep.skip iptables_bigstep.call_result dest: skipD)
          apply(drule callD, simp_all)
          apply blast
          by (metis Cons_eq_appendI append_self_conv2 no_free_return seq_split)
      qed (fastforce intro: iptables_bigstep.intros dest: skipD)
  qed (auto dest: iptables_bigstepD)

lemma no_free_return_seq:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r1 @ Rule m Return # r2, Undecided\<rangle> \<Rightarrow> t" "matches \<gamma> m p" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r1,Undecided\<rangle> \<Rightarrow> Undecided"
  shows False
  proof -
    from assms have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Return # r2, Undecided\<rangle> \<Rightarrow> t"
      by (blast intro: seq_progress)
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return] @ r2, Undecided\<rangle> \<Rightarrow> t"
      by simp
    with assms show False
      by (blast intro: no_free_return elim: seq_split)
  qed

text{*there are only two cases when there can be a Return on top-level:
\begin{enumerate}
  \item the firewall is in a Decision state
  \item the return does not match
\end{enumerate}
In both cases, it is not applied!
*}
lemma no_free_return_fst:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs, s\<rangle> \<Rightarrow> t"
  obtains (decision) X where "s = Decision X"
        | (nomatch) m a where "r = Rule m a" "a \<noteq> Return \<or> \<not> matches \<gamma> m p"
  using assms
  proof (induction "r#rs" s t rule: iptables_bigstep_induct)
    case Seq thus ?case
      by (metis no_free_return_seq seq skip rule.exhaust)
  qed auto

lemma iptables_bigstep_deterministic: "\<lbrakk> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t = t'"
  proof (induction arbitrary: t' rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (metis seq_split)
  next
    case Call_result
    thus ?case
      by (metis no_free_return_seq callD)
  next
    case Call_return
    thus ?case
      by (metis append_Cons callD no_free_return_seq)
  qed (auto dest: iptables_bigstepD)

lemma iptables_bigstep_to_undecided: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> Undecided \<Longrightarrow> s = Undecided"
  by (metis decisionD state.exhaust)

lemma iptables_bigstep_to_decision: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Decision Y\<rangle> \<Rightarrow> Decision X \<Longrightarrow> Y = X"
  by (metis decisionD state.inject)

lemma Rule_UndecidedE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided"
  obtains (nomatch) "\<not> matches \<gamma> m p"
        | (log) "a = Log \<or> a = Empty"
        | (call) c where "a = Call c" "matches \<gamma> m p"
  using assms
  proof (induction "[Rule m a]" Undecided Undecided rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (metis append_eq_Cons_conv append_is_Nil_conv iptables_bigstep_to_undecided)
  qed simp_all

lemma Rule_DecisionE:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Decision X"
  obtains (call) chain where "matches \<gamma> m p" "a = Call chain"
        | (accept_reject) "matches \<gamma> m p" "X = FinalAllow \<Longrightarrow> a = Accept" "X = FinalDeny \<Longrightarrow> a = Drop \<or> a = Reject"
  using assms
  proof (induction "[Rule m a]" Undecided "Decision X" rule: iptables_bigstep_induct)
    case (Seq rs\<^sub>1)
    thus ?case
      by (cases rs\<^sub>1) (auto dest: skipD)
  qed simp_all

(*TODO: tune*)
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


end
