theory Semantics
imports Main Firewall_Common "Common/List_Misc" "~~/src/HOL/Library/LaTeXsugar"
begin

section\<open>Big Step Semantics\<close>


text\<open>
The assumption we apply in general is that the firewall does not alter any packets.
\<close>

text\<open>A firewall ruleset is a map of chain names
  (e.g., INPUT, OUTPUT, FORWARD, arbitrary-user-defined-chain) to a list of rules.
  The list of rules is processed sequentially.\<close>
type_synonym 'a ruleset = "string \<rightharpoonup> 'a rule list"

text\<open>A matcher (parameterized by the type of primitive @{typ 'a} and packet @{typ 'p})
     is a function which just tells whether a given primitive and packet matches.\<close>
type_synonym ('a, 'p) matcher = "'a \<Rightarrow> 'p \<Rightarrow> bool"

text\<open>Example: Assume a network packet only has a destination street number
    (for simplicity, of type @{typ "nat"}) and we only support the following match expression:
    Is the packet's street number within a certain range?
    The type for the primitive could then be @{typ "nat \<times> nat"} and a possible implementation
    for @{typ "(nat \<times> nat, nat) matcher"} could be
    @{term "match_street_number (a,b) p \<longleftrightarrow> p \<in> {a .. b}"}.
    Usually, the primitives are a datatype which supports interfaces, IP addresses, protocols,
    ports, payload, ...\<close>


text\<open>Given an @{typ "('a, 'p) matcher"} and a match expression, does a packet of type @{typ 'p}
     match the match expression?\<close>
fun matches :: "('a, 'p) matcher \<Rightarrow> 'a match_expr \<Rightarrow> 'p \<Rightarrow> bool" where
"matches \<gamma> (MatchAnd e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<and> matches \<gamma> e2 p" |
"matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" |
"matches \<gamma> (Match e) p \<longleftrightarrow> \<gamma> e p" |
"matches _ MatchAny _ \<longleftrightarrow> True"


(*Note: "matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" does not work for ternary logic.
  Here, we have Boolean logic and everything is fine.*)


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

text\<open>
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
\<close>


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
  we may want to support. Luckily, we introduced the @{term "Decision state"}, which should make adding packet modification states easy.
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
    case Undecided
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


text\<open>there are only two cases when there can be a Return on top-level:

  \<^item> the firewall is in a Decision state
  \<^item> the return does not match

In both cases, it is not applied!
\<close>
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
  qed (auto dest: iptables_bigstepD)
qed

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



lemma Unknown_actions_False: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> r = Rule m a \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> a = Unknown \<or> (\<exists>chain. a = Goto chain) \<Longrightarrow> False"
proof -
  have 1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Unknown], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> False"
  by (induction "[Rule m Unknown]" Undecided t rule: iptables_bigstep.induct)
     (auto elim: list_app_singletonE dest: skipD)
  
  { fix chain
    have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> False"
    by (induction "[Rule m (Goto chain)]" Undecided t rule: iptables_bigstep.induct)
       (auto elim: list_app_singletonE dest: skipD)
  }note 2=this
  show "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> r = Rule m a \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> a = Unknown \<or> (\<exists>chain. a = Goto chain) \<Longrightarrow> False"
  apply(erule seqE_cons)
  apply(case_tac ti)
   apply(simp_all)
   using Rule_UndecidedE apply fastforce
  by (metis "1" "2" decision iptables_bigstep_deterministic)
qed

text\<open>
The notation we prefer in the paper. The semantics are defined for fixed @{text \<Gamma>} and @{text \<gamma>}
\<close>
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




text\<open>Showing that semantics are defined.
  For rulesets which can be loaded by the Linux kernel. The kernel does not allow loops.\<close>




text\<open>
  We call a ruleset well-formed (wf) iff all @{const Call}s are into actually existing chains.
\<close>
definition wf_chain :: "'a ruleset \<Rightarrow> 'a rule list \<Rightarrow> bool" where
  "wf_chain \<Gamma> rs \<equiv> (\<forall>r \<in> set rs. \<forall> chain. get_action r = Call chain \<longrightarrow> \<Gamma> chain \<noteq> None)"
lemma wf_chain_append: "wf_chain \<Gamma> (rs1@rs2) \<longleftrightarrow> wf_chain \<Gamma> rs1 \<and> wf_chain \<Gamma> rs2"
  by(simp add: wf_chain_def, blast)

lemma wf_chain_fst: "wf_chain \<Gamma> (r # rs) \<Longrightarrow>  wf_chain \<Gamma> (rs)"
  by(simp add: wf_chain_def)


text\<open>This is what our tool will check at runtime\<close>
definition sanity_wf_ruleset :: "(string \<times> 'a rule list) list \<Rightarrow> bool" where
  "sanity_wf_ruleset \<Gamma> \<equiv> distinct (map fst \<Gamma>) \<and>
          (\<forall> rs \<in> ran (map_of \<Gamma>). (\<forall>r \<in> set rs. case get_action r of Accept \<Rightarrow> True
                                                                    | Drop \<Rightarrow> True
                                                                    | Reject \<Rightarrow> True
                                                                    | Log \<Rightarrow> True
                                                                    | Empty \<Rightarrow> True
                                                                    | Call chain \<Rightarrow> chain \<in> dom (map_of \<Gamma>)
                                                                    | Goto chain \<Rightarrow> chain \<in> dom (map_of \<Gamma>)
                                                                    | Return \<Rightarrow> True
                                                                    | _ \<Rightarrow> False))"

lemma sanity_wf_ruleset_wf_chain: "sanity_wf_ruleset \<Gamma> \<Longrightarrow> rs \<in> ran (map_of \<Gamma>) \<Longrightarrow> wf_chain (map_of \<Gamma>) rs"
  apply(simp add: sanity_wf_ruleset_def wf_chain_def)
  by fastforce

lemma sanity_wf_ruleset_start: "sanity_wf_ruleset \<Gamma> \<Longrightarrow> chain_name \<in> dom (map_of \<Gamma>) \<Longrightarrow>
  default_action = Accept \<or> default_action = Drop \<Longrightarrow> 
  wf_chain (map_of \<Gamma>) [Rule MatchAny (Call chain_name), Rule MatchAny default_action]"
 apply(simp add: sanity_wf_ruleset_def wf_chain_def)
 apply(safe)
  apply(simp_all)
  apply blast+
 done

lemma [code]: "sanity_wf_ruleset \<Gamma> =
  (let dom = map fst \<Gamma>;
       ran = map snd \<Gamma>
   in distinct dom \<and>
    (\<forall> rs \<in> set ran. (\<forall>r \<in> set rs. case get_action r of Accept \<Rightarrow> True
                                                       | Drop \<Rightarrow> True
                                                       | Reject \<Rightarrow> True
                                                       | Log \<Rightarrow> True
                                                       | Empty \<Rightarrow> True
                                                       | Call chain \<Rightarrow> chain \<in> set dom
                                                       | Goto chain \<Rightarrow> chain \<in> set dom
                                                       | Return \<Rightarrow> True
                                                       | _ \<Rightarrow> False)))"
  proof -
  have set_map_fst: "set (map fst \<Gamma>) = dom (map_of \<Gamma>)"
    by (simp add: dom_map_of_conv_image_fst)
  have set_map_snd: "distinct (map fst \<Gamma>) \<Longrightarrow> set (map snd \<Gamma>) = ran (map_of \<Gamma>)"
    by (simp add: ran_distinct)
  show ?thesis
  unfolding sanity_wf_ruleset_def Let_def
  apply(subst set_map_fst)+
  apply(rule iffI)
   apply(elim conjE)
   apply(subst set_map_snd)
    apply(simp)
   apply(simp)
  apply(elim conjE)
  apply(subst(asm) set_map_snd)
   apply(simp_all)
  done
qed





lemma semantics_bigstep_defined1: assumes "\<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg"
  and "\<forall>rsg \<in> ran \<Gamma> \<union> {rs}. \<forall> r \<in> set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown"
  and "\<forall> r \<in> set rs. get_action r \<noteq> Return" (*no toplevel return*)
  and "(\<forall>name \<in> dom \<Gamma>. \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>the (\<Gamma> name), Undecided\<rangle> \<Rightarrow> t)" (*defined for all chains in the background ruleset*)
  shows "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
using assms proof(induction rs)
case Nil thus ?case
 apply(rule_tac x=s in exI)
 by(simp add: skip)
next
case (Cons r rs)
  from Cons.prems Cons.IH obtain t' where t': "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t'"
    apply simp
    apply(elim conjE)
    apply(simp add: wf_chain_fst)
    by blast

  obtain m a where r: "r = Rule m a" by(cases r) blast

  show ?case
  proof(cases "matches \<gamma> m p")
  case False
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], s\<rangle> \<Rightarrow> s"
      apply(cases s)
       apply(simp add: nomatch r)
      by(simp add: decision)
    thus ?thesis
      apply(rule_tac x=t' in exI)
      apply(rule_tac t=s in seq'_cons)
       apply assumption
      using t' by(simp)
  next
  case True
    show ?thesis
    proof(cases s)
    case (Decision X) thus ?thesis
      apply(rule_tac x="Decision X" in exI)
      by(simp add: decision)
    next
    case Undecided
      have "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m a # rs, Undecided\<rangle> \<Rightarrow> t"
      proof(cases a)
        case Accept with True show ?thesis
          apply(rule_tac x="Decision FinalAllow" in exI)
          apply(rule_tac t="Decision FinalAllow" in seq'_cons)
           by(auto intro: iptables_bigstep.intros)
        next
        case Drop with True show ?thesis
          apply(rule_tac x="Decision FinalDeny" in exI)
          apply(rule_tac t="Decision FinalDeny" in seq'_cons)
           by(auto intro: iptables_bigstep.intros)
        next
        case Log with True t' Undecided show ?thesis
          apply(rule_tac x=t' in exI)
          apply(rule_tac t=Undecided in seq'_cons)
           by(auto intro: iptables_bigstep.intros)
        next
        case Reject with True show ?thesis
          apply(rule_tac x="Decision FinalDeny" in exI)
          apply(rule_tac t="Decision FinalDeny" in seq'_cons)
           by(auto intro: iptables_bigstep.intros)[2]
        next
        case Return with Cons.prems(3)[simplified r] show ?thesis by simp
        next
        case Goto with Cons.prems(2)[simplified r] show ?thesis by auto
        next
        case (Call chain_name)
          from Call Cons.prems(1) obtain rs' where 1: "\<Gamma> chain_name = Some rs'" by(simp add: r wf_chain_def) blast
          with Cons.prems(4) obtain t'' where 2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>the (\<Gamma> chain_name), Undecided\<rangle> \<Rightarrow> t''" by blast
          from 1 2 True have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain_name)], Undecided\<rangle> \<Rightarrow> t''" by(auto dest: call_result)
          with Call t' Undecided show ?thesis
          apply(simp add: r)
          apply(cases t'')
           apply simp
           apply(rule_tac x=t' in exI)
           apply(rule_tac t=Undecided in seq'_cons)
            apply(auto intro: iptables_bigstep.intros)[2]
          apply(simp)
          apply(rule_tac x=t'' in exI)
          apply(rule_tac t=t'' in seq'_cons)
           apply(auto intro: iptables_bigstep.intros)
         done
        next
        case Empty  with True t' Undecided show ?thesis
         apply(rule_tac x=t' in exI)
         apply(rule_tac t=Undecided in seq'_cons)
          by(auto intro: iptables_bigstep.intros)
        next
        case Unknown with Cons.prems(2)[simplified r] show ?thesis by(simp)
      qed
      thus ?thesis
      unfolding r Undecided by simp
    qed
  qed
qed

text\<open>Showing the main theorem\<close>

context
begin
  private lemma iptables_bigstep_defined_if_singleton_rules:
  "\<forall> r \<in> set rs. (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], s\<rangle> \<Rightarrow> t) \<Longrightarrow> \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  proof(induction rs arbitrary: s)
  case Nil hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[], s\<rangle> \<Rightarrow> s" by(simp add: skip)
     thus ?case by blast
  next
  case(Cons r rs s)
    from Cons.prems obtain t where t: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], s\<rangle> \<Rightarrow> t" by simp blast
    with Cons show ?case
    proof(cases t)
      case Decision with t show ?thesis by (meson decision seq'_cons)
      next
      case Undecided
      from Cons obtain t' where t': "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t'" by simp blast
      with Undecided t show ?thesis
      apply(rule_tac x=t' in exI)
      apply(rule seq'_cons)
       apply(simp)
      using iptables_bigstep_to_undecided by fastforce
    qed
  qed
  
  
  
  
  
  
  
  text\<open>well founded relation.\<close>
  definition calls_chain :: "'a ruleset \<Rightarrow> (string \<times> string) set" where
    "calls_chain \<Gamma> = {(r, s). case \<Gamma> r of Some rs \<Rightarrow> \<exists>m. Rule m (Call s) \<in> set rs | None \<Rightarrow> False}"  
  
  lemma calls_chain_def2: "calls_chain \<Gamma> = {(caller, callee). \<exists>rs m. \<Gamma> caller = Some rs \<and> Rule m (Call callee) \<in> set rs}"
    unfolding calls_chain_def
    apply(safe)
     apply(simp split: option.split_asm)
    apply(simp)
    by blast
  
  text\<open>example\<close>
  private lemma "calls_chain [
      ''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
      ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
      ''bar'' \<mapsto> [],
      ''baz'' \<mapsto> []] =
      {(''FORWARD'', ''foo''), (''FORWARD'', ''baz''), (''foo'', ''bar'')}"
    unfolding calls_chain_def by(auto split: option.split_asm if_split_asm)
  
  private lemma "wf (calls_chain [
      ''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
      ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
      ''bar'' \<mapsto> [],
      ''baz'' \<mapsto> []])"
  proof -
    have g: "calls_chain [''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
            ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
            ''bar'' \<mapsto> [],
            ''baz'' \<mapsto> []] = {(''FORWARD'', ''foo''), (''FORWARD'', ''baz''), (''foo'', ''bar'')}"
    by(auto simp add: calls_chain_def split: option.split_asm if_split_asm)
    show ?thesis
      unfolding g
      apply(simp)
      apply safe
       apply(erule rtranclE, simp_all)
      apply(erule rtranclE, simp_all)
      done
  qed    
      
  
  text\<open>In our proof, we will need the reverse.\<close>
  private definition called_by_chain :: "'a ruleset \<Rightarrow> (string \<times> string) set" where
    "called_by_chain \<Gamma> = {(callee, caller). case \<Gamma> caller of Some rs \<Rightarrow> \<exists>m. Rule m (Call callee) \<in> set rs | None \<Rightarrow> False}"
  private lemma called_by_chain_converse: "calls_chain \<Gamma> = converse (called_by_chain \<Gamma>)"
    apply(simp add: calls_chain_def called_by_chain_def)
    by blast
  private lemma wf_called_by_chain: "finite (calls_chain \<Gamma>) \<Longrightarrow> wf (calls_chain \<Gamma>) \<Longrightarrow> wf (called_by_chain \<Gamma>)"
    apply(frule Wellfounded.wf_acyclic)
    apply(drule(1) Wellfounded.finite_acyclic_wf_converse)
    apply(simp add: called_by_chain_converse)
    done
  
  
  private lemma helper_cases_call_subchain_defined_or_return:
        "(\<forall>x\<in>ran \<Gamma>. wf_chain \<Gamma> x) \<Longrightarrow>
         \<forall>rsg\<in>ran \<Gamma>. \<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
         \<forall>y m. \<forall>r\<in>set rs_called. r = Rule m (Call y) \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], Undecided\<rangle> \<Rightarrow> t) \<Longrightarrow>
         wf_chain \<Gamma> rs_called \<Longrightarrow> 
         \<forall>r\<in>set rs_called. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
         (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called, Undecided\<rangle> \<Rightarrow> t) \<or>
         (\<exists>rs_called1 rs_called2 m'.
             rs_called = (rs_called1 @ [Rule m' Return] @ rs_called2) \<and>
             matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided)"
  proof(induction rs_called arbitrary:)
  case Nil hence "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> t"
     apply(rule_tac x=Undecided in exI)
     by(simp add: skip)
   thus ?case by simp
  next
  case (Cons r rs)
    from Cons.prems have "wf_chain \<Gamma> [r]" by(simp add: wf_chain_def)
    from Cons.prems have IH:"(\<exists>t'. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t') \<or>
      (\<exists>rs_called1 rs_called2 m'.
          rs = (rs_called1 @ [Rule m' Return] @ rs_called2) \<and>
          matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided)"
      apply -
      apply(rule Cons.IH)
          apply(auto dest: wf_chain_fst)
      done
  
    from Cons.prems have case_call: "r = Rule m (Call y) \<Longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], Undecided\<rangle> \<Rightarrow> t)" for y m
      by(simp)
  
    obtain m a where r: "r = Rule m a" by(cases r) simp
  
    from Cons.prems have a_not: "(\<forall>chain. a \<noteq> Goto chain) \<and> a \<noteq> Unknown" by(simp add: r)
  
    have ex_neq_ret: "a \<noteq> Return \<Longrightarrow> \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> t"
    proof(cases "matches \<gamma> m p")
    case False thus ?thesis by(rule_tac x=Undecided in exI)(simp add: nomatch; fail)
    next
    case True
      assume "a \<noteq> Return"
      show ?thesis
      proof(cases a)
      case Accept with True show ?thesis
        by(rule_tac x="Decision FinalAllow" in exI) (simp add: accept; fail)
      next
      case Drop with True show ?thesis
        by(rule_tac x="Decision FinalDeny" in exI) (simp add: drop; fail)
      next
      case Log with True show ?thesis
        by(rule_tac x="Undecided" in exI)(simp add: log; fail)
      next
      case Reject with True show ?thesis
        by(rule_tac x="Decision FinalDeny" in exI) (simp add: reject; fail)
      next
      case Call with True show ?thesis
        apply(simp)
        apply(rule case_call)
        apply(simp add: r; fail)
        done
      next
      case Empty with True show ?thesis by(rule_tac x="Undecided" in exI) (simp add: empty; fail)
      next
      case Return with \<open>a \<noteq> Return\<close> show ?thesis by simp
      qed(simp_all add: a_not)
    qed
  
    have *: "?case"
      if pre: "rs = rs_called1 @ Rule m' Return # rs_called2 \<and> matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided"
      for rs_called1 m' rs_called2
    proof(cases "matches \<gamma> m p")
    case False thus ?thesis
      apply -
      apply(rule disjI2)
      apply(rule_tac x="r#rs_called1" in exI)
      apply(rule_tac x=rs_called2 in exI)
      apply(rule_tac x=m' in exI)
      apply(simp add: r pre)
      apply(rule_tac t=Undecided in seq_cons)
       apply(simp add: r nomatch; fail)
      apply(simp add: pre; fail)
      done
    next
    case True
      from pre have rule_case_dijs1: "\<exists>X. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow> ?thesis"
        apply -
        apply(rule disjI1)
        apply(elim exE conjE, rename_tac X)
        apply(simp)
        apply(rule_tac x="Decision X" in exI)
        apply(rule_tac t="Decision X" in seq_cons)
         apply(simp add: r; fail)
        apply(simp add: decision; fail)
        done

      from pre have rule_case_dijs2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> ?thesis"
        apply -
        apply(rule disjI2)
        apply(rule_tac x="r#rs_called1" in exI)
        apply(rule_tac x=rs_called2 in exI)
        apply(rule_tac x=m' in exI)
        apply(simp add: r)
        apply(rule_tac t=Undecided in seq_cons)
         apply(simp; fail)
        apply(simp;fail)
        done

      show ?thesis
      proof(cases a)
      case Accept show ?thesis
        apply(rule rule_case_dijs1)
        apply(rule_tac x="FinalAllow" in exI)
        using True pre Accept by(simp add: accept)
      next
      case Drop show ?thesis
        apply(rule rule_case_dijs1)
        apply(rule_tac x="FinalDeny" in exI)
        using True Drop by(simp add: deny)
      next
      case Log show ?thesis
        apply(rule rule_case_dijs2)
        using Log True by(simp add: log)
      next
      case Reject show ?thesis
        apply(rule rule_case_dijs1)
        apply(rule_tac x="FinalDeny" in exI)
        using Reject True by(simp add: reject)
      next
      case (Call x5)
        have "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x5)], Undecided\<rangle> \<Rightarrow> t" by(rule case_call) (simp add: r Call)
        with Call pre True show ?thesis
        apply(simp)
        apply(elim exE, rename_tac t_called)
        apply(case_tac t_called)
         apply(simp)
         apply(rule disjI2)
         apply(rule_tac x="r#rs_called1" in exI)
         apply(rule_tac x=rs_called2 in exI)
         apply(rule_tac x=m' in exI)
         apply(simp add: r)
         apply(rule_tac t=Undecided in seq_cons)
          apply(simp add: r; fail)
         apply(simp; fail)
        apply(rule disjI1)
        apply(rule_tac x=t_called in exI)
        apply(rule_tac t=t_called in seq_cons)
         apply(simp add: r; fail)
        apply(simp add: decision; fail)
        done
      next
      case Empty show ?thesis
        apply(rule rule_case_dijs2)
        using Empty True by(simp add: pre empty)
      next
      case Return show ?thesis
       apply(rule disjI2)
       apply(rule_tac x="[]" in exI)
       apply(rule_tac x="rs_called1 @ Rule m' Return # rs_called2" in exI)
       apply(rule_tac x=m in exI)
       using Return True pre by(simp add: skip r)
      qed(simp_all add: a_not)
    qed
     
    from IH have **: "a \<noteq> Return \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> t) \<Longrightarrow> ?case"
    proof(elim disjE, goal_cases)
    case 2
      from this obtain rs_called1 m' rs_called2 where 
        a1: "rs = rs_called1 @ [Rule m' Return] @ rs_called2" and
        a2: "matches \<gamma> m' p" and a3: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided" by blast
      show ?case
        apply(rule *)
        using a1 a2 a3 by simp
    next
    case 1 thus ?case 
      proof(cases "a \<noteq> Return")
      case True
        with 1 obtain t1 t2 where t1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> t1"
                              and t2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t2" by blast
        from t1 t2 show ?thesis
        apply -
        apply(rule disjI1)
        apply(simp add: r)
        apply(cases t1)
         apply(simp_all)
         apply(rule_tac x=t2 in exI)
         apply(rule_tac seq'_cons)
          apply(simp_all)
        apply (meson decision seq_cons)
        done
      next
      case False show ?thesis
        proof(cases "matches \<gamma> m p")
          assume "\<not> matches \<gamma> m p" with 1 show ?thesis
            apply -
            apply(rule disjI1)
            apply(elim exE)
            apply(rename_tac t')
            apply(rule_tac x=t' in exI)
            apply(rule_tac t=Undecided in seq_cons)
             apply(simp add: r nomatch; fail)
            by(simp)
        next
          assume "matches \<gamma> m p" with False show ?thesis
            apply -
            apply(rule disjI2)
            apply(rule_tac x="[]" in exI)
            apply(rule_tac x=rs in exI)
            apply(rule_tac x=m in exI)
            apply(simp add: r skip; fail)
            done
        qed
      qed
    qed
    thus ?case using ex_neq_ret by blast
  qed
  
  
  lemma helper_defined_single: 
    assumes "wf (called_by_chain \<Gamma>)" 
    and "\<forall>rsg \<in> ran \<Gamma> \<union> {[Rule m a]}. wf_chain \<Gamma> rsg"
    and "\<forall>rsg \<in> ran \<Gamma> \<union> {[Rule m a]}. \<forall> r \<in> set rsg. (\<not>(\<exists>chain. get_action r = Goto chain)) \<and> get_action r \<noteq> Unknown"
    and "a \<noteq> Return" (*no toplevel Return*)
    shows "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t"
  proof(cases s)
  case (Decision decision) thus ?thesis
    apply(rule_tac x="Decision decision" in exI)
    apply(simp)
    using iptables_bigstep.decision by fast
  next
  case Undecided
    have "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> t"
    proof(cases "matches \<gamma> m p")
    case False with assms show ?thesis
      apply(rule_tac x=Undecided in exI)
      apply(rule_tac t=Undecided in seq'_cons)
       apply (metis empty_iff empty_set insert_iff list.simps(15) nomatch' rule.sel(1)) 
      apply(simp add: skip; fail)
      done
    next
    case True
    show ?thesis
      proof(cases a)
      case Unknown with assms(3) show ?thesis by simp
      next
      case Goto with assms(3) show ?thesis by auto
      next
      case Accept with True show ?thesis by(auto intro: iptables_bigstep.intros)
      next
      case Drop with True show ?thesis by(auto intro: iptables_bigstep.intros)
      next
      case Reject with True show ?thesis by(auto intro: iptables_bigstep.intros)
      next
      case Log with True show ?thesis by(auto intro: iptables_bigstep.intros)
      next
      case Empty with True show ?thesis by(auto intro: iptables_bigstep.intros)
      next
      case Return with assms show ?thesis by simp
      next
      case (Call chain_name)
        thm wf_induct_rule[where r="(calls_chain \<Gamma>)" and P="\<lambda>x. \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x)], Undecided\<rangle> \<Rightarrow> t"]
        --\<open>Only the assumptions we will need\<close>
        from assms have "wf (called_by_chain \<Gamma>)"
            "\<forall>rsg\<in>ran \<Gamma>. wf_chain \<Gamma> rsg"
            "\<forall>rsg\<in>ran \<Gamma>. \<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown" by auto
        --\<open>strengthening the IH to do a well-founded induction\<close>
        hence "matches \<gamma> m p \<Longrightarrow> wf_chain \<Gamma> [Rule m (Call chain_name)] \<Longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain_name)], Undecided\<rangle> \<Rightarrow> t)"
        proof(induction arbitrary: m rule: wf_induct_rule[where r="called_by_chain \<Gamma>"])
        case (less chain_name_neu)
          thm less.prems
          from less.prems have "\<Gamma> chain_name_neu \<noteq> None" by(simp add: wf_chain_def)
          from this obtain rs_called where rs_called: "\<Gamma> chain_name_neu = Some rs_called" by blast
  
          from less rs_called have "wf_chain \<Gamma> rs_called" by (simp add: ranI)
          from less rs_called have "rs_called \<in> ran \<Gamma>" by (simp add: ranI)
  
          (*get good IH*)
          from less.prems rs_called have
            "\<forall>y m. \<forall>r \<in> set rs_called. r = Rule m (Call y) \<longrightarrow> (y, chain_name_neu) \<in> called_by_chain \<Gamma> \<and> wf_chain \<Gamma> [Rule m (Call y)]"
             apply(simp)
             apply(intro impI allI conjI)
              apply(simp add: called_by_chain_def)
              apply blast
             apply(simp add: wf_chain_def)
             apply (meson ranI rule.sel(2))
             done
          with less have "\<forall>y m. \<forall>r\<in>set rs_called. r = Rule m (Call y) \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], Undecided\<rangle> \<Rightarrow> t)"
             apply(intro allI, rename_tac y my)
             apply(case_tac "matches \<gamma> my p")
              apply blast
             apply(intro ballI impI)
             apply(rule_tac x=Undecided in exI)
             apply(simp add: nomatch; fail)
             done
          from less.prems(4) rs_called \<open>rs_called \<in> ran \<Gamma>\<close>
            helper_cases_call_subchain_defined_or_return[OF less.prems(3) less.prems(4) this \<open>wf_chain \<Gamma> rs_called\<close>] have
            "(\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called, Undecided\<rangle> \<Rightarrow> t) \<or>
             (\<exists>rs_called1 rs_called2 m'.
                  \<Gamma> chain_name_neu = Some (rs_called1@[Rule m' Return]@rs_called2) \<and>
                  matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided)" by simp
          thus ?case
          proof(elim disjE exE conjE)
            fix t
            assume a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called, Undecided\<rangle> \<Rightarrow> t" show ?case
            using call_result[OF less.prems(1) rs_called a] by(blast)
          next
            fix m' rs_called1 rs_called2
            assume a1: "\<Gamma> chain_name_neu = Some (rs_called1 @ [Rule m' Return] @ rs_called2)"
            and a2: "matches \<gamma> m' p" and a3: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided"
            show ?case using call_return[OF less.prems(1) a1 a2 a3 ] by(blast)
          qed
        qed
        with True assms Call show ?thesis by simp
      qed
    qed
  with Undecided show ?thesis by simp
  qed
  
  
  private lemma helper_defined_ruleset_calledby: "wf (called_by_chain \<Gamma>) \<Longrightarrow> 
    \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow>
    \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. \<forall> r \<in> set rsg. (\<not>(\<exists>chain. get_action r = Goto chain)) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
    \<forall> r \<in> set rs. get_action r \<noteq> Return \<Longrightarrow>
    \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  apply(rule iptables_bigstep_defined_if_singleton_rules)
  apply(intro ballI, rename_tac r, case_tac r, rename_tac m a, simp)
  apply(rule helper_defined_single)
     apply(simp; fail)
    apply(simp add: wf_chain_def; fail)
   apply fastforce
  apply fastforce
  done
  
  corollary semantics_bigstep_defined: "finite (calls_chain \<Gamma>) \<Longrightarrow> wf (calls_chain \<Gamma>) \<Longrightarrow> (*call relation finite and terminating*)
    \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow> (*All calls to defined chains*)
    \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. \<forall> r \<in> set rsg. (\<forall>x. get_action r \<noteq> Goto x) \<and> get_action r \<noteq> Unknown \<Longrightarrow> (*no bad actions*)
    \<forall> r \<in> set rs. get_action r \<noteq> Return (*no toplevel return*) \<Longrightarrow>
    \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  apply(drule(1) wf_called_by_chain)
  apply(thin_tac "wf (calls_chain \<Gamma>)")
  apply(rule helper_defined_ruleset_calledby)
     apply(simp_all)
  done
end









text\<open>Common Algorithms\<close>

lemma iptables_bigstep_rm_LogEmpty: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rm_LogEmpty rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof(induction rs arbitrary: s)
case Nil thus ?case by(simp)
next
case (Cons r rs)
  have step_IH: "(\<And>s. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs2, s\<rangle> \<Rightarrow> t) \<Longrightarrow>
         \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs2, s\<rangle> \<Rightarrow> t" for rs1 rs2 r
  by (meson seq'_cons seqE_cons)
  have case_log: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Log # rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" for m
    apply(rule iffI)
     apply(erule seqE_cons)
     apply (metis append_Nil log_remove seq')
    apply(rule_tac t=s in seq'_cons)
     apply(cases s)
      apply(cases "matches \<gamma> m p")
       apply(simp add: log; fail)
      apply(simp add: nomatch; fail)
     apply(simp add: decision; fail)
    apply simp
   done
  have case_empty: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Empty # rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" for m
    apply(rule iffI)
     apply(erule seqE_cons)
     apply (metis append_Nil empty_empty seq')
    apply(rule_tac t=s in seq'_cons)
     apply(cases s)
      apply(cases "matches \<gamma> m p")
       apply(simp add: empty; fail)
      apply(simp add: nomatch; fail)
     apply(simp add: decision; fail)
    apply simp
   done

  from Cons show ?case  
  apply(cases r, rename_tac m a)
  apply(case_tac a)
          apply(simp_all)
          apply(simp_all cong: step_IH)
   apply(simp_all add: case_log case_empty)
  done
qed

lemma iptables_bigstep_rw_Reject: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rw_Reject rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof(induction rs arbitrary: s)
case Nil thus ?case by(simp)
next
case (Cons r rs)
  have step_IH: "(\<And>s. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs2, s\<rangle> \<Rightarrow> t) \<Longrightarrow>
         \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>r#rs2, s\<rangle> \<Rightarrow> t" for rs1 rs2 r
  by (meson seq'_cons seqE_cons)
  have fst_rule: "(\<And>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[r1], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[r2], s\<rangle> \<Rightarrow> t) \<Longrightarrow> 
    \<Gamma>,\<gamma>,p\<turnstile> \<langle>r1 # rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>r2 # rs, s\<rangle> \<Rightarrow> t" for r1 r2 rs s t
  by (meson seq'_cons seqE_cons)
  have dropreject: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Drop], s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Reject], s\<rangle> \<Rightarrow> t" for m t
    apply(cases s)
     apply(cases "matches \<gamma> m p")
      using drop reject dropD rejectD apply fast
     using nomatch nomatchD apply fast
    using decision decisionD apply fast
    done

  from Cons show ?case
  apply(cases r, rename_tac m a)
  apply simp
  apply(case_tac a)
          apply(simp_all)
          apply(simp_all cong: step_IH)
   apply(rule fst_rule)
   apply(simp add: dropreject)
  done
qed



end
