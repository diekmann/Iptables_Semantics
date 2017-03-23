theory Alternative_Semantics
imports Semantics
begin
  
(* the first thing (I think) we have to do is alter the Seq rule / merge it with NoMatch.
 Its properties make it hard to work with\<dots> *)
inductive iptables_bigstep_ns :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_,_,_\<turnstile> \<langle>_, _\<rangle> \<Rightarrow>\<^sub>s _"  [60,60,60,20,98,98] 89)
  for \<Gamma> and \<gamma> and p where
skip:    "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[], t\<rangle> \<Rightarrow>\<^sub>s t" |
accept:  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Accept # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision FinalAllow" |
drop:    "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Drop # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision FinalDeny" |
reject:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Reject # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision FinalDeny" |
log:     "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Log # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t" |
empty:   "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m Empty # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t" |
nms:     "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m a # rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t" |
(*decision: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Decision X\<rangle> \<Rightarrow>\<^sub>s Decision X" |*)
call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1 @ Rule m' Return # rs\<^sub>2);
                 matches \<gamma> m' p; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow>\<^sub>s Undecided; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rrs, Undecided\<rangle> \<Rightarrow>\<^sub>s t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Call chain) # rrs, Undecided\<rangle> \<Rightarrow>\<^sub>s t" |
call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision X \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Call chain) # rrs, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision X" |
call_no_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s Undecided;
                    \<Gamma>,\<gamma>,p\<turnstile> \<langle>rrs, Undecided\<rangle> \<Rightarrow>\<^sub>s t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m (Call chain) # rrs, Undecided\<rangle> \<Rightarrow>\<^sub>s t"

lemma a: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>s t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  apply(induction rule: iptables_bigstep_ns.induct; (simp add: iptables_bigstep.intros;fail)?)
  apply (meson iptables_bigstep.decision iptables_bigstep.accept seq_cons)
  apply (meson iptables_bigstep.decision iptables_bigstep.drop seq_cons)
  apply (meson iptables_bigstep.decision iptables_bigstep.reject seq_cons)
  apply (meson iptables_bigstep.log seq_cons)
  apply (meson iptables_bigstep.empty seq_cons)
  apply (meson nomatch seq_cons)
  subgoal using iptables_bigstep.call_return seq_cons by fastforce
  apply (meson iptables_bigstep.decision iptables_bigstep.call_result seq_cons)
  apply (meson iptables_bigstep.call_result seq'_cons)
  done

lemma empty_rs_stateD: assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[], s\<rangle> \<Rightarrow>\<^sub>s t" shows "t = s"
  using assms by(cases rule: iptables_bigstep_ns.cases)
lemma decided: "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision X\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow>\<^sub>s Decision X"
proof(induction rs\<^sub>1)
  case Nil
  then show ?case by (fast dest: empty_rs_stateD)
next
  case (Cons a rs\<^sub>1)
  from Cons.prems show ?case 
    by(cases rule: iptables_bigstep_ns.cases; simp add: Cons.IH iptables_bigstep_ns.intros)
qed
  
lemma decided_determ: "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, s\<rangle> \<Rightarrow>\<^sub>s t; s = Decision X\<rbrakk> \<Longrightarrow> t = Decision X"
  by(induction rule: iptables_bigstep_ns.induct; (simp add: iptables_bigstep_ns.intros;fail)?)

lemma seq_ns:
  "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow>\<^sub>s t; \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow>\<^sub>s t'\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow>\<^sub>s t'"
proof (cases t, goal_cases)
  case 1
  from 1(1,2) show ?case unfolding 1 proof(induction rs\<^sub>1)
    case (Cons a rs\<^sub>3)
    then show ?case
      apply -
      apply(rule iptables_bigstep_ns.cases[OF Cons.prems(1)]; simp add: iptables_bigstep_ns.intros)
    done
  qed simp
next
  case (2 X)
  hence "t' = Decision X" by (simp add: decided_determ)
  from 2(1) show ?case by (simp add: "2"(3) \<open>t' = Decision X\<close> decided)
qed
      
lemma b: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> s = Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>s t"
  apply(induction rule: iptables_bigstep.induct; (simp add: iptables_bigstep_ns.intros;fail)?)
   apply (metis decided decision seq_ns seq_progress skipD state.exhaust)
  apply(metis call_no_result iptables_bigstep_ns.call_result iptables_bigstep_ns.skip state.exhaust)
  done
    
inductive iptables_bigstep_nz :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> bool"
  ("_,_,_\<turnstile> _ \<Rightarrow>\<^sub>z _"  [60,60,60,20,98] 89)
  for \<Gamma> and \<gamma> and p where
skip:    "\<Gamma>,\<gamma>,p \<turnstile> []  \<Rightarrow>\<^sub>z Undecided" |
accept:  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Accept # rs \<Rightarrow>\<^sub>z Decision FinalAllow" |
drop:    "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Drop # rs \<Rightarrow>\<^sub>z Decision FinalDeny" |
reject:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> Rule m Reject # rs \<Rightarrow>\<^sub>z Decision FinalDeny" |
log:     "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Log # rs \<Rightarrow>\<^sub>z t" |
empty:   "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Empty # rs \<Rightarrow>\<^sub>z t" |
nms:     "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m a # rs \<Rightarrow>\<^sub>z t" |
call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1 @ Rule m' Return # rs\<^sub>2);
                 matches \<gamma> m' p; \<Gamma>,\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided; \<Gamma>,\<gamma>,p\<turnstile> rrs \<Rightarrow>\<^sub>z t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call chain) # rrs \<Rightarrow>\<^sub>z t" |
call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z Decision X \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call chain) # rrs \<Rightarrow>\<^sub>z Decision X" |
call_no_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z Undecided;
                    \<Gamma>,\<gamma>,p\<turnstile> rrs \<Rightarrow>\<^sub>z t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call chain) # rrs \<Rightarrow>\<^sub>z t"

lemma c: "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>s t"
  by(induction rule: iptables_bigstep_nz.induct; simp add: iptables_bigstep_ns.intros)
    
lemma d: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>s t \<Longrightarrow> s = Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t"
  by(induction rule: iptables_bigstep_ns.induct; simp add: iptables_bigstep_nz.intros)
    
inductive iptables_bigstep_r :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> bool"
  ("_,_,_\<turnstile> _ \<Rightarrow>\<^sub>r _"  [60,60,60,20,98] 89)
  for \<Gamma> and \<gamma> and p where
skip:    "\<Gamma>,\<gamma>,p \<turnstile> []  \<Rightarrow>\<^sub>r Undecided" |
accept:  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Accept # rs \<Rightarrow>\<^sub>r Decision FinalAllow" |
drop:    "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Drop # rs \<Rightarrow>\<^sub>r Decision FinalDeny" |
reject:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> Rule m Reject # rs \<Rightarrow>\<^sub>r Decision FinalDeny" |
return:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> Rule m Return # rs \<Rightarrow>\<^sub>r Undecided" |
log:     "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Log # rs \<Rightarrow>\<^sub>r t" |
empty:   "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Empty # rs \<Rightarrow>\<^sub>r t" |
nms:     "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m a # rs \<Rightarrow>\<^sub>r t" |
call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r Decision X \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call chain) # rrs \<Rightarrow>\<^sub>r Decision X" |
call_no_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r Undecided;
                    \<Gamma>,\<gamma>,p\<turnstile> rrs \<Rightarrow>\<^sub>r t \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call chain) # rrs \<Rightarrow>\<^sub>r t"

lemma "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<Longrightarrow> s = Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t"
  apply(induction rule: iptables_bigstep_r.induct; (simp add: iptables_bigstep_nz.intros)?)
  oops

lemma returning:  "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>r Undecided; matches \<gamma> m' p\<rbrakk>
    \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs\<^sub>1 @ Rule m' Return # rs\<^sub>2 \<Rightarrow>\<^sub>r Undecided"
proof(induction rs\<^sub>1)
  case Nil
  then show ?case by (simp add: return)
next
  case (Cons a rs\<^sub>3)
  then show ?case by - (rule iptables_bigstep_r.cases[OF Cons.prems(1)]; simp add: iptables_bigstep_r.intros)
qed
 
lemma e: "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> s = Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t"
  by(induction rule: iptables_bigstep_nz.induct; simp add: iptables_bigstep_r.intros returning)
    

definition "no_call_to c rs \<equiv> (\<forall>r \<in> set rs. case get_action r of Call c' \<Rightarrow> c \<noteq> c' | _ \<Rightarrow> True)"
definition "all_chains p \<Gamma> rs \<equiv> (p rs \<and> (\<forall>l rs. \<Gamma> l = Some rs \<longrightarrow> p rs))"
lemma all_chains_no_call_upd: "all_chains (no_call_to c) \<Gamma> rs \<Longrightarrow> (\<Gamma>(c \<mapsto> x)),\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t"
proof (rule iffI, goal_cases)
  case 1
  from 1(2,1) show ?case 
    by(induction rule: iptables_bigstep_nz.induct; 
      (simp add: iptables_bigstep_nz.intros no_call_to_def all_chains_def split: if_splits;fail)?)
next
  case 2
  from 2(2,1) show ?case 
    by(induction rule: iptables_bigstep_nz.induct; 
      (simp add: iptables_bigstep_nz.intros no_call_to_def all_chains_def split:  action.splits;fail)?)
qed

lemma updated_call: "\<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> \<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z t"
  by(cases t; simp add: iptables_bigstep_nz.call_no_result iptables_bigstep_nz.call_result iptables_bigstep_nz.skip)
    
lemma shows
      log_nz:     "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Log # rs \<Rightarrow>\<^sub>z t"
and empty_nz:   "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> Rule m Empty # rs \<Rightarrow>\<^sub>z t"
  by (meson iptables_bigstep_nz.log iptables_bigstep_nz.empty iptables_bigstep_nz.nms)+
    
lemma nz_empty_rs_stateD: assumes "\<Gamma>,\<gamma>,p\<turnstile> [] \<Rightarrow>\<^sub>z t" shows "t = Undecided"
  using assms by(cases rule: iptables_bigstep_nz.cases)
    
lemma upd_callD: "\<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z t \<Longrightarrow> matches \<gamma> m p 
  \<Longrightarrow> (\<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>z t \<or> (\<exists>rs\<^sub>1 rs\<^sub>2 m'. rs = rs\<^sub>1 @ Rule m' Return # rs\<^sub>2 \<and> matches \<gamma> m' p \<and> \<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided \<and> t = Undecided))"
  by(subst (asm) iptables_bigstep_nz.simps) (auto dest!: nz_empty_rs_stateD)
    
lemma partial_fun_upd: "(f(x \<mapsto> y)) x = Some y" by(fact fun_upd_same)
 
lemma f: "\<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> all_chains (no_call_to c) \<Gamma> rs \<Longrightarrow> 
  (\<Gamma>(c \<mapsto> rs)),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z t"
proof(induction rule: iptables_bigstep_r.induct; (simp add: iptables_bigstep_nz.intros;fail)?)
  case (return m rs)
  then show ?case by (metis append_Nil fun_upd_same iptables_bigstep_nz.call_return iptables_bigstep_nz.skip)
next
  case (log rs t mx)
  have ac: "all_chains (no_call_to c) \<Gamma> rs"
    using log(4) by(simp add: all_chains_def no_call_to_def)
  have *: "\<Gamma>(c \<mapsto> Rule mx Log # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z Undecided"
    if "rs = rs\<^sub>1 @ Rule m' Return # rs\<^sub>2" "matches \<gamma> m' p" 
       "\<Gamma>(c \<mapsto> rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
    for rs\<^sub>1 rs\<^sub>2 m'
  proof -
    have ac2: "all_chains (no_call_to c) \<Gamma> rs\<^sub>1" using log(4) that
      by(simp add: all_chains_def no_call_to_def)
    hence "\<Gamma>(c \<mapsto> Rule mx Log # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
      using that(3) unfolding that by(simp add: all_chains_no_call_upd)
        hence "\<Gamma>(c \<mapsto> Rule mx Log # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> Rule mx Log # rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
      by (simp add: log_nz)
    thus ?thesis using that(1,2)
      by(elim iptables_bigstep_nz.call_return[where rs\<^sub>2=rs\<^sub>2, OF \<open>matches \<gamma> m p\<close>, rotated]; simp add: iptables_bigstep_nz.skip)
  qed
  from log(2)[OF log(3) ac] show ?case
    apply -
    apply(drule upd_callD[OF _ \<open>matches \<gamma> m p\<close>])
    apply(erule disjE)
    subgoal
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule log_nz)
      apply(simp add: ac all_chains_no_call_upd)
      done
    using * by blast
next
  case (empty rs t mx) text\<open>analogous\<close> (*<*)
  have ac: "all_chains (no_call_to c) \<Gamma> rs"
    using empty(4) by(simp add: all_chains_def no_call_to_def)
  have *: "\<Gamma>(c \<mapsto> Rule mx Empty # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z Undecided"
    if "rs = rs\<^sub>1 @ Rule m' Return # rs\<^sub>2" "matches \<gamma> m' p" 
       "\<Gamma>(c \<mapsto> rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
    for rs\<^sub>1 rs\<^sub>2 m'
  proof -
    have ac2: "all_chains (no_call_to c) \<Gamma> rs\<^sub>1" using empty(4) that
      by(simp add: all_chains_def no_call_to_def)
    hence "\<Gamma>(c \<mapsto> Rule mx Empty # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
      using that(3) unfolding that by(simp add: all_chains_no_call_upd)
        hence "\<Gamma>(c \<mapsto> Rule mx Empty # rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> Rule mx Empty # rs\<^sub>1 \<Rightarrow>\<^sub>z Undecided"
      by (simp add: empty_nz)
    thus ?thesis using that(1,2)
      by(elim iptables_bigstep_nz.call_return[where rs\<^sub>2=rs\<^sub>2, OF \<open>matches \<gamma> m p\<close>, rotated]; simp add: iptables_bigstep_nz.skip)
  qed
  from empty(2)[OF empty(3) ac] show ?case
    apply -
    apply(drule upd_callD[OF _ \<open>matches \<gamma> m p\<close>])
    apply(erule disjE)
    subgoal
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule empty_nz)
      apply(simp add: ac all_chains_no_call_upd)
      done
    using * by blast
    (*>*)
next
  case (nms m' rs t a)
  have ac: "all_chains (no_call_to c) \<Gamma> rs" using nms(5) by(simp add: all_chains_def no_call_to_def)
  from nms.IH[OF nms(4) ac] show ?case
    apply -
    apply(drule upd_callD[OF _ \<open>matches \<gamma> m p\<close>])
    apply(erule disjE)
    subgoal
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule iptables_bigstep_nz.nms[OF \<open>\<not> matches \<gamma> m' p\<close>])
      apply(simp add: ac all_chains_no_call_upd)
      done
    apply safe
    subgoal for rs\<^sub>1 rs\<^sub>2 r
      apply(subgoal_tac "all_chains (no_call_to c) \<Gamma> rs\<^sub>1") (* Ich kann auch anders. *)
       apply(subst (asm) all_chains_no_call_upd, assumption)
       apply(subst (asm) all_chains_no_call_upd[symmetric], assumption)
       apply(drule iptables_bigstep_nz.nms[where a=a, OF \<open>\<not> matches \<gamma> m' p\<close>])
       apply(erule (1) iptables_bigstep_nz.call_return[where rs\<^sub>2=rs\<^sub>2, OF \<open>matches \<gamma> m p\<close>, rotated])
        apply(insert ac; simp add: all_chains_def no_call_to_def iptables_bigstep_nz.skip)+
      done
    done
next
  case (call_result m' c' rs X rrs)
  have acrs: "all_chains (no_call_to c) \<Gamma> rs" using call_result(2,6) by(simp add: all_chains_def no_call_to_def)
  have cc: "c \<noteq> c'" (* okay, this one is a bit nifty\<dots> *) using call_result(6) by(simp add: all_chains_def no_call_to_def)
  have "\<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z Decision X" using call_result.IH call_result.prems(1) acrs by blast
  then show ?case
    apply -
    apply(drule upd_callD[OF _ \<open>matches \<gamma> m p\<close>])
    apply(erule disjE)
    subgoal
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule iptables_bigstep_nz.call_result[where rs=rs, OF \<open>matches \<gamma> m' p\<close> ])
      apply(simp add: cc[symmetric] call_result(2);fail)
      apply(simp add: acrs all_chains_no_call_upd;fail)
      done
    apply safe (* oh. Didn't expect that. :) *)
  done
next
  case (call_no_result m' c' rs rrs t)
  have acrs: "all_chains (no_call_to c) \<Gamma> rs" using call_no_result(2,8) by(simp add: all_chains_def no_call_to_def)
  have acrrs: "all_chains (no_call_to c) \<Gamma> rrs" using call_no_result(2,8) by(simp add: all_chains_def no_call_to_def)
  have acrs1: "all_chains (no_call_to c) \<Gamma> rs\<^sub>1" if "rs = rs\<^sub>1 @ rs\<^sub>2" for rs\<^sub>1 rs\<^sub>2
    using acrs that by(simp add: all_chains_def no_call_to_def)
  have acrrs1: "all_chains (no_call_to c) \<Gamma> rs\<^sub>1" if "rrs = rs\<^sub>1 @ rs\<^sub>2" for rs\<^sub>1 rs\<^sub>2
    using acrrs that by(simp add: all_chains_def no_call_to_def)
  have cc: "c \<noteq> c'" (* okay, this one is a bit nifty\<dots> *) using call_no_result(8) by(simp add: all_chains_def no_call_to_def)
  have "\<Gamma>(c \<mapsto> rs),\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>z Undecided" using call_no_result.IH call_no_result.prems(1) acrs by blast
  with call_no_result(6)[OF \<open>matches \<gamma> m p\<close> acrrs] show ?case
    apply -
    apply(drule upd_callD[OF _ \<open>matches \<gamma> m p\<close>])+
    apply(elim disjE) (* 4 sg *)
    apply safe
    subgoal
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule iptables_bigstep_nz.call_no_result[where rs=rs, OF \<open>matches \<gamma> m' p\<close> ])
      apply(simp add: cc[symmetric] call_no_result(2);fail)
       apply(simp add: acrs all_chains_no_call_upd;fail)
      apply(simp add: acrrs all_chains_no_call_upd)
      done
    subgoal for rs\<^sub>1 rs\<^sub>2 r
      apply(rule updated_call[OF _ \<open>matches \<gamma> m p\<close>])
      apply(rule call_return[OF \<open>matches \<gamma> m' p\<close>])
         apply(simp add: cc[symmetric] call_no_result(2);fail)
        apply(simp;fail)
       apply(simp add: acrs1 all_chains_no_call_upd;fail)
      apply(simp add: acrrs all_chains_no_call_upd)
      done
    subgoal for rs\<^sub>1 rs\<^sub>2 r
      apply(rule call_return[where rs\<^sub>1="Rule m' (Call c') # rs\<^sub>1", OF \<open>matches \<gamma> m p\<close>])
         apply(simp;fail)
        apply(simp;fail)
      apply(rule iptables_bigstep_nz.call_no_result[OF \<open>matches \<gamma> m' p\<close>])
         apply(simp add: cc[symmetric] call_no_result(2);fail)
        apply (meson acrs all_chains_no_call_upd)
       apply(subst all_chains_no_call_upd; simp add: acrrs1 all_chains_no_call_upd; fail)
      apply (simp add: iptables_bigstep_nz.skip;fail)
      done
    subgoal for rrs\<^sub>1 rs\<^sub>1 rrs\<^sub>2 rs\<^sub>2 rr r
       apply(rule call_return[where rs\<^sub>1="Rule m' (Call c') # rrs\<^sub>1", OF \<open>matches \<gamma> m p\<close>])
         apply(simp;fail)
        apply(simp;fail)
       apply(rule call_return[OF \<open>matches \<gamma> m' p\<close>])
          apply(simp add: cc[symmetric] call_no_result(2);fail)
         apply blast
        apply (meson acrs1 all_chains_no_call_upd)
       apply(subst all_chains_no_call_upd; simp add: acrrs1 all_chains_no_call_upd; fail)
      apply (simp add: iptables_bigstep_nz.skip;fail)
      done
    done
qed
  
lemma r_skip_inv: "\<Gamma>,\<gamma>,p\<turnstile> [] \<Rightarrow>\<^sub>r t \<Longrightarrow> t = Undecided"
  by(subst (asm) iptables_bigstep_r.simps) auto
  
(* why did I do all this? essentially, because I thought this should be derivable: *)
lemma r_call_eq: "\<Gamma> c = Some rs \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> [Rule m (Call c)] \<Rightarrow>\<^sub>r t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t"
(* and yes, there is a more general form of this lemma, but\<dots> meh. *)
  apply(rule iffI)
  subgoal
    apply(subst (asm) iptables_bigstep_r.simps)
    apply(auto dest: r_skip_inv)
  done
  subgoal
    apply(cases t)
     apply(erule (1) iptables_bigstep_r.call_no_result)
      apply(simp;fail)
     apply(simp add: iptables_bigstep_r.skip;fail)
      apply(simp)
    apply(erule (2) iptables_bigstep_r.call_result)
  done
by -
  
theorem r_eq_orig: "\<lbrakk>all_chains (no_call_to c) \<Gamma> rs; \<Gamma> c = Some rs\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call c)], Undecided\<rangle> \<Rightarrow> t"
  apply(rule iffI)
  subgoal
    apply(drule f[where m=MatchAny, THEN c, THEN a])
      apply(simp;fail)
     apply(simp;fail)
    apply (metis fun_upd_triv)
    done  
  subgoal
    apply(subst r_call_eq[where m=MatchAny, symmetric])
      apply(simp;fail)
     apply(simp;fail)
    apply(erule b[THEN d, THEN e, OF _ refl refl refl])
    done
  done

corollary r_eq_orig': "\<lbrakk>all_chains (no_call_to c) \<Gamma> rs; \<Gamma> c = Some rs\<rbrakk> \<Longrightarrow> 
  \<Gamma>,\<gamma>,p\<turnstile> [Rule MatchAny (Call c)] \<Rightarrow>\<^sub>r t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call c)], Undecided\<rangle> \<Rightarrow> t"
(* if you really like symmetry *)
  by(simp add: r_call_eq r_eq_orig)

end