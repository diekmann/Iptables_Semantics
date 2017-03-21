theory Semantics_Goto
imports Main Firewall_Common "Common/List_Misc" "~~/src/HOL/Library/LaTeXsugar"
begin

section\<open>Big Step Semantics with Goto\<close>
text\<open>
  We extend the iptables semantics to support the goto action.
  A goto directly continues processing at the start of the called chain.
  It does not change the call stack.
  In contrast to calls, goto does not return.
  Consequently, everything behind a matching goto cannot be reached.
\<close>
text\<open>
  This theory is structured as follows.
  Fist, the goto semantics are introduced.
  Then, we show that those semantics are deterministic.
  Finally, we present two methods to remove gotos.
   The first unfolds goto.
   The second replaces gotos with calls.
  Finally, since the goto rules makes all proofs quite ugly, we never mention the goto semantics again.
  As we have shown, we can get rid of the gotos easily, thus, we stick to the nicer iptables semantics without goto.
\<close>

context
begin
  
  subsection\<open>Semantics\<close>
    private type_synonym 'a ruleset = "string \<rightharpoonup> 'a rule list"
    
    private type_synonym ('a, 'p) matcher = "'a \<Rightarrow> 'p \<Rightarrow> bool"
    
    qualified fun matches :: "('a, 'p) matcher \<Rightarrow> 'a match_expr \<Rightarrow> 'p \<Rightarrow> bool" where
      "matches \<gamma> (MatchAnd e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<and> matches \<gamma> e2 p" |
      "matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" |
      "matches \<gamma> (Match e) p \<longleftrightarrow> \<gamma> e p" |
      "matches _ MatchAny _ \<longleftrightarrow> True"
    
    
    (*
    main:
      call foo
      deny-all
    foo:
      goto bar
    bar:
      [nothing]
    
    The call returns, even if a goto is executed in the called chains. The deny-all will be executed!
    
    Chain OUTPUT (policy ACCEPT 98 packets, 34936 bytes)
     pkts bytes target     prot opt in     out     source               destination         
        1    84            all  --  *      *       0.0.0.0/0            127.42.0.1          
        1    84 foo        all  --  *      *       0.0.0.0/0            127.42.0.1          
        1    84            all  --  *      *       0.0.0.0/0            127.42.0.1          
    
    Chain bar (1 references)
     pkts bytes target     prot opt in     out     source               destination         
    
    Chain foo (1 references)
     pkts bytes target     prot opt in     out     source               destination         
        1    84 bar        all  --  *      *       0.0.0.0/0            0.0.0.0/0           [goto] 
    
    *)
    qualified fun no_matching_Goto :: "('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> bool" where
      "no_matching_Goto _ _ [] \<longleftrightarrow> True" |
      "no_matching_Goto \<gamma> p ((Rule m (Goto _))#rs) \<longleftrightarrow> \<not> matches \<gamma> m p \<and> no_matching_Goto \<gamma> p rs" |
      "no_matching_Goto \<gamma> p (_#rs) \<longleftrightarrow> no_matching_Goto \<gamma> p rs"
    
    inductive iptables_goto_bigstep :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a rule list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
      ("_,_,_\<turnstile>\<^sub>g \<langle>_, _\<rangle> \<Rightarrow> _"  [60,60,60,20,98,98] 89)
      for \<Gamma> and \<gamma> and p where
    skip:    "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], t\<rangle> \<Rightarrow> t" |
    accept:  "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Accept], Undecided\<rangle> \<Rightarrow> Decision FinalAllow" |
    drop:    "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Drop], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
    reject:  "matches \<gamma> m p \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Reject], Undecided\<rangle> \<Rightarrow> Decision FinalDeny" |
    log:     "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Log], Undecided\<rangle> \<Rightarrow> Undecided" |
    empty:   "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Empty], Undecided\<rangle> \<Rightarrow> Undecided" |
    nomatch: "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided" |
    decision: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Decision X\<rangle> \<Rightarrow> Decision X" |
    seq:      "\<lbrakk>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t; \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t'; no_matching_Goto \<gamma> p rs\<^sub>1\<rbrakk> \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1@rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t'" |
    call_return:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some (rs\<^sub>1@[Rule m' Return]@rs\<^sub>2);
                     matches \<gamma> m' p; \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided;
                     no_matching_Goto \<gamma> p rs\<^sub>1\<rbrakk> \<Longrightarrow>
                     (*we do not support a goto in the first part if you want to return
                     probably unhandled case:
                     main:
                       call foo
                     foo:
                       goto bar
                     bar:
                       Return //returns to `call foo'
                     But this would be a really awkward ruleset!
                     *)
                   \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" |
    call_result:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<rbrakk> \<Longrightarrow>
                   \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t" | (*goto handling here seems okay*)
    goto_decision:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision X \<rbrakk> \<Longrightarrow>
                   \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> Decision X" |
    goto_no_decision:  "\<lbrakk> matches \<gamma> m p; \<Gamma> chain = Some rs; \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<rbrakk> \<Longrightarrow>
                   \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> Undecided"
    
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
    @{thm[mode=Rule] call_result [no_vars]}\\[1ex] 
    @{thm[mode=Rule] goto_decision [no_vars]}\\[1ex] 
    @{thm[mode=Rule] goto_no_decision [no_vars]}
    \end{center}
\<close>
    
    private lemma deny:
      "matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> iptables_goto_bigstep \<Gamma> \<gamma> p [Rule m a] Undecided (Decision FinalDeny)"
    by (auto intro: drop reject)
    
    
    private lemma iptables_goto_bigstep_induct
      [case_names
        Skip Allow Deny Log Nomatch Decision Seq Call_return Call_result Goto_Decision Goto_no_Decision,
       induct pred: iptables_goto_bigstep]:
    "\<lbrakk> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,s\<rangle> \<Rightarrow> t;
       \<And>t. P [] t t;
       \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Accept \<Longrightarrow> P [Rule m a] Undecided (Decision FinalAllow);
       \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Drop \<or> a = Reject \<Longrightarrow> P [Rule m a] Undecided (Decision FinalDeny);
       \<And>m a. matches \<gamma> m p \<Longrightarrow> a = Log \<or> a = Empty \<Longrightarrow> P [Rule m a] Undecided Undecided;
       \<And>m a. \<not> matches \<gamma> m p \<Longrightarrow> P [Rule m a] Undecided Undecided;
       \<And>rs X. P rs (Decision X) (Decision X);
       \<And>rs rs\<^sub>1 rs\<^sub>2 t t'. rs = rs\<^sub>1 @ rs\<^sub>2 \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs\<^sub>1 Undecided t \<Longrightarrow> 
                          \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t' \<Longrightarrow> P rs\<^sub>2 t t' \<Longrightarrow> no_matching_Goto \<gamma> p rs\<^sub>1 \<Longrightarrow> 
                          P rs Undecided t';
       \<And>m a chain rs\<^sub>1 m' rs\<^sub>2. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow>
                              \<Gamma> chain = Some (rs\<^sub>1 @ [Rule m' Return] @ rs\<^sub>2) \<Longrightarrow>
                              matches \<gamma> m' p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow>
                              no_matching_Goto \<gamma> p rs\<^sub>1 \<Longrightarrow>  P rs\<^sub>1 Undecided Undecided \<Longrightarrow>
                              P [Rule m a] Undecided Undecided;
       \<And>m a chain rs t. matches \<gamma> m p \<Longrightarrow> a = Call chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow>
                         \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> P rs Undecided t \<Longrightarrow> P [Rule m a] Undecided t;
       \<And>m a chain rs rest X. matches \<gamma> m p \<Longrightarrow> a = Goto chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow>
                              \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,Undecided\<rangle> \<Rightarrow> (Decision X) \<Longrightarrow> P rs Undecided (Decision X) \<Longrightarrow>
                              P (Rule m a#rest) Undecided (Decision X);
       \<And>m a chain rs rest. matches \<gamma> m p \<Longrightarrow> a = Goto chain \<Longrightarrow> \<Gamma> chain = Some rs \<Longrightarrow>
                           \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> P rs Undecided Undecided \<Longrightarrow>
                           P (Rule m a#rest) Undecided Undecided\<rbrakk> \<Longrightarrow>
     P rs s t"
    by (induction rule: iptables_goto_bigstep.induct) auto


  
  subsubsection\<open>Forward reasoning\<close>
  
    private lemma decisionD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> s = Decision X \<Longrightarrow> t = Decision X"
      by (induction rule: iptables_goto_bigstep_induct) auto
    
    private lemma iptables_goto_bigstep_to_undecided: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> Undecided \<Longrightarrow> s = Undecided"
      by (metis decisionD state.exhaust)
    
    private lemma iptables_goto_bigstep_to_decision: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Decision Y\<rangle> \<Rightarrow> Decision X \<Longrightarrow> Y = X"
      by (metis decisionD state.inject)
    
    
    private lemma skipD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [] \<Longrightarrow> s = t"
      by (induction rule: iptables_goto_bigstep.induct) auto
    
    
    private lemma gotoD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m (Goto chain)] \<Longrightarrow> s = Undecided \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>
                    \<exists> rs. \<Gamma> chain = Some rs \<and> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,s\<rangle> \<Rightarrow> t"
      by (induction rule: iptables_goto_bigstep.induct) (auto dest: skipD elim: list_app_singletonE)
    
    private lemma not_no_matching_Goto_singleton_cases: "\<not> no_matching_Goto \<gamma> p [Rule m a] \<longleftrightarrow> (\<exists> chain. a = (Goto chain)) \<and> matches \<gamma> m p"
      by(case_tac a) (simp_all)
    
    private lemma no_matching_Goto_Cons: "no_matching_Goto \<gamma> p [r] \<Longrightarrow> no_matching_Goto \<gamma> p rs \<Longrightarrow> no_matching_Goto \<gamma> p (r#rs)"
      by(cases r)(rename_tac m a, case_tac a, simp_all)
    
    private lemma no_matching_Goto_head: "no_matching_Goto \<gamma> p (r#rs) \<Longrightarrow> no_matching_Goto \<gamma> p [r]"
      by(cases r)(rename_tac m a, case_tac a, simp_all)
    private lemma no_matching_Goto_tail: "no_matching_Goto \<gamma> p (r#rs) \<Longrightarrow> no_matching_Goto \<gamma> p rs"
      by(cases r)(rename_tac m a, case_tac a, simp_all)
    
    private lemma not_no_matching_Goto_cases:
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
            with \<open>\<not> no_matching_Goto \<gamma> p (r # rs)\<close> Nil not_no_matching_Goto_singleton_cases have "(\<exists> chain. a = (Goto chain)) \<and> matches \<gamma> m p" by metis
            from this obtain chain where "a = (Goto chain)" and "matches \<gamma> m p" by blast
            have "r # rs = [] @ Rule m (Goto chain) # []" "no_matching_Goto \<gamma> p []" "matches \<gamma> m p"
              by (simp_all add: \<open>a = Goto chain\<close> \<open>r = Rule m a\<close> Nil \<open>matches \<gamma> m p\<close>)
            thus ?thesis by blast
          next
          case(Cons r' rs')
            with Cons_outer have "r # rs =  r # r' # rs'" by simp
            show ?thesis
            proof(cases"no_matching_Goto \<gamma> p [r]")
            case True 
              with \<open>\<not> no_matching_Goto \<gamma> p (r # rs)\<close> have "\<not> no_matching_Goto \<gamma> p rs" by (meson no_matching_Goto_Cons)
              have "rs \<noteq> []" using Cons by simp
              from Cons_outer(1)[OF \<open>\<not> no_matching_Goto \<gamma> p rs\<close> \<open>rs \<noteq> []\<close>]
                obtain rs1 m chain rs2 where "rs = rs1 @ Rule m (Goto chain) # rs2" "no_matching_Goto \<gamma> p rs1" "matches \<gamma> m p" by blast
              with \<open>r # rs =  r # r' # rs'\<close> \<open>no_matching_Goto \<gamma> p [r]\<close> no_matching_Goto_Cons
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
                by (simp_all add: \<open>a = Goto chain\<close> \<open>r = Rule m a\<close> \<open>matches \<gamma> m p\<close>)
              thus ?thesis by blast
            qed
          qed
        qed
    
    private lemma seq_cons_Goto_Undecided: 
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> Undecided"
      and "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m (Goto chain) # rs, Undecided\<rangle> \<Rightarrow> Undecided"
      proof(cases "matches \<gamma> m p")
        case True
          from True assms have "\<exists>rs. \<Gamma> chain = Some rs \<and> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided" by(auto dest: gotoD)
          with True show ?thesis using goto_no_decision by fast
      next
        case False
        with assms have " \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)] @ rs, Undecided\<rangle> \<Rightarrow> Undecided" by(auto dest: seq)
        with False show ?thesis by simp
      qed

    private lemma seq_cons_Goto_t: 
      "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m (Goto chain) # rs, Undecided\<rangle> \<Rightarrow> t"
       apply(frule gotoD)
          apply(simp_all)
       apply(clarify)
       apply(cases t)
        apply(auto intro: iptables_goto_bigstep.intros)
    done
    
    
    private lemma no_matching_Goto_append: "no_matching_Goto \<gamma> p (rs1@rs2) \<longleftrightarrow> no_matching_Goto \<gamma> p rs1 \<and>  no_matching_Goto \<gamma> p rs2"
      by(induction \<gamma> p rs1 rule: no_matching_Goto.induct) (simp_all)
    
    private lemma no_matching_Goto_append1: "no_matching_Goto \<gamma> p (rs1@rs2) \<Longrightarrow> no_matching_Goto \<gamma> p rs1"
      using no_matching_Goto_append by fast
    private lemma no_matching_Goto_append2: "no_matching_Goto \<gamma> p (rs1@rs2) \<Longrightarrow> no_matching_Goto \<gamma> p rs2"
      using no_matching_Goto_append by fast
    
    private lemma seq_cons:
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r],Undecided\<rangle> \<Rightarrow> t" and "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,t\<rangle> \<Rightarrow> t'" and "no_matching_Goto \<gamma> p [r]"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs, Undecided\<rangle> \<Rightarrow> t'"
      proof -
        from assms have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r] @ rs, Undecided\<rangle> \<Rightarrow> t'" by (rule seq)
        thus ?thesis by simp
      qed
    
    context
      notes skipD[dest] list_app_singletonE[elim]
    begin
      lemma acceptD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Accept] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalAllow"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma dropD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Drop] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalDeny"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma rejectD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Reject] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Decision FinalDeny"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma logD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Log] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Undecided"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma emptyD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m Empty] \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> s = Undecided \<Longrightarrow> t = Undecided"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma nomatchD: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t \<Longrightarrow> r = [Rule m a] \<Longrightarrow> s = Undecided \<Longrightarrow> \<not> matches \<gamma> m p \<Longrightarrow> t = Undecided"
      by (induction rule: iptables_goto_bigstep.induct) auto
      
      lemma callD:
        assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r, s\<rangle> \<Rightarrow> t" "r = [Rule m (Call chain)]" "s = Undecided" "matches \<gamma> m p" "\<Gamma> chain = Some rs"
        obtains "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,s\<rangle> \<Rightarrow> t"
              | rs\<^sub>1 rs\<^sub>2 m' where "rs = rs\<^sub>1 @ Rule m' Return # rs\<^sub>2" "matches \<gamma> m' p" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> Undecided" "no_matching_Goto \<gamma> p rs\<^sub>1" "t = Undecided"
        using assms
        proof (induction r s t arbitrary: rs rule: iptables_goto_bigstep.induct)
          case (seq rs\<^sub>1)
          thus ?case by (cases rs\<^sub>1) auto
        qed auto
    end
    
    private lemmas iptables_goto_bigstepD = skipD acceptD dropD rejectD logD emptyD nomatchD decisionD callD gotoD
    
    private lemma seq':
      assumes "rs = rs\<^sub>1 @ rs\<^sub>2" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t\<rangle> \<Rightarrow> t'" and "no_matching_Goto \<gamma> p rs\<^sub>1"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,s\<rangle> \<Rightarrow> t'"
      using assms by (cases s) (auto intro: seq decision dest: decisionD)
    
    
    private lemma seq'_cons: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r],s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,t\<rangle> \<Rightarrow> t' \<Longrightarrow> no_matching_Goto \<gamma> p [r] \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs, s\<rangle> \<Rightarrow> t'"
      by (metis decision decisionD state.exhaust seq_cons)
    
    
    private lemma no_matching_Goto_take: "no_matching_Goto \<gamma> p rs \<Longrightarrow> no_matching_Goto \<gamma> p  (take n rs)"
      apply(induction n arbitrary: rs)
       apply(simp_all)
      apply(rename_tac r rs)
      apply(case_tac rs)
       apply(simp_all)
      apply(rename_tac r' rs')
      apply(case_tac r')
      apply(simp)
      apply(rename_tac m a)
      by(case_tac a) (simp_all)
    
    private lemma seq_split:
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t" "rs = rs\<^sub>1@rs\<^sub>2"
      obtains (no_matching_Goto) t' where "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t'" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t'\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p rs\<^sub>1"
            | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
    proof -
      have "(\<exists>t'. \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t' \<and> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t'\<rangle> \<Rightarrow> t \<and> no_matching_Goto \<gamma> p rs\<^sub>1) \<or> (\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t \<and> \<not> no_matching_Goto \<gamma> p rs\<^sub>1)"
      using assms
      proof (induction rs s t arbitrary: rs\<^sub>1 rs\<^sub>2 rule: iptables_goto_bigstep_induct)
        case Skip thus ?case by (auto intro: iptables_goto_bigstep.intros simp add: accept)
      next
        case Allow thus ?case by (cases rs\<^sub>1) (auto intro: iptables_goto_bigstep.intros simp add: accept)
      next
        case Deny thus ?case by (cases rs\<^sub>1) (auto intro: iptables_goto_bigstep.intros simp add: deny)
      next
        case Log thus ?case by (cases rs\<^sub>1) (auto intro: iptables_goto_bigstep.intros simp add: log empty)
      next
        case Nomatch thus ?case by (cases rs\<^sub>1) (auto intro: iptables_goto_bigstep.intros simp add: not_no_matching_Goto_singleton_cases)
      next
        case Decision thus ?case by (auto intro: iptables_goto_bigstep.intros)
      next
        case (Seq rs rsa rsb t t')
        hence rs: "rsa @ rsb = rs\<^sub>1 @ rs\<^sub>2" by simp
        note List.append_eq_append_conv_if[simp]
        from rs show ?case
          proof (cases rule: list_app_eq_cases)
            case longer
            with Seq have t1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>take (length rsa) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t"
              by simp
            from Seq.IH(2)[OF longer(2)] have IH:
              "(\<exists>t'a. \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>drop (length rsa) rs\<^sub>1, t\<rangle> \<Rightarrow> t'a \<and> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, t'a\<rangle> \<Rightarrow> t' \<and> no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)) \<or>
               \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>drop (length rsa) rs\<^sub>1, t\<rangle> \<Rightarrow> t' \<and> \<not> no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)" (is "?IH_no_Goto \<or> ?IH_Goto") by simp
            thus ?thesis
              proof(rule disjE)
                assume IH: ?IH_no_Goto
                from IH obtain t2
                  where t2a: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>drop (length rsa) rs\<^sub>1,t\<rangle> \<Rightarrow> t2"
                    and rs_part2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t2\<rangle> \<Rightarrow> t'"
                    and "no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)"
                  by blast
                with t1 rs_part2 have rs_part1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t2"
                  using Seq.hyps(4) longer(1) seq by fastforce
                have "no_matching_Goto \<gamma> p (take (length rsa) rs\<^sub>1 @ drop (length rsa) rs\<^sub>1)"
                  using Seq.hyps(4) \<open>no_matching_Goto \<gamma> p (drop (length rsa) rs\<^sub>1)\<close> longer(1)
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
    
            from rsb' Seq.hyps have t2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>drop (length rsa - length rs\<^sub>1) rs\<^sub>2,t\<rangle> \<Rightarrow> t'"
              by blast
    
            from Seq.IH(1)[OF rsa'] have IH:
              "(\<exists>t'. \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t' \<and> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>take (length rsa - length rs\<^sub>1) rs\<^sub>2, t'\<rangle> \<Rightarrow> t \<and> no_matching_Goto \<gamma> p rs\<^sub>1) \<or>
                \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t \<and> \<not> no_matching_Goto \<gamma> p rs\<^sub>1" (is "?IH_no_Goto \<or> ?IH_Goto") by simp
    
            thus ?thesis
              proof(rule disjE)
                assume IH: ?IH_no_Goto
                from IH obtain t1
                  where t1a: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,Undecided\<rangle> \<Rightarrow> t1"
                    and t1b: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>take (length rsa - length rs\<^sub>1) rs\<^sub>2,t1\<rangle> \<Rightarrow> t"
                    and "no_matching_Goto \<gamma> p rs\<^sub>1"
                  by blast
        
                  from no_matching_Goto_rs2 t2 seq' t1b have rs2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,t1\<rangle> \<Rightarrow> t'"
                    by  fastforce
                  from t1a rs2 \<open>no_matching_Goto \<gamma> p rs\<^sub>1\<close> show ?thesis by fast
              next
                assume ?IH_Goto
                thus ?thesis by (metis Seq.hyps(4) no_matching_Goto_append1 rsa') 
              qed
          qed
      next
        case Call_return
        hence "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Undecided"
          by (case_tac [!] rs\<^sub>1) (auto intro: iptables_goto_bigstep.skip iptables_goto_bigstep.call_return)
        thus ?case by fast
      next
        case (Call_result _ _ _ _ t)
        show ?case
          proof (cases rs\<^sub>1)
            case Nil
            with Call_result have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> t"
              by (auto intro: iptables_goto_bigstep.intros)
            thus ?thesis using local.Nil by auto 
          next
            case Cons
            with Call_result have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> t" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, t\<rangle> \<Rightarrow> t"
              by (auto intro: iptables_goto_bigstep.intros)
            thus ?thesis by fast
          qed
      next
        case (Goto_Decision m a chain rs rest X)
        thus ?case
          proof (cases rs\<^sub>1)
            case Nil
            with Goto_Decision have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Decision X"
              by (auto intro: iptables_goto_bigstep.intros)
            thus ?thesis using local.Nil by auto
          next
            case Cons
            with Goto_Decision have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Decision X" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, Decision X\<rangle> \<Rightarrow> Decision X"
              by (auto intro: iptables_goto_bigstep.intros) 
            thus ?thesis by fast
          qed
      next
        case (Goto_no_Decision m a chain rs rest rs\<^sub>1)
        from Goto_no_Decision have rs1rs2: "Rule m (Goto chain) # rest = rs\<^sub>1 @ rs\<^sub>2" by simp
        from goto_no_decision[OF Goto_no_Decision(1)]  Goto_no_Decision(3)  Goto_no_Decision(4)
          have x: "\<And>rest. \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m (Goto chain) # rest, Undecided\<rangle> \<Rightarrow> Undecided" by simp
        show ?case
          proof (cases rs\<^sub>1)
            case Nil
            with Goto_no_Decision have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2, Undecided\<rangle> \<Rightarrow> Undecided"
              by (auto intro: iptables_goto_bigstep.intros)
            thus ?thesis by fast
          next
            case (Cons rs\<^sub>1a rs\<^sub>1s)
            with rs1rs2 have "rs\<^sub>1 = Rule m (Goto chain) # (take (length rs\<^sub>1s) rest)" by simp
            from Cons rs1rs2 have"rs\<^sub>2 = drop (length rs\<^sub>1s) rest" by simp
            
            from Cons Goto_no_Decision have 1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
              using x by auto[1]
            have 2: "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
              by (simp add: Goto_no_Decision.hyps(1) \<open>rs\<^sub>1 = Rule m (Goto chain) # take (length rs\<^sub>1s) rest\<close>) 
            from 1 2 show ?thesis by fast
          qed
      qed
    thus ?thesis using matching_Goto no_matching_Goto by blast 
    qed
    
    private lemma seqE:
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1@rs\<^sub>2, s\<rangle> \<Rightarrow> t"
      obtains (no_matching_Goto) ti where "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>2,ti\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p rs\<^sub>1"
            | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs\<^sub>1,s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p rs\<^sub>1"
      using assms by (force elim: seq_split)
    
    private lemma seqE_cons:
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs, s\<rangle> \<Rightarrow> t"
      obtains (no_matching_Goto) ti where "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r],s\<rangle> \<Rightarrow> ti" "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,ti\<rangle> \<Rightarrow> t" "no_matching_Goto \<gamma> p [r]"
            | (matching_Goto) "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r],s\<rangle> \<Rightarrow> t" "\<not> no_matching_Goto \<gamma> p [r]"
      using assms by (metis append_Cons append_Nil seqE)
    
    private lemma seqE_cons_Undecided:
      assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs, Undecided\<rangle> \<Rightarrow> t"
      obtains (no_matching_Goto) ti where "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r],Undecided\<rangle> \<Rightarrow> ti" and "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs,ti\<rangle> \<Rightarrow> t" and "no_matching_Goto \<gamma> p [r]"
            | (matching_Goto) m chain rs' where "r = Rule m (Goto chain)" and "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)],Undecided\<rangle> \<Rightarrow> t" and "matches \<gamma> m p" "\<Gamma> chain = Some rs'"
      using assms
      proof(cases rule: seqE_cons)
      case no_matching_Goto thus ?thesis using local.that by simp
      next
      case matching_Goto
        from this(2) not_no_matching_Goto_singleton_cases[of \<gamma> p "(get_match r)" "(get_action r)", simplified] have
          "((\<exists>chain. (get_action r) = Goto chain) \<and> matches \<gamma> (get_match r) p)" by simp
        from this obtain chain m where r: "r = Rule m (Goto chain)" "matches \<gamma> m p" by(cases r) auto
        from matching_Goto r have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)],Undecided\<rangle> \<Rightarrow> t" by simp
        from gotoD[OF matching_Goto(1)] r \<open>matches \<gamma> m p\<close> obtain rs' where "\<Gamma> chain = Some rs'" by blast
      from local.that 
      show ?thesis using \<open>\<Gamma> chain = Some rs'\<close> \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> t\<close> r(1) r(2) by blast
    qed
    
    private lemma nomatch':
      assumes "\<And>r. r \<in> set rs \<Longrightarrow> \<not> matches \<gamma> (get_match r) p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> s"
      proof(cases s)
        case Undecided
        have "\<forall>r\<in>set rs. \<not> matches \<gamma> (get_match r) p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
          proof(induction rs)
            case Nil
            thus ?case by (fast intro: skip)
          next
            case (Cons r rs)
            hence "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[r], Undecided\<rangle> \<Rightarrow> Undecided"
              by (cases r) (auto intro: nomatch)
            with Cons show ?case
              by (metis list.set_intros(1) list.set_intros(2) not_no_matching_Goto_singleton_cases rule.collapse seq'_cons)
          qed
        with assms Undecided show ?thesis by simp
      qed (blast intro: decision)
    
    private lemma no_free_return: assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> t" and "matches \<gamma> m p" shows "False"
      proof -
      { fix a s
        have no_free_return_hlp: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>a,s\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>  s = Undecided \<Longrightarrow> a = [Rule m Return] \<Longrightarrow> False"
        proof (induction rule: iptables_goto_bigstep.induct)
          case (seq rs\<^sub>1)
          thus ?case
            by (cases rs\<^sub>1) (auto dest: skipD)
        qed simp_all
      } with assms show ?thesis by blast
      qed
  
  subsection\<open>Determinism\<close>
    private lemma iptables_goto_bigstep_Undecided_Undecided_deterministic: 
      "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> t = Undecided"
    proof(induction rs Undecided Undecided arbitrary: t rule: iptables_goto_bigstep_induct)
      case Skip thus ?case by(fastforce  dest: skipD logD emptyD nomatchD decisionD)
      next
      case Log thus ?case by(fastforce  dest: skipD logD emptyD nomatchD decisionD)
      next
      case Nomatch thus ?case by(fastforce  dest: skipD logD emptyD nomatchD decisionD)
      next
      case Seq thus ?case by (metis iptables_goto_bigstep_to_undecided seqE)
      next
      case (Call_return m a chain rs\<^sub>1 m' rs\<^sub>2) 
        from Call_return have " \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
          apply(frule_tac rs\<^sub>1=rs\<^sub>1 and m'=m' and chain=chain in call_return)
              by(simp_all)
        with Call_return show ?case
          apply simp
          apply (metis callD no_free_return seqE seqE_cons)
          done
      next
      case Call_result thus ?case by (meson callD)
      next
      case Goto_no_Decision thus ?case by (metis gotoD no_matching_Goto.simps(2) option.sel seqE_cons)
    qed
    
    private lemma iptables_goto_bigstep_Undecided_deterministic:
      "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t' \<Longrightarrow>  t' = t"
    proof(induction rs Undecided t arbitrary: t' rule: iptables_goto_bigstep_induct)
      case Skip thus ?case by(fastforce  dest: skipD logD emptyD nomatchD decisionD)
      next
      case Allow thus ?case by (auto dest: iptables_goto_bigstepD)
      next
      case Deny thus ?case by (auto dest: iptables_goto_bigstepD)
      next
      case Log thus ?case by (auto dest: iptables_goto_bigstepD)
      next
      case Nomatch thus ?case by (auto dest: iptables_goto_bigstepD)
      next
      case Seq thus ?case by (metis decisionD seqE state.exhaust)
      next
      case Call_return thus ?case by (meson call_return iptables_goto_bigstep_Undecided_Undecided_deterministic)
      next
      case Call_result thus ?case by (metis callD call_result iptables_goto_bigstep_Undecided_Undecided_deterministic)
      next
      case Goto_Decision thus ?case by (metis gotoD no_matching_Goto.simps(2) option.sel seqE_cons)
      next
      case Goto_no_Decision thus ?case by (meson goto_no_decision iptables_goto_bigstep_Undecided_Undecided_deterministic)
    qed
    
    qualified theorem iptables_goto_bigstep_deterministic: assumes "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t" and "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t'" shows "t = t'"
    using assms
      apply(cases s)
       apply(simp add: iptables_goto_bigstep_Undecided_deterministic)
      by(auto dest: decisionD)
  
  subsection\<open>Matching\<close>
    
    private lemma matches_rule_and_simp_help:
      assumes "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule (MatchAnd m m') a'], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m' a'], s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow>?r")
      proof
        assume ?l thus ?r
          by (induction "[Rule (MatchAnd m m') a']" s t rule: iptables_goto_bigstep_induct)
             (auto intro: iptables_goto_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
      next
        assume ?r thus ?l
          by (induction "[Rule m' a']" s t rule: iptables_goto_bigstep_induct)
             (auto intro: iptables_goto_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
      qed
    
    private lemma matches_MatchNot_simp: 
      assumes "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule (MatchNot m) a], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
      proof
        assume ?l thus ?r
          by (induction "[Rule (MatchNot m) a]" "Undecided" t rule: iptables_goto_bigstep_induct)
             (auto intro: iptables_goto_bigstep.intros simp: assms Cons_eq_append_conv dest: skipD)
      next
        assume ?r
        hence "t = Undecided"
          by (metis skipD)
        with assms show ?l
          by (fastforce intro: nomatch)
      qed
    
    private lemma matches_MatchNotAnd_simp:
      assumes "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule (MatchAnd (MatchNot m) m') a], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
      proof
        assume ?l thus ?r
          by (induction "[Rule (MatchAnd (MatchNot m) m') a]" "Undecided" t rule: iptables_goto_bigstep_induct)
             (auto intro: iptables_goto_bigstep.intros simp add: assms Cons_eq_append_conv dest: skipD)
      next
        assume ?r
        hence "t = Undecided"
          by (metis skipD)
        with assms show ?l
          by (fastforce intro: nomatch)
      qed
      
    private lemma matches_rule_and_simp:
      assumes "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule (MatchAnd m m') a'], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m' a'], s\<rangle> \<Rightarrow> t"
      proof (cases s)
        case Undecided
        with assms show ?thesis
          by (simp add: matches_rule_and_simp_help)
      next
        case Decision
        thus ?thesis by (metis decision decisionD)
      qed
    
    
    
    qualified definition add_match :: "'a match_expr \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
      "add_match m rs = map (\<lambda>r. case r of Rule m' a' \<Rightarrow> Rule (MatchAnd m m') a') rs"
    
    private lemma add_match_split: "add_match m (rs1@rs2) = add_match m rs1 @ add_match m rs2"
      unfolding add_match_def
      by (fact map_append)
    
    private lemma add_match_split_fst: "add_match m (Rule m' a' # rs) = Rule (MatchAnd m m') a' # add_match m rs"
      unfolding add_match_def
      by simp
    
    private lemma matches_add_match_no_matching_Goto_simp: "matches \<gamma> m p \<Longrightarrow> no_matching_Goto \<gamma> p (add_match m rs) \<Longrightarrow> no_matching_Goto \<gamma> p rs"
      apply(induction rs)
       apply(simp_all)
      apply(rename_tac r rs)
      apply(case_tac r)
      apply(simp add: add_match_split_fst no_matching_Goto_tail)
      apply(drule no_matching_Goto_head)
      apply(rename_tac m' a')
      apply(case_tac a')
              apply simp_all
      done
    
    
    private lemma matches_add_match_no_matching_Goto_simp2: "matches \<gamma> m p \<Longrightarrow>  no_matching_Goto \<gamma> p rs \<Longrightarrow> no_matching_Goto \<gamma> p (add_match m rs)"
      apply(induction rs)
       apply(simp add: add_match_def)
      apply(rename_tac r rs)
      apply(case_tac r)
      apply(simp add: add_match_split_fst no_matching_Goto_tail)
      apply(rename_tac m' a')
      apply(case_tac a')
              apply simp_all
      done
    
    private lemma matches_add_match_MatchNot_no_matching_Goto_simp: "\<not> matches \<gamma> m p \<Longrightarrow> no_matching_Goto \<gamma> p (add_match m rs)"
      apply(induction rs)
       apply(simp add: add_match_def)
      apply(rename_tac r rs)
      apply(case_tac r)
      apply(simp add: add_match_split_fst no_matching_Goto_tail)
      apply(rename_tac m' a')
      apply(case_tac a')
              apply simp_all
      done
    
    
    private lemma not_matches_add_match_simp:
      assumes "\<not> matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], Undecided\<rangle> \<Rightarrow> t"
      proof(induction rs)
      case Nil thus ?case unfolding add_match_def by simp
      next
      case (Cons r rs)
        obtain m' a where r: "r = Rule m' a" by(cases r, simp)
        let ?lhs="\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule (MatchAnd m m') a # add_match m rs, Undecided\<rangle> \<Rightarrow> t"
        let ?rhs="\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], Undecided\<rangle> \<Rightarrow> t"
        { assume ?lhs
          from \<open>?lhs\<close> Cons have ?rhs
           proof(cases  \<Gamma> \<gamma> p "Rule (MatchAnd m m') a" "add_match m rs"  t rule: seqE_cons_Undecided)
           case (no_matching_Goto ti)
             hence "ti = Undecided"  by (simp add: assms nomatchD)
             with no_matching_Goto Cons show ?thesis by simp
           next
           case (matching_Goto) with Cons assms show ?thesis by force
         qed
        } note 1=this
        { assume ?rhs
          hence "t = Undecided" using skipD by metis
          with Cons.IH \<open>?rhs\<close> have ?lhs 
           by (meson assms matches.simps(1) nomatch not_no_matching_Goto_singleton_cases seq_cons)  
        } with 1 show ?case by(auto simp add: r add_match_split_fst)
      qed
    
    private lemma matches_add_match_MatchNot_simp:
      assumes m: "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[], s\<rangle> \<Rightarrow> t" (is "?l s \<longleftrightarrow> ?r s")
      proof (cases s)
        case Undecided
        have "?l Undecided \<longleftrightarrow> ?r Undecided"
          proof
            assume "?l Undecided" with m show "?r Undecided"
              proof (induction rs)
                case Nil
                thus ?case
                  unfolding add_match_def by simp
              next
                case (Cons r rs)
                thus ?case
                  by (cases r) (metis matches_MatchNotAnd_simp skipD seqE_cons add_match_split_fst)
              qed
          next
            assume "?r Undecided" with m show "?l Undecided"
              proof (induction rs)
                case Nil
                thus ?case
                  unfolding add_match_def by simp
              next
                case (Cons r rs)
                hence "t = Undecided" using skipD by metis
                with Cons show ?case
                  apply (cases r)
                  apply(simp add: add_match_split_fst)
                  by (metis matches.simps(1) matches.simps(2) matches_MatchNotAnd_simp not_no_matching_Goto_singleton_cases seq_cons)
              qed
          qed
        with Undecided show ?thesis by fast
      next
        case (Decision d)
        thus ?thesis
          by(metis decision decisionD)
      qed
    
    
    private lemma just_show_all_bigstep_semantics_equalities_with_start_Undecided: 
          "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs1, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs2, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> 
           \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs1, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs2, s\<rangle> \<Rightarrow> t"
      apply(cases s)
       apply(simp)
      apply(simp)
      using decision decisionD by fastforce
      
    private lemma matches_add_match_simp_helper:
      assumes m: "matches \<gamma> m p"
      shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
      proof
        assume ?l with m show ?r
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
             obtain m' a where r: "r = Rule m' a" by(cases r, simp)
             from Cons have " \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule (MatchAnd m m') a # add_match m rs, Undecided\<rangle> \<Rightarrow> t"
               by(simp add: r add_match_split_fst)
             from this Cons have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m' a # rs, Undecided\<rangle> \<Rightarrow> t"
             proof(cases rule: seqE_cons_Undecided)
               case (no_matching_Goto ti)
                from no_matching_Goto(3) Cons.prems(1) not_no_matching_Goto_singleton_cases
                  have "no_matching_Goto \<gamma> p [Rule m' a]" by (metis matches.simps(1))
                with no_matching_Goto Cons show ?thesis
                 apply(simp add: matches_rule_and_simp)
                 apply(cases ti)
                  apply (simp add: seq'_cons)
                 by (metis decision decisionD seq'_cons)
               next
               case (matching_Goto) with Cons show ?thesis
                apply(clarify)
                apply(simp add: matches_rule_and_simp_help)
                by (simp add: seq_cons_Goto_t)
             qed
             thus ?case by(simp add: r)
          qed
      next
        assume ?r with m show ?l
          proof (induction rs)
            case Nil
            thus ?case
              unfolding add_match_def by simp
          next
            case (Cons r rs)
             obtain m' a where r: "r = Rule m' a" by(cases r, simp)
             from Cons have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m' a # rs, Undecided\<rangle> \<Rightarrow> t" by(simp add: r)
             from this have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule (MatchAnd m m') a # add_match m rs, Undecided\<rangle> \<Rightarrow> t"
                proof(cases \<Gamma> \<gamma> p "Rule m' a" rs t rule: seqE_cons_Undecided)
                case (no_matching_Goto ti)
                  from no_matching_Goto Cons.prems matches_rule_and_simp[symmetric] have
                    "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule (MatchAnd m m') a], Undecided\<rangle> \<Rightarrow> ti" by fast
                  with Cons.prems Cons.IH no_matching_Goto show ?thesis
                   apply(cases ti)
                    apply (metis matches.simps(1) not_no_matching_Goto_singleton_cases seq_cons)
                   apply (metis decision decisionD matches.simps(1) not_no_matching_Goto_singleton_cases seq_cons)
                   done
                next
                case (matching_Goto) with Cons show ?thesis
                  by (simp add: matches_rule_and_simp_help seq_cons_Goto_t)
             qed
             thus ?case by(simp add: r add_match_split_fst)
          qed
      qed
    
    
    private lemma matches_add_match_simp:
      "matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t"
      apply(rule just_show_all_bigstep_semantics_equalities_with_start_Undecided)
      by(simp add: matches_add_match_simp_helper)
    
    private lemma not_matches_add_matchNot_simp:
      "\<not> matches \<gamma> m p \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t"
      by (simp add: matches_add_match_simp)
    
  subsection\<open>Goto Unfolding\<close>
    private lemma unfold_Goto_Undecided:
        assumes chain_defined: "\<Gamma> chain = Some rs" and no_matching_Goto_rs: "no_matching_Goto \<gamma> p rs"
        shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>(Rule m (Goto chain))#rest, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs @ add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t"
              (is "?l \<longleftrightarrow> ?r")
    proof
      assume ?l
      thus ?r
        proof(cases rule: seqE_cons_Undecided)
        case (no_matching_Goto ti)
          from no_matching_Goto have "\<not> matches \<gamma> m p" by simp
          with no_matching_Goto have ti: "ti = Undecided" using nomatchD by metis
          from \<open>\<not> matches \<gamma> m p\<close> have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> Undecided"
            using not_matches_add_match_simp skip by fast
          from \<open>\<not> matches \<gamma> m p\<close> matches_add_match_MatchNot_no_matching_Goto_simp have "no_matching_Goto \<gamma> p (add_match m rs)" by force
          from no_matching_Goto ti have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rest, Undecided\<rangle> \<Rightarrow> t" by simp
          with not_matches_add_matchNot_simp[OF \<open>\<not> matches \<gamma> m p\<close>] have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t" by simp
          show ?thesis
            by (meson \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t\<close> \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> Undecided\<close> \<open>no_matching_Goto \<gamma> p (add_match m rs)\<close> seq)
        next
        case (matching_Goto m chain rs')
          from matching_Goto gotoD assms have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t" by fastforce
          hence 1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs, Undecided\<rangle> \<Rightarrow> t" by (simp add: matches_add_match_simp matching_Goto(3))
          have 2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rest, t\<rangle> \<Rightarrow> t" by (simp add: matches_add_match_MatchNot_simp matching_Goto(3) skip)
          from no_matching_Goto_rs matches_add_match_no_matching_Goto_simp2 matching_Goto have 3: "no_matching_Goto \<gamma> p (add_match m rs)" by fast
          from 1 2 3 show ?thesis using matching_Goto(1) seq by fastforce
        qed
    next
      assume ?r
      thus ?l
        proof(cases "matches \<gamma> m p")
        case True
          have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t"
            by (metis True \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs @ add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t\<close>
                matches_add_match_MatchNot_simp matches_add_match_simp_helper self_append_conv seq' seqE)
          show ?l
          apply(cases t)
           using goto_no_decision[OF True] chain_defined apply (metis \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t\<close>)
          using goto_decision[OF True, of \<Gamma> chain rs _ rest] chain_defined apply (metis \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t\<close>)
          done
        next
        case False
          with \<open>?r\<close> have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match (MatchNot m) rest, Undecided\<rangle> \<Rightarrow> t"
            by (metis matches_add_match_MatchNot_no_matching_Goto_simp not_matches_add_match_simp seqE skipD)
          with False have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rest, Undecided\<rangle> \<Rightarrow> t" by (meson not_matches_add_matchNot_simp) 
          show ?l by (meson False \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rest, Undecided\<rangle> \<Rightarrow> t\<close> nomatch not_no_matching_Goto_singleton_cases seq_cons)
        qed
    qed
    
    
    (*
    This theorem allows us to unfold the deepest goto in a ruleset.
    This can be iterated to get to the higher-level gotos.
    *)
    qualified theorem unfold_Goto:
        assumes chain_defined: "\<Gamma> chain = Some rs" and no_matching_Goto_rs: "no_matching_Goto \<gamma> p rs"
        shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>(Rule m (Goto chain))#rest, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>add_match m rs @ add_match (MatchNot m) rest, s\<rangle> \<Rightarrow> t"
      apply(rule just_show_all_bigstep_semantics_equalities_with_start_Undecided)
      using assms unfold_Goto_Undecided by fast
    
    
    
    text\<open>A chain that will definitely come to a direct decision\<close>
    qualified fun terminal_chain :: "'a rule list \<Rightarrow> bool" where
      "terminal_chain [] = False" |
      "terminal_chain [Rule MatchAny Accept] = True" |
      "terminal_chain [Rule MatchAny Drop] = True" |
      "terminal_chain [Rule MatchAny Reject] = True" |
      "terminal_chain ((Rule _ (Goto _))#rs) = False" |
      "terminal_chain ((Rule _ (Call _))#rs) = False" |
      "terminal_chain ((Rule _ Return)#rs) = False" |
      "terminal_chain ((Rule _ Unknown)#rs) = False" |
      "terminal_chain (_#rs) = terminal_chain rs"
    
    private lemma terminal_chain_no_matching_Goto: "terminal_chain rs \<Longrightarrow> no_matching_Goto \<gamma> p rs"
       by(induction rs rule: terminal_chain.induct)  simp_all
    
    text\<open>A terminal chain means (if the semantics are actually defined) that the chain will
         ultimately yield a final filtering decision, for all packets.\<close>
    qualified lemma "terminal_chain rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<exists>X. t = Decision X"
            apply(induction rs)
             apply(simp)
            apply(rename_tac r rs)
            apply(case_tac r)
            apply(rename_tac m a)
            apply(simp)
            apply(frule_tac \<gamma>=\<gamma> and p=p in terminal_chain_no_matching_Goto)
            apply(case_tac a)
                    apply(simp_all)
                apply(erule seqE_cons, simp_all,
                       metis iptables_goto_bigstepD matches.elims terminal_chain.simps terminal_chain.simps terminal_chain.simps)+
            done
    
    private lemma replace_Goto_with_Call_in_terminal_chain_Undecided:
        assumes chain_defined: "\<Gamma> chain = Some rs" and terminal_chain: "terminal_chain rs"
        shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"
              (is "?l \<longleftrightarrow> ?r")
      proof
        assume ?l
        thus ?r
          proof(cases rule: seqE_cons_Undecided)
          case (no_matching_Goto ti)
            from no_matching_Goto have "\<not> matches \<gamma> m p" by simp
            with nomatch have 1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> Undecided" by fast
            from \<open>\<not> matches \<gamma> m p\<close> nomatch have 2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" by fast
            from 1 2 show ?thesis
              using \<open>?l\<close> iptables_goto_bigstep_Undecided_Undecided_deterministic by fastforce 
          next
          case (matching_Goto m chain rs')
            from matching_Goto gotoD assms have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t" by fastforce
            from call_result[OF \<open>matches \<gamma> m p\<close> chain_defined \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t\<close>] show ?thesis
              by (metis matching_Goto(1) rule.sel(1))
          qed
      next
        assume ?r
        thus ?l
          proof(cases "matches \<gamma> m p")
          case True
            {fix rs1::"'a rule list" and  m' and rs2
              have "terminal_chain (rs1 @ Rule m' Return # rs2) \<Longrightarrow> False"
              apply(induction rs1)
               apply(simp_all)
              apply(rename_tac r' rs')
              apply(case_tac r')
              apply(rename_tac m a)
              apply(simp_all)
              apply(case_tac a)
                      apply(simp_all)
                apply (metis append_is_Nil_conv hd_Cons_tl terminal_chain.simps)+
              done
            } note no_return=this
            have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t"
              apply(rule callD[OF \<open>?r\<close> _ _ True chain_defined])
                 apply(simp_all)
              using no_return terminal_chain by blast
            show ?l
              apply(cases t)
               using goto_no_decision[OF True] chain_defined apply (metis \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t\<close>)
              using goto_decision[OF True, of \<Gamma> chain rs _ "[]"] chain_defined apply (metis \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t\<close>)
              done
          next
          case False
            show ?l using False \<open>\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t\<close> nomatch nomatchD by fastforce 
          qed
      qed
    
  
  qualified theorem replace_Goto_with_Call_in_terminal_chain:
        assumes chain_defined: "\<Gamma> chain = Some rs" and terminal_chain: "terminal_chain rs"
        shows "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], s\<rangle> \<Rightarrow> t"
      apply(rule just_show_all_bigstep_semantics_equalities_with_start_Undecided)
      using assms replace_Goto_with_Call_in_terminal_chain_Undecided by fast
  

  qualified fun rewrite_Goto_chain_safe :: "(string \<rightharpoonup> 'a rule list) \<Rightarrow> 'a rule list \<Rightarrow> ('a rule list) option" where
    "rewrite_Goto_chain_safe _ [] = Some []" |
    "rewrite_Goto_chain_safe \<Gamma> ((Rule m (Goto chain))#rs) =
      (case (\<Gamma> chain) of None     \<Rightarrow> None
                      |  Some rs' \<Rightarrow> (if
                                         \<not> terminal_chain rs'
                                      then
                                         None
                                      else
                                         map_option (\<lambda>rs. Rule m (Call chain) # rs) (rewrite_Goto_chain_safe \<Gamma> rs)
                                     )
      )" |
    "rewrite_Goto_chain_safe \<Gamma> (r#rs) = map_option (\<lambda>rs. r # rs) (rewrite_Goto_chain_safe \<Gamma> rs)"

  private fun rewrite_Goto_safe_internal
    :: "(string \<times> 'a rule list) list \<Rightarrow> (string \<times> 'a rule list) list \<Rightarrow> (string \<times> 'a rule list) list option" where
    "rewrite_Goto_safe_internal _ [] = Some []" |
    "rewrite_Goto_safe_internal \<Gamma> ((chain_name, rs)#cs) = 
                (case rewrite_Goto_chain_safe (map_of \<Gamma>) rs of
                         None \<Rightarrow> None
                       | Some rs' \<Rightarrow> map_option (\<lambda>rst. (chain_name, rs')#rst) (rewrite_Goto_safe_internal \<Gamma> cs)
                )"

  qualified fun rewrite_Goto_safe :: "(string \<times> 'a rule list) list \<Rightarrow> (string \<times> 'a rule list) list option" where
    "rewrite_Goto_safe cs = rewrite_Goto_safe_internal cs cs"


  (*use rewrite_Goto_chain_safe whenever possible!*)
  qualified definition rewrite_Goto :: "(string \<times> 'a rule list) list \<Rightarrow> (string \<times> 'a rule list) list" where
    "rewrite_Goto cs = the (rewrite_Goto_safe cs)"


  private lemma step_IH_cong: "(\<And>s. \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs2, s\<rangle> \<Rightarrow> t) \<Longrightarrow>
         \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs1, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>r#rs2, s\<rangle> \<Rightarrow> t"
  apply(rule iffI)
   apply(erule seqE_cons)
    apply(rule seq'_cons)
      apply simp_all
   apply(drule not_no_matching_Goto_cases)
    apply(simp; fail)
   apply(elim exE conjE, rename_tac rs1a m chain rs2a)
   apply(subgoal_tac "r = Rule m (Goto chain)")
    prefer 2
    subgoal by (simp add: Cons_eq_append_conv)
   apply(thin_tac "[r] = _ @ Rule m (Goto chain) # _")
   apply simp
   apply (metis decision decisionD seq_cons_Goto_t state.exhaust)
  apply(erule seqE_cons)
   apply(rule seq'_cons)
     apply simp_all
  apply(drule not_no_matching_Goto_cases)
   apply(simp; fail)
  apply(elim exE conjE, rename_tac rs1a m chain rs2a)
  apply(subgoal_tac "r = Rule m (Goto chain)")
   prefer 2
   subgoal by (simp add: Cons_eq_append_conv)
  apply(thin_tac "[r] = _ @ Rule m (Goto chain) # _")
  apply simp
  apply (metis decision decisionD seq_cons_Goto_t state.exhaust)
  done

  private lemma terminal_chain_decision: 
    "terminal_chain rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<exists>X. t = Decision X"
    apply(induction rs arbitrary: t rule: terminal_chain.induct)
                                         apply simp_all
                                    apply(auto dest: iptables_goto_bigstepD)[3]
                                 apply(erule seqE_cons, simp_all, blast dest: iptables_goto_bigstepD)+ (*6s*)
    done
    

  private lemma terminal_chain_Goto_decision: "\<Gamma> chain = Some rs \<Longrightarrow> terminal_chain rs \<Longrightarrow> matches \<gamma> m p \<Longrightarrow>
       \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], s\<rangle> \<Rightarrow> t \<Longrightarrow> \<exists>X. t = Decision X"
    apply(cases s)
     apply(drule gotoD, simp_all)
     apply(elim exE conjE, simp_all)
     using terminal_chain_decision apply fast
    by (meson decisionD)
    

  qualified theorem rewrite_Goto_chain_safe:
    "rewrite_Goto_chain_safe \<Gamma> rs = Some rs' \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs', s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t"
  proof(induction \<Gamma> rs arbitrary: rs' s rule: rewrite_Goto_chain_safe.induct)
  case 1 thus ?case by (simp split: option.split_asm if_split_asm)
  next
  case (2 \<Gamma> m chain rs) 
    from 2(2) obtain z x2 where "\<Gamma> chain = Some x2" and "terminal_chain x2"
            and "rs' = Rule m (Call chain) # z"
            and "Some z = rewrite_Goto_chain_safe \<Gamma> rs"
    by(auto split: option.split_asm if_split_asm)
    from 2(1) \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close> \<open>Some z = rewrite_Goto_chain_safe \<Gamma> rs\<close> 
      have IH: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>z, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, s\<rangle> \<Rightarrow> t" for s by simp

    have "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m (Call chain) # z, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>Rule m (Goto chain) # rs, Undecided\<rangle> \<Rightarrow> t"
          (is "?lhs \<longleftrightarrow> ?rhs")
    proof(intro iffI)
      assume ?lhs
      with IH obtain ti where ti1: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> ti" and ti2: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>rs, ti\<rangle> \<Rightarrow> t"
        by(auto elim: seqE_cons)
      show ?rhs
      proof(cases "matches \<gamma> m p")
      case False
        from replace_Goto_with_Call_in_terminal_chain \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close> 
        have " \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> ti \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> ti"
          by fast
        with False ti1 ti2 show ?thesis by(rule_tac t=ti in seq'_cons) simp+
      next
      case True
        from ti1 \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close>
        have g: "\<Gamma>,\<gamma>,p\<turnstile>\<^sub>g \<langle>[Rule m (Goto chain)], Undecided\<rangle> \<Rightarrow> ti"
          by(subst(asm) replace_Goto_with_Call_in_terminal_chain[symmetric]) simp+
        with True \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close> obtain X where X: "ti = Decision X"
          by(blast dest: terminal_chain_Goto_decision)
        with this ti2 have "t = Decision X"
          by(simp add: decisionD)
        with g X True ti2 \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close> show ?thesis
          apply(simp)
          apply(rule seq_cons_Goto_t, simp_all)
          done
      qed
    next
      assume ?rhs
      with IH \<open>\<Gamma> chain = Some x2\<close> \<open>terminal_chain x2\<close> \<open>Some z = rewrite_Goto_chain_safe \<Gamma> rs\<close> show ?lhs
        apply -
        apply(erule seqE_cons)
         subgoal for ti
         apply simp_all
         apply(rule_tac t=ti in seq'_cons)
           apply simp_all
         using replace_Goto_with_Call_in_terminal_chain by fast
        apply simp
        apply(frule(3) terminal_chain_Goto_decision)
        apply(subst(asm) replace_Goto_with_Call_in_terminal_chain, simp_all)
        apply(rule seq'_cons, simp_all)
        apply(elim exE)
        by (simp add: decision)
    qed
    with \<open>rs' = Rule m (Call chain) # z\<close> show ?case
      apply -
      apply(rule just_show_all_bigstep_semantics_equalities_with_start_Undecided)
      by simp

  qed(auto cong: step_IH_cong)
  


  text\<open>Example: The semantics are actually defined (for this example).\<close>
  lemma defines "\<gamma> \<equiv> (\<lambda>_ _. True)" and "m \<equiv> MatchAny"
  shows "[''FORWARD'' \<mapsto> [Rule m Log, Rule m (Call ''foo''), Rule m Drop],
          ''foo'' \<mapsto> [Rule m Log, Rule m (Goto ''bar''), Rule m Reject],
          ''bar'' \<mapsto> [Rule m (Goto ''baz''), Rule m Reject],
          ''baz'' \<mapsto> [(Rule m Accept)]],
      \<gamma>,p\<turnstile>\<^sub>g\<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalAllow)"
  apply(subgoal_tac "matches \<gamma> m p")
   prefer 2
   apply(simp add: \<gamma>_def m_def; fail)
  apply(rule call_result)
    apply(auto)
  apply(rule_tac t=Undecided in seq_cons)
    apply(auto intro: log)
  apply(rule_tac t="Decision FinalAllow" in seq_cons)
    apply(auto intro: decision)
  apply(rule call_result)
     apply(simp)+
  apply(rule_tac t=Undecided in seq_cons)
    apply(auto intro: log)
  apply(rule goto_decision)
    apply(simp)+
  apply(rule goto_decision)
    apply(simp)+
  apply(auto intro: accept)
  done


end


end
