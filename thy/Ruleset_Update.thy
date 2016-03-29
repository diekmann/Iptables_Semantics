theory Ruleset_Update
imports Matching
begin

lemma free_return_not_match: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<not> matches \<gamma> m p"
  using no_free_return by fast


subsection{*Background Ruleset Updating*}
lemma update_Gamma_nomatch: 
  assumes "\<not> matches \<gamma> m p"
  shows "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
  proof
    assume ?l thus ?r
      proof (induction rs' s t rule: iptables_bigstep_induct)
        case (Call_return m a chain' rs\<^sub>1 m' rs\<^sub>2)
        thus ?case
          proof (cases "chain' = chain")
            case True
            with Call_return show ?thesis
              apply simp
              apply(cases "rs\<^sub>1")
              using assms apply fastforce
              apply(rule_tac rs\<^sub>1="list" and m'="m'" and rs\<^sub>2="rs\<^sub>2" in call_return)
                 apply(simp)
                apply(simp)
               apply(simp)
              apply(simp)
              apply(erule seqE_cons[where \<Gamma>="(\<lambda>a. if a = chain then Some rs else \<Gamma> a)"])
              apply(frule iptables_bigstep_to_undecided[where \<Gamma>="(\<lambda>a. if a = chain then Some rs else \<Gamma> a)"])
              apply(simp)
              done
          qed (auto intro: call_return)
      next
        case (Call_result m' a' chain' rs' t')
        have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain')], Undecided\<rangle> \<Rightarrow> t'"
          proof (cases "chain' = chain")
            case True
            with Call_result have "Rule m a # rs = rs'" "(\<Gamma>(chain \<mapsto> rs)) chain' = Some rs"
              by simp+
            with assms Call_result show ?thesis
              by (metis call_result nomatchD seqE_cons)
          next
            case False
            with Call_result show ?thesis
              by (metis call_result fun_upd_apply)
          qed
        with Call_result show ?case
          by fast
      qed (auto intro: iptables_bigstep.intros)
  next
    assume ?r thus ?l
      proof (induction rs' s t rule: iptables_bigstep_induct)
        case (Call_return m' a' chain' rs\<^sub>1)
        thus ?case
          proof (cases "chain' = chain")
            case True
            with Call_return show ?thesis
              using assms
              by (auto intro: seq_cons nomatch intro!: call_return[where rs\<^sub>1 = "Rule m a # rs\<^sub>1"])
          qed (auto intro: call_return)
      next
        case (Call_result m' a' chain' rs')
        thus ?case
          proof (cases "chain' = chain")
            case True
            with Call_result show ?thesis
              using assms by (auto intro: seq_cons nomatch intro!: call_result)
          qed (auto intro: call_result)
      qed (auto intro: iptables_bigstep.intros)
  qed

lemma update_Gamma_log_empty:
  assumes "a = Log \<or> a = Empty"
  shows "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t \<longleftrightarrow>
         \<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t" (is "?l \<longleftrightarrow> ?r")
  proof
    assume ?l thus ?r
      proof (induction rs' s t rule: iptables_bigstep_induct)
        case (Call_return m' a' chain' rs\<^sub>1 m'' rs\<^sub>2)
        (*it seems that Isabelle has problems to apply @{thm fun_upd_apply} at the semantics if it appears in the goal without @{text \<lambda>}*)
        note [simp] = fun_upd_apply[abs_def]

        from Call_return have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain')], Undecided\<rangle> \<Rightarrow> Undecided" (is ?Call_return_case)
          proof(cases "chain' = chain")
          case True with Call_return show ?Call_return_case
            --{*@{term rs\<^sub>1} cannot be empty*}
            proof(cases "rs\<^sub>1")
            case Nil with Call_return(3) `chain' = chain` assms have "False" by simp
              thus ?Call_return_case by simp
            next
            case (Cons r\<^sub>1 rs\<^sub>1s)
            from Cons Call_return have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>r\<^sub>1 # rs\<^sub>1s, Undecided\<rangle> \<Rightarrow> Undecided" by blast
            with seqE_cons[where \<Gamma>="\<Gamma>(chain \<mapsto> rs)"] obtain ti where 
              "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[r\<^sub>1], Undecided\<rangle> \<Rightarrow> ti" and "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs\<^sub>1s, ti\<rangle> \<Rightarrow> Undecided" by metis
            with iptables_bigstep_to_undecided[where \<Gamma>="\<Gamma>(chain \<mapsto> rs)"] have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs\<^sub>1s, Undecided\<rangle> \<Rightarrow> Undecided" by fast
            with Cons Call_return `chain' = chain` show ?Call_return_case
               apply(rule_tac rs\<^sub>1="rs\<^sub>1s" and m'="m''" and rs\<^sub>2="rs\<^sub>2" in call_return)
                  apply(simp_all)
               done
             qed
          next
          case False with Call_return show ?Call_return_case
           by (auto intro: call_return)
          qed
        thus ?case using Call_return by blast
      next
        case (Call_result m' a' chain' rs' t')
        thus ?case
          proof (cases "chain' = chain")
            case True
            with Call_result have "rs' = [] @ [Rule m a] @ rs"
              by simp
            with Call_result assms have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[] @ rs, Undecided\<rangle> \<Rightarrow> t'"
              using log_remove empty_empty by fast
            hence "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t'"
              by simp
            with Call_result True show ?thesis
              by (metis call_result fun_upd_same)
          qed (fastforce intro: call_result)
      qed (auto intro: iptables_bigstep.intros)
  next
    have cases_a: "\<And>P. (a = Log \<Longrightarrow> P a) \<Longrightarrow> (a = Empty \<Longrightarrow> P a) \<Longrightarrow> P a" using assms by blast
    assume ?r thus ?l
      proof (induction rs' s t rule: iptables_bigstep_induct)
        case (Call_return m' a' chain' rs\<^sub>1 m'' rs\<^sub>2)
        from Call_return have xx: "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>Rule m a # rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
          apply -
          apply(rule cases_a)
          apply (auto intro: nomatch seq_cons intro!: log empty simp del: fun_upd_apply)
          done
        with Call_return show ?case
          proof(cases "chain' = chain")
            case False
            with Call_return have x: "(\<Gamma>(chain \<mapsto> Rule m a # rs)) chain' = Some (rs\<^sub>1 @ Rule m'' Return # rs\<^sub>2)"
              by(simp)
            with Call_return have "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain')], Undecided\<rangle> \<Rightarrow> Undecided"
             apply -
             apply(rule call_return[where rs\<^sub>1="rs\<^sub>1" and m'="m''" and rs\<^sub>2="rs\<^sub>2"])
                apply(simp_all add: x xx del: fun_upd_apply)
             done
             thus "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' a'], Undecided\<rangle> \<Rightarrow> Undecided" using Call_return by simp
            next
            case True
            with Call_return have x: "(\<Gamma>(chain \<mapsto> Rule m a # rs)) chain' = Some (Rule m a # rs\<^sub>1 @ Rule m'' Return # rs\<^sub>2)"
              by(simp)
            with Call_return have "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain')], Undecided\<rangle> \<Rightarrow> Undecided"
             apply -
             apply(rule call_return[where rs\<^sub>1="Rule m a#rs\<^sub>1" and m'="m''" and rs\<^sub>2="rs\<^sub>2"])
                apply(simp_all add: x xx del: fun_upd_apply)
             done
             thus "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' a'], Undecided\<rangle> \<Rightarrow> Undecided" using Call_return by simp
          qed
      next
        case (Call_result ma a chaina rs t)
        thus ?case
          apply (cases "chaina = chain")
           apply(rule cases_a)
            apply (auto intro: nomatch seq_cons intro!: log empty call_result)[2]
          by (auto intro!: call_result)[1]
      qed (auto intro: iptables_bigstep.intros)
  qed

lemma map_update_chain_if: "(\<lambda>b. if b = chain then Some rs else \<Gamma> b) = \<Gamma>(chain \<mapsto> rs)"
  by auto

lemma no_recursive_calls_helper:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"
  and     "matches \<gamma> m p"
  and     "\<Gamma> chain = Some [Rule m (Call chain)]"
  shows   False
  using assms
  proof (induction "[Rule m (Call chain)]" Undecided t rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (metis Cons_eq_append_conv append_is_Nil_conv skipD)
  next
    case (Call_return chain' rs\<^sub>1 m' rs\<^sub>2)
    hence "rs\<^sub>1 @ Rule m' Return # rs\<^sub>2 = [Rule m (Call chain')]"
      by simp
    thus ?case
      by (cases "rs\<^sub>1") auto
  next
    case Call_result
    thus ?case
      by simp
  qed (auto intro: iptables_bigstep.intros)

lemma no_recursive_calls:
  "\<Gamma>(chain \<mapsto> [Rule m (Call chain)]),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> matches \<gamma> m p \<Longrightarrow> False"
  by (fastforce intro: no_recursive_calls_helper)

lemma no_recursive_calls2:
  assumes "\<Gamma>(chain \<mapsto> (Rule m (Call chain)) # rs''),\<gamma>,p\<turnstile> \<langle>(Rule m (Call chain)) # rs', Undecided\<rangle> \<Rightarrow> Undecided"
  and     "matches \<gamma> m p"
  shows   False
  using assms
  proof (induction "(Rule m (Call chain)) # rs'" Undecided Undecided arbitrary: rs' rule: iptables_bigstep_induct)
    case (Seq rs\<^sub>1 rs\<^sub>2 t)
    thus ?case
      by (cases rs\<^sub>1) (auto elim: seqE_cons simp add: iptables_bigstep_to_undecided)
  qed (auto intro: iptables_bigstep.intros simp: Cons_eq_append_conv)


lemma update_Gamma_nochange1: 
  assumes "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided"
  and     "\<Gamma>(chain \<mapsto> Rule m a # rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t"
  shows   "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs', s\<rangle> \<Rightarrow> t"
  using assms(2) proof (induction rs' s t rule: iptables_bigstep_induct)
    case (Call_return m a chaina rs\<^sub>1 m' rs\<^sub>2)
    thus ?case
      proof (cases "chaina = chain")
        case True
        with Call_return show ?thesis
          apply simp
          apply(cases "rs\<^sub>1")
          apply(simp)
          using assms apply (metis no_free_return) (*gives False*)
          apply(rule_tac rs\<^sub>1="list" and m'="m'" and rs\<^sub>2="rs\<^sub>2" in call_return)
          apply(simp)
          apply(simp)
          apply(simp)
          apply(simp)
          apply(erule seqE_cons[where \<Gamma>="(\<lambda>a. if a = chain then Some rs else \<Gamma> a)"])
          apply(frule iptables_bigstep_to_undecided[where \<Gamma>="(\<lambda>a. if a = chain then Some rs else \<Gamma> a)"])
          apply(simp)
          done
      qed (auto intro: call_return)
  next
    case (Call_result m a chaina rsa t)
    thus ?case
      proof (cases "chaina = chain")
        case True
        with Call_result show ?thesis
          apply(simp)
          apply(cases "rsa")
           apply(simp)
           apply(rule_tac rs=rs in call_result)
            apply(simp_all)
          apply(erule_tac seqE_cons[where \<Gamma>="(\<lambda>b. if b = chain then Some rs else \<Gamma> b)"])
          apply(case_tac t)
           apply(simp)
           apply(frule iptables_bigstep_to_undecided[where \<Gamma>="(\<lambda>b. if b = chain then Some rs else \<Gamma> b)"])
           apply(simp)
          apply(simp)
          apply(subgoal_tac "ti = Undecided")
           apply(simp)
          using assms(1)[simplified map_update_chain_if[symmetric]] iptables_bigstep_deterministic apply fast
          done
      qed (fastforce intro: call_result)
  qed (auto intro: iptables_bigstep.intros)

lemma update_gamme_remove_Undecidedpart:
  assumes "\<Gamma>(chain \<mapsto> rs'),\<gamma>,p\<turnstile> \<langle>rs', Undecided\<rangle> \<Rightarrow> Undecided"
  and     "\<Gamma>(chain \<mapsto> rs1@rs'),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  shows   "\<Gamma>(chain \<mapsto>rs'),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  using assms(2) proof (induction rs Undecided Undecided rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (auto simp: iptables_bigstep_to_undecided intro: seq)
  next
    case (Call_return m a chaina rs\<^sub>1 m' rs\<^sub>2)
    thus ?case
      apply(cases "chaina = chain")
       apply(simp)
       apply(cases "length rs1 \<le> length rs\<^sub>1")
        apply(simp add: List.append_eq_append_conv_if)
        apply(rule_tac rs\<^sub>1="drop (length rs1) rs\<^sub>1" and m'=m' and rs\<^sub>2=rs\<^sub>2 in call_return)
          apply(simp_all)[3]
        apply(subgoal_tac "rs\<^sub>1 = (take (length rs1) rs\<^sub>1) @ drop (length rs1) rs\<^sub>1")
         prefer 2 apply (metis append_take_drop_id)
        apply(clarify)
        apply(subgoal_tac "\<Gamma>(chain \<mapsto> drop (length rs1) rs\<^sub>1 @ Rule m' Return # rs\<^sub>2),\<gamma>,p\<turnstile> 
            \<langle>(take (length rs1) rs\<^sub>1) @ drop (length rs1) rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided")
         prefer 2 apply(auto)[1]
        apply(erule_tac rs\<^sub>1="take (length rs1) rs\<^sub>1" and rs\<^sub>2="drop (length rs1) rs\<^sub>1" in seqE)
        apply(simp)
        apply(frule_tac rs="drop (length rs1) rs\<^sub>1" in iptables_bigstep_to_undecided)
        apply(simp; fail) (*oh wow*)
       using assms apply (auto intro: call_result call_return)
      done
  next
    case (Call_result _ _ chain' rsa)
    thus ?case
      apply(cases "chain' = chain")
       apply(simp)
       apply(rule call_result)
         apply(simp_all)[2]
       apply (metis iptables_bigstep_to_undecided seqE)
      apply (auto intro: call_result)
      done
  qed (auto intro: iptables_bigstep.intros)

lemma update_Gamma_nocall:
  assumes "\<not> (\<exists>chain. a = Call chain)"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>',\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t"
  proof -
    {
      fix \<Gamma> \<Gamma>'
      have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>',\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t"
        proof (induction "[Rule m a]" s t rule: iptables_bigstep_induct)
          case Seq
          thus ?case by (metis (lifting, no_types) list_app_singletonE[where x = "Rule m a"] skipD)
        next
          case Call_return thus ?case using assms by metis
        next
          case Call_result thus ?case using assms by metis
        qed (auto intro: iptables_bigstep.intros)
    }
    thus ?thesis
      by blast
  qed

lemma update_Gamma_call:
  assumes "\<Gamma> chain = Some rs" and "\<Gamma>' chain = Some rs'"
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided" and "\<Gamma>',\<gamma>,p\<turnstile> \<langle>rs', Undecided\<rangle> \<Rightarrow> Undecided"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>',\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], s\<rangle> \<Rightarrow> t"
  proof -
    {
      fix \<Gamma> \<Gamma>' rs rs'
      assume assms:
        "\<Gamma> chain = Some rs" "\<Gamma>' chain = Some rs'"
        "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided" "\<Gamma>',\<gamma>,p\<turnstile> \<langle>rs', Undecided\<rangle> \<Rightarrow> Undecided"
      have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>',\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], s\<rangle> \<Rightarrow> t"
        proof (induction "[Rule m (Call chain)]" s t rule: iptables_bigstep_induct)
          case Seq
          thus ?case by (metis (lifting, no_types) list_app_singletonE[where x = "Rule m (Call chain)"] skipD)
        next
          case Call_result
          thus ?case
            using assms by (metis call_result iptables_bigstep_deterministic)
        qed (auto intro: iptables_bigstep.intros assms)
    }
    note * = this
    show ?thesis
      using *[OF assms(1-4)] *[OF assms(2,1,4,3)] by blast
  qed

lemma update_Gamma_remove_call_undecided:
  assumes "\<Gamma>(chain \<mapsto> Rule m (Call foo) # rs'),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  and     "matches \<gamma> m p"
  shows "\<Gamma>(chain \<mapsto> rs'),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  using assms
  proof (induction rs Undecided Undecided arbitrary: rule: iptables_bigstep_induct)
    case Seq
    thus ?case
      by (force simp: iptables_bigstep_to_undecided intro: seq')
  next
    case (Call_return m a chaina rs\<^sub>1 m' rs\<^sub>2)
    thus ?case
      apply(cases "chaina = chain")
      apply(cases "rs\<^sub>1")
      apply(force intro: call_return)
      apply(simp)
      apply(erule_tac \<Gamma>="\<Gamma>(chain \<mapsto> list @ Rule m' Return # rs\<^sub>2)" in seqE_cons)
      apply(frule_tac \<Gamma>="\<Gamma>(chain \<mapsto> list @ Rule m' Return # rs\<^sub>2)" in iptables_bigstep_to_undecided)
      apply(auto intro: call_return)
      done
  next
    case (Call_result m a chaina rsa)
    thus ?case
      apply(cases "chaina = chain")
      apply(simp)
      apply (metis call_result fun_upd_same iptables_bigstep_to_undecided seqE_cons)
      apply (auto intro: call_result)
      done
  qed (auto intro: iptables_bigstep.intros)

lemma all_return_subchain:
  assumes a1: "\<Gamma> chain = Some rs"
  and     a2: "matches \<gamma> m p"
  and     a3: "\<forall>r\<in>set rs. get_action r = Return"
  shows "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
  proof (cases "\<exists>r \<in> set rs. matches \<gamma> (get_match r) p")
    case True
    hence "(\<exists>rs1 r rs2. rs = rs1 @ r # rs2 \<and> matches \<gamma> (get_match r) p \<and> (\<forall>r'\<in>set rs1. \<not> matches \<gamma> (get_match r') p))"
      by (subst split_list_first_prop_iff[symmetric])
    then obtain rs1 r rs2
      where *: "rs = rs1 @ r # rs2" "matches \<gamma> (get_match r) p" "\<forall>r'\<in>set rs1. \<not> matches \<gamma> (get_match r') p"
      by auto

    with a3 obtain m' where "r = Rule m' Return"
      by (cases r) simp
    with * assms show ?thesis
      by (fastforce intro: call_return nomatch')
  next
    case False
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
      by (blast intro: nomatch')
    with a1 a2 show ?thesis
      by (metis call_result)
qed


lemma get_action_case_simp: "get_action (case r of Rule m' x \<Rightarrow> Rule (MatchAnd m m') x) = get_action r"
by (metis rule.case_eq_if rule.sel(2))




text{*
  We call a ruleset well-formed (wf) iff all @{const Call}s are into actually existing chains.
*}
definition wf_chain :: "'a ruleset \<Rightarrow> 'a rule list \<Rightarrow> bool" where
  "wf_chain \<Gamma> rs \<equiv> (\<forall>r \<in> set rs. \<forall> chain. get_action r = Call chain \<longrightarrow> \<Gamma> chain \<noteq> None)"
lemma wf_chain_append: "wf_chain \<Gamma> (rs1@rs2) \<longleftrightarrow> wf_chain \<Gamma> rs1 \<and> wf_chain \<Gamma> rs2"
  by(simp add: wf_chain_def, blast)

lemma wf_chain_fst: "wf_chain \<Gamma> (r # rs) \<Longrightarrow>  wf_chain \<Gamma> (rs)"
  by(simp add: wf_chain_def)


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

lemma "sanity_wf_ruleset \<Gamma> \<Longrightarrow> rs \<in> ran (map_of \<Gamma>) \<Longrightarrow> wf_chain (map_of \<Gamma>) rs"
  apply(simp add: sanity_wf_ruleset_def wf_chain_def)
  by fastforce


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







(*Scratch: showing that semantics are defined.
Not very important; I didn't find time to show this. But the rules are pretty obvious.
*)




(*the following three lemmas should be convincing that the semantics are always defined (for rulesets which
  can be loaded by the Linux kernel)*)

lemma semantics_bigstep_defined: assumes "\<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg"
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


lemma updategamma_insert_new: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> chain \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(chain \<mapsto> rs'),\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof(induction rule: iptables_bigstep_induct)
case (Call_result m a chain' rs t)
  thus ?case by (metis call_result domI fun_upd_def)
next
case Call_return
  thus ?case by (metis call_return domI fun_upd_def)
qed(auto intro: iptables_bigstep.intros)


lemma iptables_bigstep_defined_if_singleton_rules: "\<forall> r \<in> set rs. (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], s\<rangle> \<Rightarrow> t) \<Longrightarrow> \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
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







(*well founded relation.*)
definition calls_chain :: "'a ruleset \<Rightarrow> (string \<times> string) set" where
  "calls_chain \<Gamma> = {(r, s). case \<Gamma> r of Some rs \<Rightarrow> \<exists>m. Rule m (Call s) \<in> set rs | None \<Rightarrow> False}"
thm wf_induct
thm wf_induct_rule


lemma calls_chain_def2: "calls_chain \<Gamma> = {(caller, callee). \<exists>rs m. \<Gamma> caller = Some rs \<and> Rule m (Call callee) \<in> set rs}"
  unfolding calls_chain_def
  apply(safe)
   apply(simp split: option.split_asm)
  apply(simp)
  by blast

lemma "calls_chain [''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
          ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
          ''bar'' \<mapsto> [],
          ''baz'' \<mapsto> []] = {(''FORWARD'', ''foo''), (''FORWARD'', ''baz''), (''foo'', ''bar'')}"
  apply(simp add: calls_chain_def)
  apply(auto split: option.split_asm split_if_asm)
  done

lemma "wf (calls_chain [''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
          ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
          ''bar'' \<mapsto> [],
          ''baz'' \<mapsto> []])"
proof -
  have g: "calls_chain [''FORWARD'' \<mapsto> [(Rule m1 Log), (Rule m2 (Call ''foo'')), (Rule m3 Accept), (Rule m' (Call ''baz''))],
          ''foo'' \<mapsto> [(Rule m4 Log), (Rule m5 Return), (Rule m6 (Call ''bar''))], 
          ''bar'' \<mapsto> [],
          ''baz'' \<mapsto> []] = {(''FORWARD'', ''foo''), (''FORWARD'', ''baz''), (''foo'', ''bar'')}"
  by(auto simp add: calls_chain_def split: option.split_asm split_if_asm)
  show ?thesis
    unfolding g
    apply(simp)
    apply safe
     apply(erule rtranclE, simp_all)
    apply(erule rtranclE, simp_all)
    done
qed    
    

definition called_by_chain :: "'a ruleset \<Rightarrow> (string \<times> string) set" where
  "called_by_chain \<Gamma> = {(callee, caller). case \<Gamma> caller of Some rs \<Rightarrow> \<exists>m. Rule m (Call callee) \<in> set rs | None \<Rightarrow> False}"
lemma called_by_chain_converse: "calls_chain \<Gamma> = converse (called_by_chain \<Gamma>)"
  apply(simp add: calls_chain_def called_by_chain_def)
  by blast

thm acyclic_def


(*yay, we got the reverse condition*)
lemma wf_called_by_chain: "finite (calls_chain \<Gamma>) \<Longrightarrow> wf (calls_chain \<Gamma>) \<Longrightarrow> wf (called_by_chain \<Gamma>)"
  apply(frule Wellfounded.wf_acyclic)
  apply(drule(1) Wellfounded.finite_acyclic_wf_converse)
  apply(simp add: called_by_chain_converse)
  done


lemma hopefully_solves: "(\<forall>x\<in>ran \<Gamma>. wf_chain \<Gamma> x) \<Longrightarrow>
       \<forall>rsg\<in>ran \<Gamma>. \<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
       \<forall>y m. \<forall>r\<in>set rs_called. r = Rule m (Call y) \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], Undecided\<rangle> \<Rightarrow> t) \<Longrightarrow>
       wf_chain \<Gamma> rs_called \<Longrightarrow> 
       \<forall>r\<in>set rs_called. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
       (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called, Undecided\<rangle> \<Rightarrow> t) \<or>
       (\<exists>rs_called1 rs_called2 m'.
           rs_called = (rs_called1 @ [Rule m' Return] @ rs_called2) \<and>
           matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided)"
using assms proof(induction rs_called arbitrary:)
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

  (*TODO: indent properly*)
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
  case True with pre show ?thesis
    apply(simp add: r)
    apply(case_tac a)
            apply(simp_all add: a_not)
          apply(rule disjI1, rule_tac x="Decision FinalAllow" in exI)
          apply(rule_tac t="Decision FinalAllow" in seq_cons)
           apply(simp add: accept; fail)
          apply(simp add: decision; fail)
         apply(rule disjI1)
         apply(rule_tac x="Decision FinalDeny" in exI)
         apply(rule_tac t="Decision FinalDeny" in seq_cons)
          apply(simp add: drop; fail)
         apply(simp add: decision; fail)
        apply(rule disjI2)
        apply(rule_tac x="r#rs_called1" in exI)
        apply(rule_tac x=rs_called2 in exI)
        apply(rule_tac x=m' in exI)
        apply(simp add: r)
         apply(rule_tac t=Undecided in seq_cons)
         apply(simp add: r log; fail)
        apply(simp; fail)
       apply(rule disjI1)
       apply(rule_tac x="Decision FinalDeny" in exI)
       apply(rule_tac t="Decision FinalDeny" in seq_cons)
        apply(simp add: reject; fail)
       apply(simp add: decision; fail)
      apply(subgoal_tac "\<exists>a. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x5)], Undecided\<rangle> \<Rightarrow> a")
       prefer 2
       apply(rule case_call)
       apply(simp add: r; fail)
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
       apply(simp; fail)
      apply(simp add: decision; fail)
     apply(rule disjI2)
     apply(rule_tac x="[]" in exI)
     apply(rule_tac x="rs_called1 @ Rule m' Return # rs_called2" in exI)
     apply(rule_tac x=m in exI)
     apply(simp add: skip r; fail)
    apply(rule disjI2)
    apply(rule_tac x="r#rs_called1" in exI)
    apply(rule_tac x=rs_called2 in exI)
    apply(rule_tac x=m' in exI)
    apply(simp add: r)
    apply(rule_tac t=Undecided in seq_cons)
     apply(simp add: r empty; fail)
    apply(simp; fail)
    done
  qed
   
  from IH have **: "a \<noteq> Return \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> t) \<Longrightarrow> ?case"
    apply(elim disjE)
     prefer 2
     apply(simp)
     apply(elim exE)
     apply(drule *)
     apply(simp; fail)
    apply(case_tac "a \<noteq> Return")
     apply(rule disjI1)
     apply(simp add: r)
     (*apply(elim conjE)*)
     apply(elim exE, rename_tac t2 t1)
     apply(case_tac t2)
      apply(simp_all)
      apply(rule_tac x=t1 in exI)
      apply(rule_tac seq'_cons)
       apply(simp_all)
     apply (meson decision seq_cons)
    apply(case_tac "matches \<gamma> m p")
     prefer 2
     apply(rule disjI1)
     apply(elim exE)
     apply(rename_tac t')
     apply(rule_tac x=t' in exI)
     apply(rule_tac t=Undecided in seq_cons)
      apply(simp add: r nomatch; fail)
     apply(simp; fail)

     apply(rule disjI2)
     apply(rule_tac x="[]" in exI)
     apply(rule_tac x=rs in exI)
     apply(rule_tac x=m in exI)
     apply(simp add: r skip; fail)
    done
    
  thus ?case using ex_neq_ret by blast
qed

lemma helper_defined_single: "finite (calls_chain \<Gamma>) \<Longrightarrow> wf (calls_chain \<Gamma>) \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {[Rule m a]}. wf_chain \<Gamma> rsg \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {[Rule m a]}. \<forall> r \<in> set rsg. (\<not>(\<exists>chain. get_action r = Goto chain)) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
  a \<noteq> Return (*no toplevel return*) \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], s\<rangle> \<Rightarrow> t"
apply(drule(1) wf_called_by_chain)
apply(thin_tac "wf (calls_chain \<Gamma>)")
thm wf_induct_rule[where r="(calls_chain \<Gamma>)" and P="\<lambda>x. \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x)], s\<rangle> \<Rightarrow> t"]
(*apply(induction arbitrary: rule: wf_induct_rule[where r="(calls_chain \<Gamma>)"])*)
apply(simp)
apply(cases s)
 prefer 2
 apply(rename_tac decision)
 apply(rule_tac x="Decision decision" in exI)
 apply(simp)
 using iptables_bigstep.decision apply fast
apply simp
apply(case_tac "\<not> matches \<gamma> m p")
 apply(rule_tac x=Undecided in exI)
 apply(rule_tac t=s in seq'_cons)
  apply (metis empty_iff empty_set insert_iff list.simps(15) nomatch' rule.sel(1)) 
 apply(simp add: skip; fail)
apply(simp)
apply(case_tac a)
        apply(simp_all)
      apply(auto intro: iptables_bigstep.intros)[4]
  defer
  apply fastforce
 apply(auto intro: iptables_bigstep.intros)[1]
apply(rename_tac chain_name)
apply(thin_tac "a = _")
apply(subgoal_tac "\<forall>m. matches \<gamma> m p \<longrightarrow> wf_chain \<Gamma> [Rule m (Call chain_name)] \<longrightarrow> (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain_name)], s\<rangle> \<Rightarrow> t)")
 apply(simp; fail)
thm wf_induct_rule[where r="(calls_chain \<Gamma>)" and P="\<lambda>x. \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x)], s\<rangle> \<Rightarrow> t"]
apply(erule wf_induct_rule[where r="called_by_chain \<Gamma>"])
apply(simp)
(*jetz weiss ich was ueber x*)

apply(rename_tac old_name_todo chain_name) 

(*warum weiss ich nix ueber x?*)

apply(case_tac "\<Gamma> chain_name")
 apply(simp add: wf_chain_def; fail)
apply(rename_tac rs_called)
apply(intro allI impI, rename_tac m_neu)
apply(thin_tac " matches \<gamma> m p")
apply(subgoal_tac "(\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called, Undecided\<rangle> \<Rightarrow> t) \<or>
                    (\<exists>rs_called1 rs_called2 m'. \<Gamma> chain_name = Some (rs_called1@[Rule m' Return]@rs_called2) \<and>
                        matches \<gamma> m' p \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs_called1, Undecided\<rangle> \<Rightarrow> Undecided)")
 apply(elim disjE)
  apply(elim exE)
  apply(drule(2) call_result)
  apply blast
 apply(elim exE conjE)
  apply(drule(3) call_return)
  apply blast

apply(subgoal_tac "\<forall>y m. \<forall>r \<in> set rs_called. r = Rule m (Call y) \<longrightarrow> (y, chain_name) \<in> called_by_chain \<Gamma> \<and> wf_chain \<Gamma> [Rule m (Call y)]")
 prefer 2
 apply(simp)
 apply(intro impI allI conjI)
  apply(simp add: called_by_chain_def)
  apply blast
 apply(simp add: wf_chain_def)
 apply (meson ranI rule.sel(2))

(*get good IH*)
apply(subgoal_tac "\<forall>y m. \<forall>r\<in>set rs_called. r = Rule m (Call y) \<longrightarrow> (*matches \<gamma> m p \<longrightarrow>*) (\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], Undecided\<rangle> \<Rightarrow> t)")
 prefer 2
 apply(intro allI, rename_tac y my)
 apply(case_tac "matches \<gamma> my p")
  apply blast
 apply(intro ballI impI)
 apply(rule_tac x=Undecided in exI)
 apply(simp add: nomatch; fail)

apply(subgoal_tac "wf_chain \<Gamma> rs_called")
 prefer 2
 apply (simp add: ranI)

(*TODO: maybe we can continue from here :)*)

apply(elim conjE)
apply(drule(3) hopefully_solves)
 apply(simp_all)
apply(subgoal_tac "rs_called \<in> ran \<Gamma>")
 prefer 2
 apply (simp add: ranI)
by blast


lemma "finite (calls_chain \<Gamma>) \<Longrightarrow> wf (calls_chain \<Gamma>) \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. \<forall> r \<in> set rsg. (\<not>(\<exists>chain. get_action r = Goto chain)) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
  \<forall> r \<in> set rs. get_action r \<noteq> Return (*no toplevel return*) \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(rule iptables_bigstep_defined_if_singleton_rules)
apply(intro ballI, rename_tac r, case_tac r, rename_tac m a, simp)
thm helper_defined_single
apply(rule helper_defined_single)
   apply(simp_all)
  apply(simp add: wf_chain_def)
 apply fastforce
apply fastforce
done




end
