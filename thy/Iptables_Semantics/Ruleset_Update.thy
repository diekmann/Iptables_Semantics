theory Ruleset_Update
imports Matching
begin

lemma free_return_not_match: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m Return], Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<not> matches \<gamma> m p"
  using no_free_return by fast


subsection\<open>Background Ruleset Updating\<close>
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
            --\<open>@{term rs\<^sub>1} cannot be empty\<close>
            proof(cases "rs\<^sub>1")
            case Nil with Call_return(3) \<open>chain' = chain\<close> assms have "False" by simp
              thus ?Call_return_case by simp
            next
            case (Cons r\<^sub>1 rs\<^sub>1s)
            from Cons Call_return have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>r\<^sub>1 # rs\<^sub>1s, Undecided\<rangle> \<Rightarrow> Undecided" by blast
            with seqE_cons[where \<Gamma>="\<Gamma>(chain \<mapsto> rs)"] obtain ti where 
              "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[r\<^sub>1], Undecided\<rangle> \<Rightarrow> ti" and "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs\<^sub>1s, ti\<rangle> \<Rightarrow> Undecided" by metis
            with iptables_bigstep_to_undecided[where \<Gamma>="\<Gamma>(chain \<mapsto> rs)"] have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs\<^sub>1s, Undecided\<rangle> \<Rightarrow> Undecided" by fast
            with Cons Call_return \<open>chain' = chain\<close> show ?Call_return_case
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


lemma updategamma_insert_new: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> chain \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(chain \<mapsto> rs'),\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof(induction rule: iptables_bigstep_induct)
case (Call_result m a chain' rs t)
  thus ?case by (metis call_result domI fun_upd_def)
next
case Call_return
  thus ?case by (metis call_return domI fun_upd_def)
qed(auto intro: iptables_bigstep.intros)




end
