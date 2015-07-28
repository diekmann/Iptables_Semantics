theory Ruleset_Update
imports Matching
begin


(*TODO: move*)
lemma add_match_distrib:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
proof -
  {
    fix m1 m2
    have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
      proof (induction rs arbitrary: s)
        case Nil thus ?case by (simp add: add_match_def)
        next
        case (Cons r rs)
        from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
        with Cons.prems obtain ti where 1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m1 (MatchAnd m2 m)) a], s\<rangle> \<Rightarrow> ti" and 2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), ti\<rangle> \<Rightarrow> t"
          apply(simp add: add_match_split_fst)
          apply(erule seqE_cons)
          by simp
        from 1 r have base: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule (MatchAnd m2 (MatchAnd m1 m)) a], s\<rangle> \<Rightarrow> ti"
           by (metis matches.simps(1) matches_rule_iptables_bigstep)
        from 2 Cons.IH have IH: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), ti\<rangle> \<Rightarrow> t" by simp
        from base IH seq'_cons have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule (MatchAnd m2 (MatchAnd m1 m)) a # add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t" by fast
        thus ?case using r by(simp add: add_match_split_fst[symmetric])
      qed
  }
  thus ?thesis by blast
qed

lemma add_match_split_fst': "add_match m (a # rs) = add_match m [a] @ add_match m rs"
  by (simp add: add_match_split[symmetric])


lemma add_match_match_not_cases:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> matches \<gamma> m p \<or> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  by (metis matches.simps(2) matches_add_match_simp)

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









(* only failed proofs below *)


thm finite_induct

definition ruleset_assms :: "'a ruleset \<Rightarrow> bool" where
  "ruleset_assms \<Gamma> \<equiv> \<forall>rsg \<in> ran \<Gamma>. wf_chain \<Gamma> rsg \<and> (\<forall> r \<in> set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"

lemma assumes (*Gamma: "\<Gamma> = map_of xs" and*) ruleset_assms: "ruleset_assms \<Gamma>" and Gamma_chain: "\<Gamma> name = Some rs"
  shows "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
using Gamma_chain ruleset_assms proof(induction rs arbitrary: \<Gamma> name)
case Nil thus ?case
 apply(rule_tac x=s in exI)
 apply(simp add: skip)
 done
next
case(Cons r rs)
  let ?\<Gamma>''="\<lambda>n. if n = name then Some (tl (the (\<Gamma> name))) else \<Gamma> n"
  let ?\<Gamma>'="\<lambda>n. if n = name then Some rs else \<Gamma> n"
  from `\<Gamma> name = Some (r#rs)` have x: "(tl (the (\<Gamma> name))) = rs" by simp
  have "?\<Gamma>'' = ?\<Gamma>'" using x by auto
  have y: "ran ?\<Gamma>' \<subseteq> ran \<Gamma> \<union> {rs}"
    apply(simp add: ran_def)
    by blast
  { fix P
    assume P: "\<forall>rsg\<in>ran \<Gamma>. (\<forall>r\<in>set rsg. P r)"
    from `\<Gamma> name = Some (r # rs)` have "(r # rs) \<in> ran \<Gamma>" using Map.ranI by fast
    with P have "(\<forall>r \<in> set rs. P r)" by fastforce
  }note all_r_rs=this
  have all_ran_splitand: "\<And>P Q. \<forall>rsg\<in>ran \<Gamma>. P rsg \<and> Q rsg \<Longrightarrow> (\<forall>rsg\<in>ran \<Gamma>. P rsg) \<and> (\<forall>rsg\<in>ran \<Gamma>. Q rsg)" by blast
  from `ruleset_assms \<Gamma>` have "wf_chain ?\<Gamma>' rs \<and> (\<forall>r\<in>set rs. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
    apply -
    apply(rule conjI)
     apply(simp_all add: ruleset_assms_def)
     apply(drule all_ran_splitand)
     apply(simp add: wf_chain_def)
     using all_r_rs apply auto[1]
    apply(drule all_ran_splitand)
    using all_r_rs apply auto[1]
    done
  with `ruleset_assms \<Gamma>` have "\<forall>rsg\<in>ran \<Gamma> \<union> {rs}.
       wf_chain (\<lambda>n. if n = name then Some rs else \<Gamma> n) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
    apply(simp add: ruleset_assms_def)
    apply(simp add: wf_chain_def)
    done
  hence "ruleset_assms ?\<Gamma>'"
    apply(simp add: ruleset_assms_def)
    using y by blast
  with Cons.prems Cons.IH[of ?\<Gamma>' name] have "\<exists>a. ?\<Gamma>',\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> a" by simp
  thus ?case
apply -
apply(elim exE)
apply(rename_tac t')
apply(case_tac r)
apply(rename_tac m a)
apply(simp)
apply(case_tac "\<not> matches \<gamma> m p")
 apply(rule_tac x=t' in exI)
 apply(rule_tac t=s in seq'_cons)
  apply (metis empty_iff empty_set insert_iff list.simps(15) nomatch' rule.sel(1))
  
oops


lemma ran_gammaupdate_subset: "ran (\<Gamma>(chain \<mapsto> rs)) \<subseteq> ran (\<Gamma>(chain \<mapsto> r#rs)) \<union> {rs}"
  apply(simp add: ran_def)
  by blast

lemma ruleset_assms_gammaupdate_fst: "ruleset_assms (\<Gamma>(chain \<mapsto> r # rs)) \<Longrightarrow> ruleset_assms (\<Gamma>(chain \<mapsto> rs))"
unfolding ruleset_assms_def
proof -
  fix rsg :: "'a rule list"
  assume 1: "\<forall>rsg\<in>ran (\<Gamma>(chain \<mapsto> r # rs)). wf_chain (\<Gamma>(chain \<mapsto> r # rs)) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
  hence "\<forall>rsg\<in>ran (\<Gamma>(chain \<mapsto> r # rs)) \<union> {rs}. wf_chain (\<Gamma>(chain \<mapsto> r # rs)) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
    proof(simp, intro conjI)
      assume a: "\<forall>rsg\<in>ran (\<Gamma>(chain \<mapsto> r # rs)). wf_chain (\<Gamma>(chain \<mapsto> r # rs)) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
      have "r#rs \<in> ran (\<Gamma>(chain \<mapsto> r # rs))"
        apply(intro Map.ranI)
        by auto
      with a have "wf_chain (\<Gamma>(chain \<mapsto> r # rs)) (r#rs)" by simp
      thus "wf_chain (\<Gamma>(chain \<mapsto> r # rs)) rs" by(simp add: wf_chain_fst)
    next
      assume a: "\<forall>rsg\<in>ran (\<Gamma>(chain \<mapsto> r # rs)). wf_chain (\<Gamma>(chain \<mapsto> r # rs)) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
      thus "\<forall>r\<in>set rs. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown"
      by (metis fun_upd_same insert_iff list.simps(15) ranI)
    qed
  from this ran_gammaupdate_subset
  show "\<forall> rsg \<in> ran (\<Gamma>(chain \<mapsto> rs)). wf_chain (\<Gamma>(chain \<mapsto> rs)) rsg \<and> (\<forall>r\<in>set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown)"
  by (smt fun_upd_def option.distinct(1) subsetCE wf_chain_def) (*TODO*)
qed


lemma ruleset_assms_gammaupdate_ex_rsX: 
  "ruleset_assms (\<Gamma>(chain \<mapsto> Rule m (Call chain_name) # rs)) \<Longrightarrow> \<exists>rsX. (\<Gamma>(chain \<mapsto> Rule m (Call chain_name) # rs)) chain_name = Some rsX"
  apply(simp add: ruleset_assms_def wf_chain_def)
  by (meson fun_upd_same list.set_intros(1) ranI rule.sel(2))
  

lemma assumes ruleset_assms: "ruleset_assms (\<Gamma>(chain \<mapsto> rs))"
  shows "\<exists>t. \<Gamma>(chain \<mapsto> rs(*'*)),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t" (*Undecided = s*)
using ruleset_assms proof(induction rs arbitrary: chain )
case Nil thus ?case
 apply(rule_tac x=Undecided in exI)
 apply(simp add: skip)
 done
next
case(Cons r rs)
  from ruleset_assms_gammaupdate_fst Cons.prems Cons.IH have "\<exists>a. \<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> a" by blast
  thus ?case
apply(elim exE)
apply(rename_tac t')
apply(case_tac r)
apply(rename_tac m a)
apply(simp)
apply(case_tac "\<not> matches \<gamma> m p")
 apply(rule_tac x=t' in exI)
 apply(rule_tac t=Undecided in seq'_cons)
  apply (simp add: nomatch)
 apply (simp add: map_update_chain_if update_Gamma_nomatch; fail)
apply(simp)
apply(simp add: map_update_chain_if)


apply(case_tac a)
apply(simp_all)
 apply(rule_tac x="Decision FinalAllow" in exI)
 apply(rule_tac t="Decision FinalAllow" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 apply(rule_tac x="Decision FinalDeny" in exI)
 apply(rule_tac t="Decision FinalDeny" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 apply(rule_tac x=t' in exI)
 apply(rule_tac t=Undecided in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]
 apply (simp add: update_Gamma_log_empty)

 apply(rule_tac x="Decision FinalDeny" in exI)
 apply(rule_tac t="Decision FinalDeny" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]


(** here we need something about the call**)
 apply(rename_tac chain_name)
 apply (insert Cons.prems, simp add: map_update_chain_if)

 apply(subgoal_tac "\<exists> rsX. (\<Gamma>(chain \<mapsto> Rule m (Call chain_name) # rs)) chain_name = Some rsX")
  prefer 2
  using ruleset_assms_gammaupdate_ex_rsX apply blast
 apply(elim exE, rename_tac rsX)
 apply(subgoal_tac "(\<Gamma>(chain \<mapsto> Rule m (Call chain_name) # rs)),\<gamma>,p\<turnstile> \<langle>rsX, Undecided\<rangle> \<Rightarrow> t''")(*sorry*)
 thm call_result
 apply(drule(2) call_result)
  apply(rule_tac x="t''" in exI)
  apply(rule_tac t=t'' in seq'_cons)
  apply blast
  apply(auto intro: iptables_bigstep.intros)[1]

(*IT IS IMPOSSIBLE TO SOLVE THE RETURN CASE ANYWAY*)

oops


(*
lemma "\<Gamma> = map_of xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow>
  \<forall>chainnames \<in> dom \<Gamma>. some_validity_condition chainnames \<Longrightarrow>
  \<forall> r \<in> set rs. get_action r \<noteq> Return (*no toplevel return*) \<and> get_action r \<noteq> Unknown \<and>
                (\<forall>c. get_action r \<noteq> Goto c) \<and> (\<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom \<Gamma>) \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t"
proof(induction xs arbitrary: \<Gamma> rs)
case Nil thus ?case
  apply(simp)
  (*with \<Gamma>=map.Empty, this hopefully follows from semantics_bigstep_defined*)
  sorry
next
case (Cons x xs)
  have some_validity_condition: "\<forall>a\<in>dom (map_of xs). some_validity_condition a" sorry
  with Cons.IH[of "map_of xs"] Cons.prems have IH: "\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of xs) \<Longrightarrow> \<exists>t. map_of xs,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t" by simp
  from Cons.prems have "\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of (x#xs))" by meson
  have 1: "\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of xs) \<Longrightarrow> ?case"
    apply(drule IH)
    apply(simp add: Cons.prems map_update_chain_if)
    apply(elim exE)
    apply(rename_tac t)
    apply(rule_tac x=t in exI)
    apply(rule updategamma_insert_new)
     apply(simp)
    using Cons.prems(2) by (simp add: dom_map_of_conv_image_fst) 

  from Cons have "\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of (x # xs))" by blast
  hence x: "(\<not> (\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of xs))) \<longleftrightarrow>
    (\<exists> r \<in> set rs. get_action r = Call (fst x))"
    apply -
    apply(rule iffI)
     apply fastforce
    by (metis Cons.prems(2) distinct.simps(2) dom_map_of_conv_image_fst list.simps(9) set_map)

  (*{ fix chain_name m chain
    assume m: "matches \<gamma> m p" and "chain_name \<in> dom (map_of xs)"

    have "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain_name)], Undecided\<rangle> \<Rightarrow> t"

  }*)
  
  { fix chain_name m chain
    assume m: "matches \<gamma> m p" and "chain_name \<in> dom (map_of (x # xs))" and x: "x = (chain_name, chain)"

    have "\<Gamma> = map_of (x # xs)" using Cons.prems by blast
    hence "\<Gamma> chain_name = Some chain" using x by simp

    have "\<Gamma>(chain_name \<mapsto> chain) = \<Gamma>" by (simp add: `\<Gamma> chain_name = Some chain` fun_upd_idem_iff)

    thm no_recursive_calls_helper
    thm call_result[OF m, of \<Gamma> chain_name "process_ret (add_match m chain)"] (*use those 2 below!*)
    thm process_ret_Decision_sound[of \<Gamma> chain_name chain \<gamma> p m]
    thm process_ret_Undecided_sound[of \<Gamma> chain_name chain \<gamma> p m]

    (*\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> Undecided*)

    (*remaining precondition must hopefully follow from some_validity_condition*)
    from Cons.IH[of "map_of xs" "process_ret (add_match m chain)"] some_validity_condition Cons.prems have "
      \<forall>r\<in>set (process_ret (add_match m chain)).
        get_action r \<noteq> Return \<and> get_action r \<noteq> Unknown \<and> (\<forall>c. get_action r \<noteq> Goto c) \<and> (\<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of xs)) \<Longrightarrow>
      \<exists>t. map_of xs,\<gamma>,p\<turnstile> \<langle>process_ret (add_match m chain), Undecided\<rangle> \<Rightarrow> t" by simp

    (*Problem: (\<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of xs))*)
    
    have "\<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain_name)], Undecided\<rangle> \<Rightarrow> t" sorry
  }

  (*vielversprechend*)

  show ?case
   (*apply(cases "\<not> (\<exists> r \<in> set rs. get_action r = Call (fst x))")
    apply(subst(asm) x[symmetric])
    using 1 apply blast
   apply(simp)*)
   apply(rule iptables_bigstep_defined_if_singleton_rules)
   apply(intro ballI, rename_tac r)

   apply(case_tac r)
   apply(rename_tac m a)
apply(case_tac "\<not> matches \<gamma> m p")
 apply(rule_tac x=Undecided in exI)
 using nomatch' apply force

apply(simp)

apply(case_tac a)
apply(simp_all)
 apply(auto intro: iptables_bigstep.intros)[4]
 prefer 4
 apply(auto intro: iptables_bigstep.intros)[1]

 defer
 using Cons.prems(4) rule.sel(2) apply blast
 using Cons.prems(4) rule.sel(2) apply blast
 using Cons.prems(4) rule.sel(2) apply blast

(** here we need something about the call**)
 apply(rename_tac chain_name)
 apply(subgoal_tac "chain_name \<in> dom (map_of (x#xs))")
  prefer 2 using `\<forall>r\<in>set rs. \<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom (map_of (x # xs))` rule.sel(2) apply blast
 apply(case_tac "chain_name = fst x")

 defer
 apply(subgoal_tac "chain_name \<in> dom (map_of xs)") 
  prefer 2 apply force
 

 (*arbitrary rs nutzen?*)
 defer
 
oops
*)



definition some_validity_condition :: "'a ruleset \<Rightarrow> bool" where
  "some_validity_condition \<Gamma> \<equiv> \<forall>chainname \<in> dom \<Gamma>. \<forall>r \<in> set (the (\<Gamma> chainname)).
      get_action r \<noteq> Unknown \<and>
      (\<forall>c. get_action r \<noteq> Goto c) \<and>
      (\<forall>c. get_action r = Call c \<longrightarrow> c \<in> dom \<Gamma>)"

lemma helper_obtain_from_Gamma: assumes "c \<in> dom \<Gamma>" obtains rs where "\<Gamma> c = Some rs" using assms by blast
lemma some_validity_condition_update_new:
  "some_validity_condition (\<Gamma>(chain \<mapsto> rs')) \<Longrightarrow> chain \<notin> dom \<Gamma> \<Longrightarrow>
    \<forall>rs \<in> ran \<Gamma>. \<forall>r \<in> set rs. \<forall>c. get_action r \<noteq> Call chain \<Longrightarrow> (* only true if all rules in \<Gamma> do not reference chain *)
    some_validity_condition \<Gamma>"
  apply(simp add: some_validity_condition_def)
  apply(elim conjE)
  apply(thin_tac "\<forall>r\<in>set rs'. P r rs'" for P) (*don't need updated*)
  apply(intro ballI conjI)
    apply(rename_tac c r)
    apply(erule_tac x=c in ballE, simp_all)
    apply(erule helper_obtain_from_Gamma, simp)
    apply(erule_tac x=r in ballE, simp)
    apply (metis (mono_tags, lifting) domI option.sel)
   apply(rename_tac c r)
   apply(erule_tac x=c in ballE, simp_all)
   apply(erule helper_obtain_from_Gamma, simp)
   apply(erule_tac x=r in ballE, simp)
   apply (metis (mono_tags, lifting) domI option.sel)
  apply(rename_tac c r)
  apply(intro allI impI, rename_tac c')
  apply(subgoal_tac " c' = chain \<or> c' \<in> dom \<Gamma>")
   prefer 2
   apply(erule_tac x=c in ballE, simp_all)
   apply(erule helper_obtain_from_Gamma, simp)
   apply (smt domI option.sel) (*SMT !*)
  apply(elim disjE, simp_all)
  by (metis domIff option.collapse ranI)



(*
lemma "\<Gamma> = map_of xs \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma>. wf_chain \<Gamma> rsg \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma>. \<forall> r \<in> set rsg. (\<forall>chain. get_action r \<noteq> Goto chain) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
  \<Gamma> name = Some rs \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(induction xs arbitrary: \<Gamma>)
 apply(simp)
apply(simp)
apply(rename_tac x xs \<Gamma>)
apply(case_tac x)
apply(rename_tac name' rs')
apply(simp)
apply(subgoal_tac "Ex (iptables_bigstep (map_of xs) \<gamma> p rs s)")
prefer 2
apply(case_tac "name = name'")
 apply(simp)
 
(*
  finite (dom \<Gamma>) \<Longrightarrow> (*finite induct?*)
  finite (ran \<Gamma>) \<Longrightarrow> (*finite induct?*)
*)
(*apply(rotate_tac 4)
apply(induction "(ran \<Gamma>)" arbitrary: \<Gamma> rule: finite_induct)
 apply(simp_all)
 using ranI apply fastforce*)
apply(simp)
apply(rename_tac name' \<Gamma>' \<Gamma>)
apply(case_tac "name = name'")
apply(subgoal_tac "Ex (iptables_bigstep \<Gamma>' \<gamma> p rs s)")
defer
try0
oops
*)

(*Scratch: showing that semantics are defined*)
definition calls_chain :: "'a ruleset \<Rightarrow> (string \<times> string) set" where
  "calls_chain \<Gamma> = {(r, s). case \<Gamma> r of Some rs \<Rightarrow> \<exists>m. Rule m (Call s) \<in> set rs | None \<Rightarrow> False}"
thm wf_induct
thm wf_induct_rule


lemma "\<exists>y. (y, chain_name) \<in> calls_chain \<Gamma> \<Longrightarrow> (\<And>y. (y, chain_name) \<in> calls_chain \<Gamma> \<Longrightarrow> Ex (iptables_bigstep \<Gamma> \<gamma> p rs s)) \<Longrightarrow>
   Ex (iptables_bigstep \<Gamma> \<gamma> p rs s)"
by blast


lemma "wf (calls_chain \<Gamma>) \<Longrightarrow>
  (x, y) \<in> calls_chain \<Gamma> \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call y)], s\<rangle> \<Rightarrow> t \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m (Call x)], s\<rangle> \<Rightarrow> t"
apply(induction rule: wf_induct_rule)
apply(simp)

oops

lemma "wf (calls_chain \<Gamma>) \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow>
  \<forall>rsg \<in> ran \<Gamma> \<union> {rs}. \<forall> r \<in> set rsg. (\<not>(\<exists>chain. get_action r = Goto chain)) \<and> get_action r \<noteq> Unknown \<Longrightarrow>
  \<forall> r \<in> set rs. get_action r \<noteq> Return (*no toplevel return*) \<Longrightarrow>
  \<exists>t. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
apply(simp)
apply(induction rs)
 apply(simp_all)
 apply(rule_tac x=s in exI)
 apply(simp add: skip)

apply(rename_tac r rs)
apply(elim conjE)
apply(simp add: wf_chain_fst)

apply(elim exE)
apply(rename_tac t')
apply(case_tac r)
apply(rename_tac m a)
apply(simp)
apply(case_tac "\<not> matches \<gamma> m p")
 apply(rule_tac x=t' in exI)
 apply(rule_tac t=s in seq'_cons)
  apply (metis empty_iff empty_set insert_iff list.simps(15) nomatch' rule.sel(1)) 
 apply(simp)
apply(simp)
apply(case_tac s)
 prefer 2
 apply(simp)
 apply(rule_tac x="Decision x2" in exI)
 apply(simp add: decision)
apply(simp)
apply(case_tac a)
apply(simp_all)
 apply(rule_tac x="Decision FinalAllow" in exI)
 apply(rule_tac t="Decision FinalAllow" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 apply(rule_tac x="Decision FinalDeny" in exI)
 apply(rule_tac t="Decision FinalDeny" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 apply(rule_tac x=t' in exI)
 apply(rule_tac t=Undecided in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 apply(rule_tac x="Decision FinalDeny" in exI)
 apply(rule_tac t="Decision FinalDeny" in seq'_cons)
 apply(auto intro: iptables_bigstep.intros)[2]

 prefer 2 apply fast

apply(erule_tac r="(calls_chain \<Gamma>)" in wf_induct_rule)
apply(rename_tac chain_name chain_name_x)

(** here we need something about the return**)
oops

end
