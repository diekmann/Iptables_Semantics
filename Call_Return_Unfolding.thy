theory Call_Return_Unfolding
imports Matching
begin


section{*@{term Call} @{term Return} Unfolding*}

text{*Remove @{term Return}s*}
fun process_ret :: "'a rule list \<Rightarrow> 'a rule list" where
  "process_ret [] = []" |
  "process_ret (Rule m Return # rs) = add_match (MatchNot m) (process_ret rs)" |
  "process_ret (r#rs) = r # process_ret rs"


text{*Remove @{term Call}s*}
fun process_call :: "'a ruleset \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "process_call \<Gamma> [] = []" |
  "process_call \<Gamma> (Rule m (Call chain) # rs) = add_match m (process_ret (the (\<Gamma> chain))) @ process_call \<Gamma> rs" |
  "process_call \<Gamma> (r#rs) = r # process_call \<Gamma> rs"

lemma process_ret_split_fst_Return:
  "a = Return \<Longrightarrow> process_ret (Rule m a # rs) = add_match (MatchNot m) (process_ret rs)"
  by auto

lemma process_ret_split_fst_NeqReturn:
  "a \<noteq> Return \<Longrightarrow> process_ret((Rule m a) # rs) = (Rule m a) # (process_ret rs)"
  by (cases a) auto

lemma add_match_simp: "add_match m = map (\<lambda>r. Rule (MatchAnd m (get_match r)) (get_action r))"
by (auto simp: add_match_def cong: map_cong split: rule.split)

definition add_missing_ret_unfoldings :: "'a rule list \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "add_missing_ret_unfoldings rs1 rs2 \<equiv> 
  foldr (\<lambda>rf acc. add_match (MatchNot (get_match rf)) \<circ> acc) [r\<leftarrow>rs1. get_action r = Return] id rs2"


fun MatchAnd_foldr :: "'a match_expr list \<Rightarrow> 'a match_expr" where
  "MatchAnd_foldr [] = undefined" | (*error, semantically, MatchAny would match*)
  "MatchAnd_foldr [e] = e" |
  "MatchAnd_foldr (e # es) = MatchAnd e (MatchAnd_foldr es)" 
fun add_match_MatchAnd_foldr :: "'a match_expr list \<Rightarrow> ('a rule list \<Rightarrow> 'a rule list)" where
  "add_match_MatchAnd_foldr [] = id" |
  "add_match_MatchAnd_foldr es = add_match (MatchAnd_foldr es)"

lemma add_match_add_match_MatchAnd_foldr:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (add_match_MatchAnd_foldr ms rs2), s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchAnd_foldr (m#ms)) rs2, s\<rangle> \<Rightarrow> t"
  proof (induction ms)
    case Nil
    show ?case by (simp add: add_match_def)
  next
    case Cons
    thus ?case by (simp add: iptables_bigstep_add_match_and)
  qed

lemma add_match_MatchAnd_foldr_empty_rs2: "add_match_MatchAnd_foldr ms [] = []"
  by (induction ms) (simp_all add: add_match_def)

lemma add_missing_ret_unfoldings_alt: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_missing_ret_unfoldings rs1 rs2, s\<rangle> \<Rightarrow> t \<longleftrightarrow>
  \<Gamma>,\<gamma>,p\<turnstile> \<langle>(add_match_MatchAnd_foldr (map (\<lambda>r. MatchNot (get_match r)) [r\<leftarrow>rs1. get_action r = Return])) rs2, s \<rangle> \<Rightarrow> t"
  proof(induction rs1)
    case Nil
    thus ?case
      unfolding add_missing_ret_unfoldings_def by simp
  next
    case (Cons r rs)
    from Cons obtain m a where "r = Rule m a" by(cases r) (simp)
    with Cons show ?case
      unfolding add_missing_ret_unfoldings_def
      apply(cases "matches \<gamma> m p")
       apply (simp_all add: matches_add_match_simp matches_add_match_MatchNot_simp add_match_add_match_MatchAnd_foldr[symmetric])
      done
  qed

lemma add_match_add_missing_ret_unfoldings_rot:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (add_missing_ret_unfoldings rs1 rs2), s\<rangle> \<Rightarrow> t =  
   \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_missing_ret_unfoldings (Rule (MatchNot m) Return#rs1) rs2, s\<rangle> \<Rightarrow> t"
  by(simp add: add_missing_ret_unfoldings_def iptables_bigstep_add_match_notnot_simp)


subsection{*Completeness*}
lemma process_ret_split_obvious: "process_ret (rs\<^sub>1 @ rs\<^sub>2) = 
  (process_ret rs\<^sub>1) @ (add_missing_ret_unfoldings rs\<^sub>1 (process_ret rs\<^sub>2))"
  unfolding add_missing_ret_unfoldings_def
  proof (induction rs\<^sub>1 arbitrary: rs\<^sub>2)
    case (Cons r rs)
    thus ?case
      apply(cases r)
      apply(rename_tac m a)
      apply(case_tac a)
             apply(simp_all add: add_match_split)
      done
  qed simp

lemma add_match_distrib:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
proof -
  {
    fix m1 m2
    have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m1 (add_match m2 rs), s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m2 (add_match m1 rs), s\<rangle> \<Rightarrow> t"
      proof (induction rs arbitrary: s)
        case (Cons r rs)
        thus ?case
          apply(cases r, rename_tac m a)
          apply(simp add: add_match_split_fst)
          apply(erule seqE_cons)
          apply(rule_tac t=ti in seq'_cons) (*nicht ganz*)
          apply(metis decision decisionD state.exhaust iptables_bigstep_deterministic matches.simps(1) matches_rule_and_simp nomatch) (*wtf?*)
          apply(simp)
          done
      qed (simp add: add_match_def)
  }
  thus ?thesis by blast
qed

lemma add_missing_ret_unfoldings_emptyrs2: "add_missing_ret_unfoldings rs1 [] = []"
  unfolding add_missing_ret_unfoldings_def
  by (induction rs1) (simp_all add: add_match_def)

lemma process_call_split: "process_call \<Gamma> (rs1 @ rs2) = process_call \<Gamma> rs1 @ process_call \<Gamma> rs2"
  proof (induction rs1)
    case (Cons r rs1)
    thus ?case
      apply(cases r, rename_tac m a)
      apply(case_tac a)
             apply(simp_all)
      done
  qed simp

lemma add_match_split_fst': "add_match m (a # rs) = add_match m [a] @ add_match m rs"
  by (simp add: add_match_split[symmetric])

lemma process_call_split_fst: "process_call \<Gamma> (a # rs) = process_call \<Gamma> [a] @ process_call \<Gamma> rs"
  by (simp add: process_call_split[symmetric])

lemma "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> t"
apply(induction rs)
apply(simp)
apply(rename_tac r rs)
apply(case_tac r, rename_tac m' a')
apply(case_tac a')
apply(simp_all)
apply (metis acceptD decision decisionD nomatchD seqE_cons seq_cons)
apply (metis decision decisionD dropD nomatchD seqE_cons seq_cons)
apply (metis logD nomatchD seqE_cons seq_cons)
apply (metis decision decisionD nomatchD rejectD seqE_cons seq_cons)
apply(erule seqE_cons)
apply(case_tac ti)
apply(simp)
apply(frule iptables_bigstep_to_undecided)
apply(clarsimp)
apply (metis seq'_cons)
apply(simp)
apply (metis decision iptables_bigstep_deterministic seq_cons)
apply (metis matches.simps(2) matches_add_match_simp no_free_return_seq nomatchD seq seqE_cons skip)
apply(erule seqE_cons)
apply(case_tac ti)
apply(simp)
apply (metis seq'_cons)
apply (metis decision decisionD seq'_cons)
apply(erule seqE_cons)
apply(case_tac ti)
apply(simp)
apply (metis seq'_cons)
by (metis decision iptables_bigstep_deterministic seq_cons)

lemma iptables_bigstep_process_ret_undecided: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> t"
proof (induction rs)
  case (Cons r rs)
  show ?case
    proof (cases r)
      case (Rule m' a')
      show ?thesis
        proof (cases a')
          case Accept
          with Cons Rule show ?thesis
            by simp (metis acceptD decision decisionD nomatchD seqE_cons seq_cons)
        next
          case Drop
          with Cons Rule show ?thesis
            by simp (metis decision decisionD dropD nomatchD seqE_cons seq_cons)
        next
          case Log
          with Cons Rule show ?thesis
            by simp (metis logD nomatchD seqE_cons seq_cons)
        next
          case Reject
          with Cons Rule show ?thesis
            by simp (metis decision decisionD nomatchD rejectD seqE_cons seq_cons)
        next
          case Call
          show ?thesis
            apply (insert Call Cons Rule)
            apply(erule seqE_cons)
            apply(case_tac ti)
            apply(simp)
            apply(frule iptables_bigstep_to_undecided)
            apply(clarsimp)
            apply (metis seq'_cons)
            apply(simp)
            apply (metis decision iptables_bigstep_deterministic seq_cons)
            done
        next
          case Return
          with Cons Rule show ?thesis
            by simp (metis matches.simps(2) matches_add_match_simp no_free_return_seq nomatchD seq seqE_cons skip)
        next
          case Empty
          show ?thesis
            apply (insert Empty Cons Rule)
            apply(erule seqE_cons)
            apply (rename_tac ti)
            apply(case_tac ti)
            apply (metis process_ret.simps(8) seq'_cons)
            apply (metis Rule_DecisionE emptyD state.distinct(1))
            done
        next
          case Unknown
          show ?thesis
            apply (insert Unknown Cons Rule)
            apply(erule seqE_cons)
            apply(case_tac ti)
            apply (metis process_ret.simps(9) seq'_cons)
            apply (metis decision iptables_bigstep_deterministic process_ret.simps(9) seq_cons)
            done
        qed
    qed
qed simp


lemma add_match_rot_add_missing_ret_unfoldings:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (add_missing_ret_unfoldings rs1 rs2), Undecided\<rangle> \<Rightarrow> Undecided =
   \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_missing_ret_unfoldings rs1 (add_match m rs2), Undecided\<rangle> \<Rightarrow> Undecided"
apply(simp add: add_missing_ret_unfoldings_alt add_match_add_missing_ret_unfoldings_rot add_match_add_match_MatchAnd_foldr[symmetric] iptables_bigstep_add_match_notnot_simp)
apply(cases "map (\<lambda>r. MatchNot (get_match r)) [r\<leftarrow>rs1 . (get_action r) = Return]")
 apply(simp_all add: add_match_distrib)
done

text {* Completeness *}
theorem unfolding_complete: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs,s\<rangle> \<Rightarrow> t  \<Longrightarrow>  \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_call \<Gamma> rs,s\<rangle> \<Rightarrow> t"
  proof (induction rule: iptables_bigstep_induct)
    case (Nomatch m a)
    thus ?case
      by (cases a) (auto intro: iptables_bigstep.intros simp add: not_matches_add_match_simp skip)
  next
    case Seq
    thus ?case
      by(simp add: process_call_split seq')
  next
    case (Call_return m a chain rs\<^sub>1 m' rs\<^sub>2)
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
      by simp
    hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
      by (rule iptables_bigstep_process_ret_undecided)
    with Call_return have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs\<^sub>1 @ add_missing_ret_unfoldings rs\<^sub>1 (add_match (MatchNot m') (process_ret rs\<^sub>2)), Undecided\<rangle> \<Rightarrow> Undecided"
      by (metis matches_add_match_MatchNot_simp skip add_match_rot_add_missing_ret_unfoldings seq')
    with Call_return show ?case
      by (simp add: matches_add_match_simp process_ret_split_obvious)
  next
    case Call_result
    thus ?case
      by (simp add: matches_add_match_simp iptables_bigstep_process_ret_undecided)
  qed (auto intro: iptables_bigstep.intros)



lemma process_ret_cases:
  "process_ret rs = rs \<or> (\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2 \<and> (process_ret rs) = rs\<^sub>1@(process_ret ([Rule m Return]@rs\<^sub>2)))"
  proof (induction rs)
    case (Cons r rs)
    thus ?case
      apply(cases r, rename_tac m' a')
      apply(case_tac a')
      apply(simp_all)
      apply(erule disjE,simp,rule disjI2,elim exE,simp add: process_ret_split_obvious,
        metis append_Cons process_ret_split_obvious process_ret.simps(2))+
      apply(rule disjI2)
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="rs" in exI)
      apply(rule_tac x="m'" in exI)
      apply(simp)
      apply(erule disjE,simp,rule disjI2,elim exE,simp add: process_ret_split_obvious,
        metis append_Cons process_ret_split_obvious process_ret.simps(2))+
      done
  qed simp

lemma process_ret_splitcases:
  obtains (id) "process_ret rs = rs"
        | (split) rs\<^sub>1 rs\<^sub>2 m where "rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2" and "process_ret rs = rs\<^sub>1@(process_ret ([Rule m Return]@rs\<^sub>2))"
 by (metis process_ret_cases)


lemma iptables_bigstep_process_ret_cases3_help:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> 
    (\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided) \<or>
    (\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)"
  proof (induction rs)
    case (Cons r rs)
    thus ?case
      apply(cases r, rename_tac rm ra)

      apply(case_tac "ra \<noteq> Return")
      apply(simp add: process_ret_split_fst_NeqReturn)
      apply(erule seqE_cons)
      apply(frule iptables_bigstep_to_undecided)
      apply(simp)
      apply(erule disjE)
      apply(rule disjI1)
      using seq apply fastforce
      
      apply(rule disjI2)
      apply(erule exE)+
      apply(clarify)
      apply(rule_tac x="Rule rm ra # rs\<^sub>1" in exI)
      apply(rule_tac x=rs\<^sub>2 in exI)
      apply(rule_tac x=m in exI)
      apply simp
      using seq_cons apply fast
      
      apply(simp) (*case a = Return*)
      
      apply(case_tac "matches \<gamma> rm p")
      apply(simp add: matches_add_match_MatchNot_simp skip) (*the prems becomes useless in this case*)
      apply(rule disjI2)
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="rs" in exI)
      apply(rule_tac x="rm" in exI)
      apply(simp add: skip)
      
      (*case \<not> matches*)
      apply(simp add: not_matches_add_matchNot_simp) (*get IH*)
      apply(erule disjE)
      apply(rule disjI1)
      using seq_cons nomatch apply fast
      
      (**)
      apply(rule disjI2)
      apply(clarify)
      apply(rule_tac x="Rule rm Return # rs\<^sub>1" in exI)
      apply(rule_tac x="rs\<^sub>2" in exI)
      apply(rule_tac x="m" in exI)
      apply(simp)
      using nomatch seq_cons apply fast
      done
  qed simp

lemma iptables_bigstep_process_ret_cases3:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
  obtains (noreturn) "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
        | (return) rs\<^sub>1 rs\<^sub>2 m where "rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "matches \<gamma> m p"
  using assms by (metis iptables_bigstep_process_ret_cases3_help)

lemma add_match_match_not_cases:
  "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> matches \<gamma> m p \<or> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
  by (metis matches.simps(2) matches_add_match_simp)

lemma iptables_bigstep_process_ret_DecisionD: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, s\<rangle> \<Rightarrow> Decision X \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> Decision X"
proof (induction rs arbitrary: s)
  case (Cons r rs)
  thus ?case
    apply(cases r, rename_tac m a)
    apply(clarify)

    apply(case_tac "a \<noteq> Return")
    apply(simp add: process_ret_split_fst_NeqReturn)
    apply(erule seqE_cons)
    apply(simp add: seq'_cons)

    apply(simp) (*case a = AReturn*)

    apply(case_tac "matches \<gamma> m p")
    apply(simp add: matches_add_match_MatchNot_simp skip) (*the prems becomes useless in this case*)
    apply (metis decision skipD)

    (*case \<not> matches*)
    apply(simp add: not_matches_add_matchNot_simp) (*get IH*)
    by (metis decision state.exhaust nomatch seq'_cons)
qed simp

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
          using assms apply (metis no_free_return_hlp) (*gives False*)
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
      apply(simp) (*oh wow*)
  
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

subsection{*@{const process_ret} correctness*}
lemma process_ret_add_match_dist1: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (process_ret rs), s\<rangle> \<Rightarrow> t"
apply(induction rs arbitrary: s t)
apply(simp add: add_match_def)
apply(rename_tac r rs s t)
apply(case_tac r)
apply(rename_tac m' a')
apply(simp)
apply(case_tac a')
apply(simp_all add: add_match_split_fst)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
defer
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(case_tac "matches \<gamma> (MatchNot (MatchAnd m m')) p")
apply(simp)
apply (metis decision decisionD state.exhaust matches.simps(1) matches.simps(2) matches_add_match_simp not_matches_add_match_simp)
by (metis add_match_distrib matches.simps(1) matches.simps(2) matches_add_match_MatchNot_simp)

lemma process_ret_add_match_dist2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (process_ret rs), s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), s\<rangle> \<Rightarrow> t"
apply(induction rs arbitrary: s t)
apply(simp add: add_match_def)
apply(rename_tac r rs s t)
apply(case_tac r)
apply(rename_tac m' a')
apply(simp)
apply(case_tac a')
apply(simp_all add: add_match_split_fst)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
defer
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(erule seqE_cons)
using seq' apply(fastforce)
apply(case_tac "matches \<gamma> (MatchNot (MatchAnd m m')) p")
apply(simp)
apply (metis decision decisionD state.exhaust matches.simps(1) matches.simps(2) matches_add_match_simp not_matches_add_match_simp)
by (metis add_match_distrib matches.simps(1) matches.simps(2) matches_add_match_MatchNot_simp)

(*such fuckup*)
lemma process_ret_add_match_dist: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match m (process_ret rs), s\<rangle> \<Rightarrow> t"
by (metis process_ret_add_match_dist1 process_ret_add_match_dist2)


lemma process_ret_Undecided_sound:
  assumes "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> Undecided"
  shows "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
  proof (cases "matches \<gamma> m p")
    case False
    thus ?thesis
      by (metis nomatch)
  next
    case True
    note matches = this
    show ?thesis
      using assms proof (induction rs)
        case Nil
        from call_result[OF matches, where \<Gamma>="\<Gamma>(chain \<mapsto> [])"]
        have "(\<Gamma>(chain \<mapsto> [])) chain = Some [] \<Longrightarrow> \<Gamma>(chain \<mapsto> []),\<gamma>,p\<turnstile> \<langle>[], Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> \<Gamma>(chain \<mapsto> []),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
          by simp
        thus ?case
          by (fastforce intro: skip)
      next
        case (Cons r rs)
        obtain m' a' where r: "r = Rule m' a'" by (cases r) blast

        with Cons.prems have prems: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m (Rule m' a' # rs)), Undecided\<rangle> \<Rightarrow> Undecided"
          by fast
        hence prems_simplified: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret (Rule m' a' # rs), Undecided\<rangle> \<Rightarrow> Undecided"
          using matches by (metis matches_add_match_simp process_ret_add_match_dist)

        have "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
          proof (cases "a' = Return")
            case True
            note a' = this
            have "\<Gamma>(chain \<mapsto> Rule m' Return # rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
              proof (cases "matches \<gamma> m' p")
                case True
                with matches show ?thesis
                  by (fastforce intro: call_return skip)
              next
                case False
                note matches' = this
                hence "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (Rule m' a' # rs), Undecided\<rangle> \<Rightarrow> Undecided"
                  by (metis prems_simplified update_Gamma_nomatch)
                with a' have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m') (process_ret rs), Undecided\<rangle> \<Rightarrow> Undecided"
                  by simp
                with matches matches' have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>add_match m (process_ret rs), Undecided\<rangle> \<Rightarrow> Undecided" 
                  by (simp add: matches_add_match_simp not_matches_add_matchNot_simp)
                with matches' Cons.IH show ?thesis
                  by (fastforce simp: update_Gamma_nomatch process_ret_add_match_dist)
              qed
            with a' show ?thesis
              by simp
          next
            case False
            note a' = this
            with prems_simplified have "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>Rule m' a' # process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
              by (simp add: process_ret_split_fst_NeqReturn)
            hence step: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' a'], Undecided\<rangle> \<Rightarrow> Undecided"
            and   IH_pre: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
              by (metis seqE_cons iptables_bigstep_to_undecided)+
            
            from step have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
              proof (cases rule: Rule_UndecidedE)
                case log thus ?thesis
                  using IH_pre by (metis empty iptables_bigstep.log update_Gamma_nochange1 update_Gamma_nomatch)
              next
                case call thus ?thesis
                  using IH_pre by (metis update_Gamma_remove_call_undecided)
              next
                case nomatch thus ?thesis
                  using IH_pre by (metis update_Gamma_nomatch)
              qed

            hence "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> Undecided"
              by (metis matches matches_add_match_simp process_ret_add_match_dist)
            with Cons.IH have IH: "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided"
              by fast

            from step show ?thesis
              proof (cases rule: Rule_UndecidedE)
                case log thus ?thesis using IH
                   by (simp add: update_Gamma_log_empty)
              next
                case nomatch
                thus ?thesis
                  using IH by (metis update_Gamma_nomatch)
              next
                case (call c)
                let ?\<Gamma>' = "\<Gamma>(chain \<mapsto> Rule m' a' # rs)"
                from IH_pre show ?thesis
                  proof (cases rule: iptables_bigstep_process_ret_cases3)
                    case noreturn
                    with call have "?\<Gamma>',\<gamma>,p\<turnstile> \<langle>Rule m' (Call c) # rs, Undecided\<rangle> \<Rightarrow> Undecided"
                      by (metis step seq_cons)
                    from call have "?\<Gamma>' chain = Some (Rule m' (Call c) # rs)"
                      by simp
                    from matches show ?thesis
                      by (rule call_result) fact+
                  next
                    case (return rs\<^sub>1 rs\<^sub>2 new_m')
                    with call have "?\<Gamma>' chain = Some ((Rule m' (Call c) # rs\<^sub>1) @ [Rule new_m' Return] @ rs\<^sub>2)"
                      by simp
                    from call return step have "?\<Gamma>',\<gamma>,p\<turnstile> \<langle>Rule m' (Call c) # rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided"
                      using IH_pre by (auto intro: seq_cons)
                    from matches show ?thesis
                      by (rule call_return) fact+
                  qed
              qed
          qed
        thus ?case
          by (metis r)
      qed
  qed

lemma process_ret_Decision_sound:
  assumes "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> Decision X"
  shows "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Decision X"
  proof (cases "matches \<gamma> m p")
    case False
    thus ?thesis by (metis assms state.distinct(1) not_matches_add_match_simp process_ret_add_match_dist1 skipD)
  next
    case True
    note matches = this
    show ?thesis
      using assms proof (induction rs)
        case Nil
        hence False by (metis add_match_split append_self_conv state.distinct(1) process_ret.simps(1) skipD)
        thus ?case by simp
      next
        case (Cons r rs)
        obtain m' a' where r: "r = Rule m' a'" by (cases r) blast

        with Cons.prems have prems: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m (Rule m' a' # rs)), Undecided\<rangle> \<Rightarrow> Decision X"
          by fast
        hence prems_simplified: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret (Rule m' a' # rs), Undecided\<rangle> \<Rightarrow> Decision X"
          using matches by (metis matches_add_match_simp process_ret_add_match_dist)

        have "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Decision X"
          proof (cases "a' = Return")
            case True
            note a' = this
            have "\<Gamma>(chain \<mapsto> Rule m' Return # rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> Decision X"
              proof (cases "matches \<gamma> m' p")
                case True
                with matches prems_simplified a' show ?thesis
                  by (auto simp: not_matches_add_match_simp dest: skipD)
              next
                case False
                note matches' = this
                with prems_simplified have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (Rule m' a' # rs), Undecided\<rangle> \<Rightarrow> Decision X"
                  by (metis update_Gamma_nomatch)
                with a' matches matches' have "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>add_match m (process_ret rs), Undecided\<rangle> \<Rightarrow> Decision X" 
                  by (simp add: matches_add_match_simp not_matches_add_matchNot_simp)
                with matches matches' Cons.IH show ?thesis
                  by (fastforce simp: update_Gamma_nomatch process_ret_add_match_dist matches_add_match_simp not_matches_add_matchNot_simp)
              qed
            with a' show ?thesis
              by simp
          next
            case False
            with prems_simplified obtain ti
              where step: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>[Rule m' a'], Undecided\<rangle> \<Rightarrow> ti"
                and IH_pre: "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>process_ret rs, ti\<rangle> \<Rightarrow> Decision X"
              by (auto simp: process_ret_split_fst_NeqReturn elim: seqE_cons)

            hence "\<Gamma>(chain \<mapsto> Rule m' a' # rs),\<gamma>,p\<turnstile> \<langle>rs, ti\<rangle> \<Rightarrow> Decision X"
              by (metis iptables_bigstep_process_ret_DecisionD)

            thus ?thesis
              using matches step by (force intro: call_result seq'_cons)
          qed
        thus ?case
          by (metis r)
      qed
  qed

lemma process_ret_result_empty: "[] = process_ret rs \<Longrightarrow> \<forall>r \<in> set rs. get_action r = Return"
  proof (induction rs)
    case (Cons r rs)
    thus ?case
      apply(simp)
      apply(case_tac r)
      apply(rename_tac m a)
      apply(case_tac a)
      apply(simp_all add: add_match_def)
      done
  qed simp

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


lemma process_ret_sound':
  assumes "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> t"
  shows "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"
using assms by (metis state.exhaust process_ret_Undecided_sound process_ret_Decision_sound)

lemma get_action_case_simp: "get_action (case r of Rule m' x \<Rightarrow> Rule (MatchAnd m m') x) = get_action r"
by (metis rule.case_eq_if rule.sel(2))

text{*
  We call a ruleset wf iff all Calls are into actually existing chains.
*}
definition wf_chain :: "'a ruleset \<Rightarrow> 'a rule list \<Rightarrow> bool" where
  "wf_chain \<Gamma> rs \<equiv> (\<forall>r \<in> set rs. \<forall> chain. get_action r = Call chain \<longrightarrow> \<Gamma> chain \<noteq> None)"
lemma wf_chain_append: "wf_chain \<Gamma> (rs1@rs2) \<longleftrightarrow> wf_chain \<Gamma> rs1 \<and> wf_chain \<Gamma> rs2"
  by(simp add: wf_chain_def, blast)
lemma wf_chain_process_ret: "wf_chain \<Gamma> rs \<Longrightarrow> wf_chain \<Gamma> (process_ret rs)"
  apply(induction rs)
  apply(simp add: wf_chain_def add_match_def)
  apply(case_tac a)
  apply(case_tac "x2 \<noteq> Return")
  apply(simp add: process_ret_split_fst_NeqReturn)
  using wf_chain_append apply (metis Cons_eq_appendI append_Nil)
  apply(simp add: process_ret_split_fst_Return)
  apply(simp add: wf_chain_def add_match_def get_action_case_simp)
  done
lemma wf_chain_add_match: "wf_chain \<Gamma> rs \<Longrightarrow> wf_chain \<Gamma> (add_match m rs)"
  by(induction rs) (simp_all add: wf_chain_def add_match_def get_action_case_simp)

subsection{* Soundness *}
theorem unfolding_sound: "wf_chain \<Gamma> rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_call \<Gamma> rs, s\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
proof (induction rs arbitrary: s t)
  case (Cons r rs)
  thus ?case
    apply -
    apply(subst(asm) process_call_split_fst)
    apply(erule seqE)

    unfolding wf_chain_def
    apply(case_tac r, rename_tac m a)
    apply(case_tac a)
    apply(simp_all add: seq'_cons)

    apply(case_tac s)
    defer
    apply (metis decision decisionD)
    apply(case_tac "matches \<gamma> m p")
    defer
    apply(simp add: not_matches_add_match_simp)
    apply(drule skipD, simp)
    apply (metis nomatch seq_cons)
    apply(clarify)
    apply(simp add: matches_add_match_simp)
    apply(rule_tac t=ti in seq_cons)
    apply(simp_all)

    using process_ret_sound'
    by (metis fun_upd_triv matches_add_match_simp process_ret_add_match_dist)
qed simp

corollary unfolding_sound_complete: "wf_chain \<Gamma> rs \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_call \<Gamma> rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
by (metis unfolding_complete unfolding_sound)

corollary unfolding_n_sound_complete: "\<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>((process_call \<Gamma>)^^n) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
  proof(induction n arbitrary: rs)
    case 0 thus ?case by simp
  next
    case (Suc n)
      from Suc have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>(process_call \<Gamma> ^^ n) rs, s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" by blast
      from Suc.prems have "\<forall>a\<in>ran \<Gamma> \<union> {process_call \<Gamma> rs}. wf_chain \<Gamma> a"
        proof(induction rs)
          case Nil thus ?case by simp
        next
          case(Cons r rs)
            from Cons.prems have "\<forall>a\<in>ran \<Gamma>. wf_chain \<Gamma> a" by blast
            from Cons.prems have "wf_chain \<Gamma> [r]"
              apply(simp)
              apply(clarify)
              apply(simp add: wf_chain_def)
              done
            from Cons.prems have "wf_chain \<Gamma> rs"
              apply(simp)
              apply(clarify)
              apply(simp add: wf_chain_def)
              done
            from this Cons.prems Cons.IH have "wf_chain \<Gamma> (process_call \<Gamma> rs)" by blast
            from this `wf_chain \<Gamma> [r]`have "wf_chain \<Gamma> (r # (process_call \<Gamma> rs))" by(simp add: wf_chain_def)
            from this Cons.prems have "wf_chain \<Gamma> (process_call \<Gamma> (r#rs))"
              apply(cases r)
              apply(rename_tac m a, clarify)
              apply(case_tac a)
              apply(simp_all)
              apply(simp add: wf_chain_append)
              apply(clarify)
              apply(simp add: `wf_chain \<Gamma> (process_call \<Gamma> rs)`)
              apply(rule wf_chain_add_match)
              apply(rule wf_chain_process_ret)
              apply(simp add: wf_chain_def)
              apply(clarify)
              by (metis ranI option.sel)
          from this `\<forall>a\<in>ran \<Gamma>. wf_chain \<Gamma> a` show ?case by simp
        qed
      from this Suc.IH[of "((process_call \<Gamma>) rs)"] have 
        "\<Gamma>,\<gamma>,p\<turnstile> \<langle>(process_call \<Gamma> ^^ n) (process_call \<Gamma> rs), s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_call \<Gamma> rs, s\<rangle> \<Rightarrow> t"
        by simp
    from this show ?case
      by (simp, metis Suc.prems Un_commute funpow_swap1 insertI1 insert_is_Un unfolding_sound_complete)
  qed


text_raw{*
\begin{verbatim}
loops in the linux kernel:
http://lxr.linux.no/linux+v3.2/net/ipv4/netfilter/ip_tables.c#L464
/* Figures out from what hook each rule can be called: returns 0 if
   there are loops.  Puts hook bitmask in comefrom. */
   static int mark_source_chains(const struct xt_table_info *newinfo,
                   unsigned int valid_hooks, void *entry0)

discussion: http://marc.info/?l=netfilter-devel&m=105190848425334&w=2
\end{verbatim}
*}

end
