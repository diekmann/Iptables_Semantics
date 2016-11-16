theory Call_Return_Unfolding
imports Matching Ruleset_Update
  "Common/Repeat_Stabilize"
begin


section\<open>@{term Call} @{term Return} Unfolding\<close>

text\<open>Remove @{term Return}s\<close>
fun process_ret :: "'a rule list \<Rightarrow> 'a rule list" where
  "process_ret [] = []" |
  "process_ret (Rule m Return # rs) = add_match (MatchNot m) (process_ret rs)" |
  "process_ret (r#rs) = r # process_ret rs"


text\<open>Remove @{term Call}s\<close>
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


subsection\<open>Completeness\<close>
lemma process_ret_split_obvious: "process_ret (rs\<^sub>1 @ rs\<^sub>2) = 
  (process_ret rs\<^sub>1) @ (add_missing_ret_unfoldings rs\<^sub>1 (process_ret rs\<^sub>2))"
  unfolding add_missing_ret_unfoldings_def
  proof (induction rs\<^sub>1 arbitrary: rs\<^sub>2)
    case (Cons r rs)
    from Cons obtain m a where "r = Rule m a" by (cases r) simp
    with Cons.IH show ?case
      apply(cases a)
             apply(simp_all add: add_match_split)
      done
  qed simp

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

lemma process_call_split_fst: "process_call \<Gamma> (a # rs) = process_call \<Gamma> [a] @ process_call \<Gamma> rs"
  by (simp add: process_call_split[symmetric])


lemma iptables_bigstep_process_ret_undecided: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> t"
proof (induction rs)
  case (Cons r rs)
  show ?case
    proof (cases r)
      case (Rule m' a')
      show "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret (r # rs), Undecided\<rangle> \<Rightarrow> t"
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
          case (Call chain)
          from Cons.prems obtain ti where 1:"\<Gamma>,\<gamma>,p\<turnstile> \<langle>[r], Undecided\<rangle> \<Rightarrow> ti" and 2: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, ti\<rangle> \<Rightarrow> t" using seqE_cons by metis
          thus ?thesis
            proof(cases ti)
            case Undecided
              with Cons.IH 2 have IH: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> t" by simp
              from Undecided 1 Call Rule have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain)], Undecided\<rangle> \<Rightarrow> Undecided" by simp
              with IH  have" \<Gamma>,\<gamma>,p\<turnstile> \<langle>Rule m' (Call chain) # process_ret rs, Undecided\<rangle> \<Rightarrow> t" using seq'_cons by fast
              thus ?thesis using Rule Call by force
            next
            case (Decision X)
              with 1 Rule Call have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m' (Call chain)], Undecided\<rangle> \<Rightarrow> Decision X" by simp
              moreover from 2 Decision have "t = Decision X" using decisionD by fast
              moreover from decision have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Decision X\<rangle> \<Rightarrow> Decision X" by fast
              ultimately show ?thesis using seq_cons by (metis Call Rule process_ret.simps(7))
            qed
        next
          case Return
          with Cons Rule show ?thesis
            by simp (metis matches.simps(2) matches_add_match_simp no_free_return nomatchD seqE_cons)
        next
          case Empty
          show ?thesis 
            apply (insert Empty Cons Rule)
            apply(erule seqE_cons)
            apply (rename_tac ti)
            apply(case_tac ti)
             apply (simp add: seq_cons)
            apply (metis Rule_DecisionE emptyD state.distinct(1))
            done
        next
          case Unknown
          show ?thesis using Unknown_actions_False
            by (metis Cons.IH Cons.prems Rule Unknown nomatchD process_ret.simps(10) seqE_cons seq_cons)
        next
          case Goto thus ?thesis  using Unknown_actions_False
            by (metis Cons.IH Cons.prems Rule Goto nomatchD process_ret.simps(8) seqE_cons seq_cons) 
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

text \<open>Completeness\<close>
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


lemma iptables_bigstep_process_ret_cases3:
  assumes "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
  obtains (noreturn) "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
        | (return) rs\<^sub>1 rs\<^sub>2 m where "rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2" "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" "matches \<gamma> m p"
proof -
  have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> 
    (\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided) \<or>
    (\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1@[Rule m Return]@rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)"
  proof (induction rs)
    case Nil thus ?case by simp
    next
    case (Cons r rs)
    from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
    from r Cons show ?case
      proof(cases "a \<noteq> Return")
        case True
        with r Cons.prems have prems_r: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>[Rule m a], Undecided\<rangle> \<Rightarrow> Undecided " and prems_rs: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided"
         apply(simp_all add: process_ret_split_fst_NeqReturn)
         apply(erule seqE_cons, frule iptables_bigstep_to_undecided, simp)+
         done
        from prems_rs Cons.IH have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<or>
                      (\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)" by simp
        thus "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> Undecided \<or> (\<exists>rs\<^sub>1 rs\<^sub>2 m. r # rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)"
          proof(elim disjE)
            assume "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
            hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> Undecided" using prems_r by (metis r seq'_cons) 
            thus ?thesis by simp
          next
            assume "(\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)"
            from this obtain rs\<^sub>1 rs\<^sub>2 m' where "rs = rs\<^sub>1 @ [Rule m' Return] @ rs\<^sub>2" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" and "matches \<gamma> m' p" by blast
            hence "\<exists>rs\<^sub>1 rs\<^sub>2 m. r # rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p"
              apply(rule_tac x="Rule m a # rs\<^sub>1" in exI)
              apply(rule_tac x=rs\<^sub>2 in exI)
              apply(rule_tac x=m' in exI)
              apply(simp add: r)
              using prems_r seq'_cons by fast
            thus ?thesis by simp
          qed
      next
      case False
        hence "a = Return" by simp
        with Cons.prems r have prems: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>add_match (MatchNot m) (process_ret rs), Undecided\<rangle> \<Rightarrow> Undecided" by simp
        show "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> Undecided \<or> (\<exists>rs\<^sub>1 rs\<^sub>2 m. r # rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)"
          proof(cases "matches \<gamma> m p")
          case True
            (*the Cons premises are useless in this case*)
            hence "\<exists>rs\<^sub>1 rs\<^sub>2 m. r # rs = rs\<^sub>1 @ Rule m Return # rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p"
               apply(rule_tac x="[]" in exI)
               apply(rule_tac x="rs" in exI)
               apply(rule_tac x="m" in exI)
               apply(simp add: skip r \<open>a = Return\<close>)
               done
            thus ?thesis by simp
          next
          case False
            with nomatch seq_cons False r have r_nomatch: "\<And>rs. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<Longrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> Undecided" by fast
            note r_nomatch'=r_nomatch[simplified r \<open>a = Return\<close>] --"r unfolded"
            from False not_matches_add_matchNot_simp prems have "\<Gamma>,\<gamma>,p\<turnstile> \<langle>process_ret rs, Undecided\<rangle> \<Rightarrow> Undecided" by fast
            with Cons.IH have IH: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided \<or> (\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p)" .
            thus ?thesis
              proof(elim disjE)
                assume "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Undecided"
                hence "\<Gamma>,\<gamma>,p\<turnstile> \<langle>r # rs, Undecided\<rangle> \<Rightarrow> Undecided" using r_nomatch by simp
                thus ?thesis by simp
              next
                assume "\<exists>rs\<^sub>1 rs\<^sub>2 m. rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p"
                from this obtain rs\<^sub>1 rs\<^sub>2 m' where "rs = rs\<^sub>1 @ [Rule m' Return] @ rs\<^sub>2" and "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided" and "matches \<gamma> m' p" by blast
                hence "\<exists>rs\<^sub>1 rs\<^sub>2 m. r # rs = rs\<^sub>1 @ [Rule m Return] @ rs\<^sub>2 \<and> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs\<^sub>1, Undecided\<rangle> \<Rightarrow> Undecided \<and> matches \<gamma> m p" 
                  apply(rule_tac x="Rule m Return # rs\<^sub>1" in exI)
                  apply(rule_tac x="rs\<^sub>2" in exI)
                  apply(rule_tac x="m'" in exI)
                  by(simp add:  \<open>a = Return\<close> False r r_nomatch')
                thus ?thesis by simp
              qed
          qed
       qed
  qed
  with assms noreturn return show ?thesis by auto
qed

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

subsection\<open>@{const process_ret} correctness\<close>
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
  apply (meson seq'_cons seqE_cons)
 apply (meson seq'_cons seqE_cons)
by (metis decision decisionD matches.simps(1) matches_add_match_MatchNot_simp matches_add_match_simp
  not_matches_add_matchNot_simp not_matches_add_match_simp state.exhaust)

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
  apply (meson seq'_cons seqE_cons)
 apply (meson seq'_cons seqE_cons)
by (metis decision decisionD matches.simps(1) matches_add_match_MatchNot_simp matches_add_match_simp
  not_matches_add_matchNot_simp not_matches_add_match_simp state.exhaust)

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


lemma process_ret_sound':
  assumes "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>process_ret (add_match m rs), Undecided\<rangle> \<Rightarrow> t"
  shows "\<Gamma>(chain \<mapsto> rs),\<gamma>,p\<turnstile> \<langle>[Rule m (Call chain)], Undecided\<rangle> \<Rightarrow> t"
using assms by (metis state.exhaust process_ret_Undecided_sound process_ret_Decision_sound)



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

subsection\<open>Soundness\<close>
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
            from this \<open>wf_chain \<Gamma> [r]\<close>have "wf_chain \<Gamma> (r # (process_call \<Gamma> rs))" by(simp add: wf_chain_def)
            from this Cons.prems have "wf_chain \<Gamma> (process_call \<Gamma> (r#rs))"
              apply(cases r)
              apply(rename_tac m a, clarify)
              apply(case_tac a)
                      apply(simp_all)
              apply(simp add: wf_chain_append)
              apply(clarify)
              apply(simp add: \<open>wf_chain \<Gamma> (process_call \<Gamma> rs)\<close>)
              apply(rule wf_chain_add_match)
              apply(rule wf_chain_process_ret)
              apply(simp add: wf_chain_def)
              apply(clarify)
              by (metis ranI option.sel)
          from this \<open>\<forall>a\<in>ran \<Gamma>. wf_chain \<Gamma> a\<close> show ?case by simp
        qed
      from this Suc.IH[of "((process_call \<Gamma>) rs)"] have 
        "\<Gamma>,\<gamma>,p\<turnstile> \<langle>(process_call \<Gamma> ^^ n) (process_call \<Gamma> rs), s\<rangle> \<Rightarrow> t = \<Gamma>,\<gamma>,p\<turnstile> \<langle>process_call \<Gamma> rs, s\<rangle> \<Rightarrow> t"
        by simp
    from this show ?case by (simp add: Suc.prems funpow_swap1 unfolding_sound_complete)
  qed


text_raw\<open>
\begin{verbatim}
loops in the linux kernel:
http://lxr.linux.no/linux+v3.2/net/ipv4/netfilter/ip_tables.c#L464
/* Figures out from what hook each rule can be called: returns 0 if
   there are loops.  Puts hook bitmask in comefrom. */
   static int mark_source_chains(const struct xt_table_info *newinfo,
                   unsigned int valid_hooks, void *entry0)

discussion: http://marc.info/?l=netfilter-devel&m=105190848425334&w=2
\end{verbatim}
\<close>

text\<open>Example\<close>
lemma "process_call [''X'' \<mapsto> [Rule (Match b) Return, Rule (Match c) Accept]] [Rule (Match a) (Call ''X'')] =
       [Rule (MatchAnd (Match a) (MatchAnd (MatchNot (Match b)) (Match c))) Accept]" by (simp add: add_match_def)




text\<open>This is how a firewall processes a ruleset. 
       It starts at a certain chain, usually INPUT, FORWARD, or OUTPUT (called @{term chain_name} in the lemma).
       The firewall has a default action of accept or drop.
      We can check @{const sanity_wf_ruleset} and the other assumptions at runtime.
      Consequently, we can apply @{const repeat_stabilize} as often as we want.
\<close>

theorem repeat_stabilize_process_call:
    assumes "sanity_wf_ruleset \<Gamma>" and "chain_name \<in> set (map fst \<Gamma>)" and "default_action = Accept \<or> default_action = Drop"
    shows "(map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>repeat_stabilize n (process_call (map_of \<Gamma>)) [Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t \<longleftrightarrow>
           (map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t"
proof -
  have x: "sanity_wf_ruleset \<Gamma> \<Longrightarrow> rs \<in> ran (map_of \<Gamma>) \<Longrightarrow> wf_chain (map_of \<Gamma>) rs" for \<Gamma> and rs::"'a rule list"
  apply(simp add: sanity_wf_ruleset_def wf_chain_def)
  by fastforce

  from assms(1) have 1: "\<forall>rsg \<in> ran (map_of \<Gamma>). wf_chain (map_of \<Gamma>) rsg"
    apply(intro ballI)
    apply(drule x, simp)
    apply(simp)
    done
  let ?rs="[Rule MatchAny (Call chain_name), Rule MatchAny default_action]::'a rule list"
  from assms(2,3) have 2: "wf_chain (map_of \<Gamma>) ?rs"
    apply(simp add: wf_chain_def domD dom_map_of_conv_image_fst)
    by blast

  have "\<forall>rsg \<in> ran \<Gamma> \<union> {rs}. wf_chain \<Gamma> rsg \<Longrightarrow> 
    \<Gamma>,\<gamma>,p\<turnstile> \<langle>repeat_stabilize n (process_call \<Gamma>) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t" for \<Gamma> rs
  by(simp add: repeat_stabilize_funpow unfolding_n_sound_complete)
  moreover from 1 2 have "\<forall>rsg \<in> ran (map_of \<Gamma>) \<union> {?rs}. wf_chain (map_of \<Gamma>) rsg" by simp
  ultimately show ?thesis by simp
qed



definition unfold_optimize_ruleset_CHAIN
  :: "('a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> string \<Rightarrow> action \<Rightarrow> 'a ruleset \<Rightarrow> 'a rule list option"
where
"unfold_optimize_ruleset_CHAIN optimize chain_name default_action rs = (let rs =
  (repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
    (optimize_matches optimize
      (rw_Reject (rm_LogEmpty (repeat_stabilize 10000 (process_call rs)
        [Rule MatchAny (Call chain_name), Rule MatchAny default_action]
  )))))
  in if simple_ruleset rs then Some rs else None)"


lemma unfold_optimize_ruleset_CHAIN:
    assumes "sanity_wf_ruleset \<Gamma>" and "chain_name \<in> set (map fst \<Gamma>)"
    and "default_action = Accept \<or> default_action = Drop"
    and "\<And>m. matches \<gamma> (optimize m) p = matches \<gamma> m p"
    and "unfold_optimize_ruleset_CHAIN optimize chain_name default_action (map_of \<Gamma>) = Some rs"
    shows "(map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow>
           (map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t"
proof -
  from assms(5) have rs: "rs = repeat_stabilize 1000 (optimize_matches opt_MatchAny_match_expr)
      (optimize_matches optimize
        (rw_Reject
          (rm_LogEmpty
            (repeat_stabilize 10000 (process_call (map_of \<Gamma>)) [Rule MatchAny (Call chain_name), Rule MatchAny default_action]))))"
    by(simp add: unfold_optimize_ruleset_CHAIN_def Let_def split: if_split_asm)

  have optimize_matches_generic_funpow_helper: "(\<And>m. matches \<gamma> (f m) p = matches \<gamma> m p) \<Longrightarrow>
        \<Gamma>,\<gamma>,p\<turnstile> \<langle>(optimize_matches f ^^ n) rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"
    for \<Gamma> f n rs
    proof(induction n arbitrary:)
      case 0 thus ?case by simp
    next
      case (Suc n) thus ?case
       apply(simp)
       apply(subst optimize_matches_generic[where P="\<lambda>_. True"])
       by simp_all
    qed

  have "(map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow> map_of \<Gamma>,\<gamma>,p\<turnstile> \<langle>repeat_stabilize 10000 (process_call (map_of \<Gamma>))
    [Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t"
    apply(simp add: rs repeat_stabilize_funpow)
    apply(subst optimize_matches_generic_funpow_helper)
     apply (simp add: opt_MatchAny_match_expr_correct; fail)
    apply(subst optimize_matches_generic[where P="\<lambda>_. True"], simp_all add: assms(4))
    apply(simp add: iptables_bigstep_rw_Reject iptables_bigstep_rm_LogEmpty)
    done
  also have "\<dots> \<longleftrightarrow> (map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t"
    using assms(1,2,3) by(intro repeat_stabilize_process_call[of \<Gamma> chain_name default_action \<gamma> p 10000 s t]) simp_all
  finally show ?thesis .
qed

end
