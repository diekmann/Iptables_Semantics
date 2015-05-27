theory Optimizing
imports Semantics_Ternary Packet_Set_Impl
begin


section{*Optimizing*}

subsection{*Removing Shadowed Rules*}

text{*Assumes: @{term "simple_ruleset"}*}
fun rmshadow :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'a rule list" where
  "rmshadow _ [] _ = []" |
  "rmshadow \<gamma> ((Rule m a)#rs) P = (if (\<forall>p\<in>P. \<not> matches \<gamma> m a p)
    then 
      rmshadow \<gamma> rs P
    else
      (Rule m a) # (rmshadow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m a p}))"
(*needs a ruleset without log and empty*)



subsubsection{*Soundness*}
  lemma rmshadow_sound: 
    "simple_ruleset rs \<Longrightarrow> p \<in> P \<Longrightarrow> approximating_bigstep_fun \<gamma> p (rmshadow \<gamma> rs P) = approximating_bigstep_fun \<gamma> p rs"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    let ?fw="approximating_bigstep_fun \<gamma>" --"firewall semantics"
    let ?rm="rmshadow \<gamma>"
    let ?match="matches \<gamma> (get_match r) (get_action r)"
    let ?set="{p \<in> P. \<not> ?match p}"
    from Cons.IH Cons.prems have IH: "?fw p (?rm rs P) = ?fw p rs" by (simp add: simple_ruleset_def)
    from Cons.IH[of "?set"] Cons.prems have IH': "p \<in> ?set \<Longrightarrow> ?fw p (?rm rs ?set) = ?fw p rs" by (simp add: simple_ruleset_def)
    from Cons show ?case
      proof(cases "\<forall>p\<in>P. \<not> ?match p") --"the if-condition of rmshadow"
      case True
        from True have 1: "?rm (r#rs) P = ?rm rs P" 
          apply(cases r)
          apply(rename_tac m a)
          apply(clarify)
          apply(simp)
          done
        from True Cons.prems have "?fw p (r # rs) = ?fw p rs"
          apply(cases r)
          apply(rename_tac m a)
          apply(simp add: fun_eq_iff)
          apply(clarify)
          apply(rename_tac s)
          apply(case_tac s)
           apply(simp)
          apply(simp add: Decision_approximating_bigstep_fun)
          done
        from this IH have "?fw p (?rm rs P) = ?fw p (r#rs) " by simp
        thus "?fw p (?rm (r#rs) P) = ?fw p (r#rs) " using 1 by simp
      next
      case False --"else"
        have "?fw p (r # (?rm rs ?set)) = ?fw p (r # rs)"
          proof(cases "p \<in> ?set")
            case True
              from True IH' show "?fw p (r # (?rm rs ?set)) = ?fw p (r#rs)" 
                apply(cases r)
                apply(rename_tac m a)
                apply(simp add: fun_eq_iff)
                apply(clarify)
                apply(rename_tac s)
                apply(case_tac s)
                 apply(simp)
                apply(simp add: Decision_approximating_bigstep_fun)
                done
            next
            case False
              from False Cons.prems have "?match p" by simp
              from Cons.prems have "get_action r = Accept \<or> get_action r = Drop" by(simp add: simple_ruleset_def)
              from this `?match p`show "?fw p (r # (?rm rs ?set)) = ?fw p (r#rs)"
                apply(cases r)
                apply(rename_tac m a)
                apply(simp add: fun_eq_iff)
                apply(clarify)
                apply(rename_tac s)
                apply(case_tac s)
                 apply(simp split:action.split)
                 apply fast
                apply(simp add: Decision_approximating_bigstep_fun)
                done
          qed
        from False this show ?thesis 
          apply(cases r)
          apply(rename_tac m a)
          apply(simp add: fun_eq_iff)
          apply(clarify)
          apply(rename_tac s)
          apply(case_tac s)
           apply(simp)
          apply(simp add: Decision_approximating_bigstep_fun)
          done
    qed
  qed





fun rmMatchFalse :: "'a rule list \<Rightarrow> 'a rule list" where
  "rmMatchFalse [] = []" |
  "rmMatchFalse ((Rule (MatchNot MatchAny) _)#rs) = rmMatchFalse rs" |
  "rmMatchFalse (r#rs) = r # rmMatchFalse rs"

lemma rmMatchFalse_helper: "m \<noteq> MatchNot MatchAny \<Longrightarrow> (rmMatchFalse (Rule m a # rs)) = Rule m a # (rmMatchFalse rs)"
  apply(case_tac m)
  apply(simp_all)
  apply(rename_tac match_expr)
  apply(case_tac match_expr)
  apply(simp_all)
done

lemma rmMatchFalse_correct: "approximating_bigstep_fun \<gamma> p (rmMatchFalse rs) s = approximating_bigstep_fun \<gamma> p rs s"
  apply(induction \<gamma> p rs s rule: approximating_bigstep_fun_induct)
     apply(simp)
    apply (metis Decision_approximating_bigstep_fun)
   apply(case_tac "m = MatchNot MatchAny")
    apply(simp)
   apply(simp add: rmMatchFalse_helper)
  apply(subgoal_tac "m \<noteq> MatchNot MatchAny")
  apply(drule_tac a=a and rs=rs in rmMatchFalse_helper)
  apply(simp split:action.split)
  apply(thin_tac "a = x \<Longrightarrow> _" for x)
  apply(thin_tac "a = x \<Longrightarrow> _" for x)
  by (metis bunch_of_lemmata_about_matches(3))
  



end
