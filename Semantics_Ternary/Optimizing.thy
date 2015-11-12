theory Optimizing
imports Semantics_Ternary Packet_Set_Impl
begin


section{*Optimizing*}

subsection{*Removing Shadowed Rules*}
text{*Note: there is no executable code for rmshadow at the moment*}

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
          apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
          apply(simp)
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
                apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
                apply(simp)
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
                apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
                apply(simp split:action.split)
                apply fast
                done
          qed
        from False this show ?thesis 
          apply(cases r)
          apply(rename_tac m a)
          apply(simp add: fun_eq_iff)
          apply(clarify)
          apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
          apply(simp)
          done
    qed
  qed



subsection{*Removing rules which cannot apply*}

fun rmMatchFalse :: "'a rule list \<Rightarrow> 'a rule list" where
  "rmMatchFalse [] = []" |
  "rmMatchFalse ((Rule (MatchNot MatchAny) _)#rs) = rmMatchFalse rs" |
  "rmMatchFalse (r#rs) = r # rmMatchFalse rs"

lemma rmMatchFalse_correct: "approximating_bigstep_fun \<gamma> p (rmMatchFalse rs) s = approximating_bigstep_fun \<gamma> p rs s"
  proof-
    { fix m::"'a match_expr" and a and rs
      assume assm: "m \<noteq> MatchNot MatchAny"
      have "rmMatchFalse (Rule m a # rs) = Rule m a # (rmMatchFalse rs)" (is ?hlp)
      proof(cases m)
        case (MatchNot mexpr) with assm show ?hlp by(cases mexpr) simp_all
        qed(simp_all)
    } note rmMatchFalse_helper=this
  show ?thesis
    proof(induction \<gamma> p rs s rule: approximating_bigstep_fun_induct)
      case Empty thus ?case by(simp)
      next
      case Decision thus ?case by(metis Decision_approximating_bigstep_fun)
      next
      case (Nomatch \<gamma> p m a) thus ?case
        by(cases "m = MatchNot MatchAny") (simp_all add: rmMatchFalse_helper)
      next
      case (Match \<gamma> p m a rs) 
        from Match(1) have "m \<noteq> MatchNot MatchAny" using bunch_of_lemmata_about_matches(3) by fast
        with Match rmMatchFalse_helper show ?case by(simp split:action.split)
    qed
  qed



fun cutt_off_after_default :: "'a rule list \<Rightarrow> 'a rule list" where
  "cutt_off_after_default [] = []" |
  "cutt_off_after_default ((Rule MatchAny Accept)#_) = [Rule MatchAny Accept]" |
  "cutt_off_after_default ((Rule MatchAny Drop)#_) = [Rule MatchAny Drop]" |
  "cutt_off_after_default ((Rule MatchAny Reject)#_) = [Rule MatchAny Reject]" |
  "cutt_off_after_default (r#rs) = r # cutt_off_after_default rs"

lemma cutt_off_after_default_correct: "approximating_bigstep_fun \<gamma> p (cutt_off_after_default rs) s = approximating_bigstep_fun \<gamma> p rs s"
apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
by(induction rs rule: cutt_off_after_default.induct) (simp_all add: bunch_of_lemmata_about_matches(2) split: action.split)


end
