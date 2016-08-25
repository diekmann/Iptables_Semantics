theory Fixed_Action
imports Semantics_Ternary
begin

section\<open>Fixed Action\<close>

text\<open>If firewall rules have the same action, we can focus on the matching only.\<close>

text\<open>Applying a rule once or several times makes no difference.\<close>
lemma approximating_bigstep_fun_prepend_replicate: 
  "n > 0 \<Longrightarrow> approximating_bigstep_fun \<gamma> p (r#rs) Undecided = approximating_bigstep_fun \<gamma> p ((replicate n r)@rs) Undecided"
apply(induction n)
 apply(simp)
apply(simp)
apply(case_tac r)
apply(rename_tac m a)
apply(simp split: action.split)
by fastforce




text\<open>utility lemmas\<close>
context
begin
  private lemma fixedaction_Log: "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m Log) ms) Undecided = Undecided"
    by(induction ms, simp_all)

  private lemma fixedaction_Empty:"approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m Empty) ms) Undecided = Undecided"
    by(induction ms, simp_all)

  private lemma helperX1_Log: "matches \<gamma> m' Log p \<Longrightarrow> 
         approximating_bigstep_fun \<gamma> p (map ((\<lambda>m. Rule m Log) \<circ> MatchAnd m') m2' @ rs2) Undecided =
         approximating_bigstep_fun \<gamma> p rs2 Undecided"
    by(induction m2')(simp_all split: action.split)

  private lemma helperX1_Empty: "matches \<gamma> m' Empty p \<Longrightarrow> 
         approximating_bigstep_fun \<gamma> p (map ((\<lambda>m. Rule m Empty) \<circ> MatchAnd m') m2' @ rs2) Undecided =
         approximating_bigstep_fun \<gamma> p rs2 Undecided"
    by(induction m2')(simp_all split: action.split)

  private lemma helperX3: "matches \<gamma> m' a p \<Longrightarrow>
       approximating_bigstep_fun \<gamma> p (map ((\<lambda>m. Rule m a) \<circ> MatchAnd m') m2' @ rs2 ) Undecided =
       approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m2' @ rs2) Undecided"
  proof(induction m2')
    case Nil thus ?case by simp
    next
    case Cons thus ?case by(cases a) (simp_all add: matches_simps)
  qed
  
  lemmas fixed_action_simps = fixedaction_Log fixedaction_Empty helperX1_Log helperX1_Empty helperX3
end

lemma fixedaction_swap:
   "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m1@m2)) s = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m2@m1)) s"
proof(induction s rule: just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
case Undecided
  have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m1 @ map (\<lambda>m. Rule m a) m2) Undecided =
        approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m2 @ map (\<lambda>m. Rule m a) m1) Undecided"
  proof(induction m1)
    case Nil thus ?case by simp
    next
    case (Cons m m1)
      { fix m rs
        have "approximating_bigstep_fun \<gamma> p ((map (\<lambda>m. Rule m Log) m)@rs) Undecided =
            approximating_bigstep_fun \<gamma> p rs Undecided"
        by(induction m) (simp_all)
      } note Log_helper=this
      { fix m rs
        have "approximating_bigstep_fun \<gamma> p ((map (\<lambda>m. Rule m Empty) m)@rs) Undecided =
            approximating_bigstep_fun \<gamma> p rs Undecided"
        by(induction m) (simp_all)
      } note Empty_helper=this
      
      show ?case
        proof(cases "matches \<gamma> m a p")
          case True
            thus ?thesis
              proof(induction m2)
                case Nil thus ?case by simp
              next
                case Cons thus ?case
                  apply(simp split:action.split action.split_asm)
                  using Log_helper Empty_helper by fastforce+ 
              qed
          next
          case False
            thus ?thesis
             apply(simp)
             apply(simp add: Cons.IH)
             apply(induction m2)
              apply(simp_all)
             apply(simp split:action.split action.split_asm)
             apply fastforce
            done
        qed
    qed
  thus ?thesis using Undecided by simp
qed

corollary fixedaction_reorder: "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m1 @ m2 @ m3)) s = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m2 @ m1 @ m3)) s"
proof(induction s rule: just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
case Undecided
have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m1 @ m2 @ m3)) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m2 @ m1 @ m3)) Undecided"
  proof(induction m3)
    case Nil thus ?case using fixedaction_swap by fastforce
    next
    case (Cons m3'1 m3)
      have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ((m3'1 # m3) @ m1 @ m2)) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ((m3'1 # m3) @ m2 @ m1)) Undecided"
        apply(simp)
        apply(cases "matches \<gamma> m3'1 a p")
         apply(simp split: action.split action.split_asm)
         apply (metis append_assoc fixedaction_swap map_append Cons.IH)
        apply(simp)
        by (metis append_assoc fixedaction_swap map_append Cons.IH)
      hence "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ((m1 @ m2) @ m3'1 # m3)) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ((m2 @ m1) @ m3'1 # m3)) Undecided"
        apply(subst fixedaction_swap)
        apply(subst(2) fixedaction_swap)
        by simp
      thus ?case
        apply(subst append_assoc[symmetric])
        apply(subst append_assoc[symmetric])
        by simp
  qed
  thus ?thesis using Undecided by simp
qed


text\<open>If the actions are equal, the @{term set} (position and replication independent) of the match expressions can be considered.\<close>
lemma approximating_bigstep_fun_fixaction_matchseteq: "set m1 = set m2 \<Longrightarrow>
        approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m1) s = 
       approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m2) s"
proof(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
  assume m1m2_seteq: "set m1 = set m2" and "s = Undecided"
  from m1m2_seteq have
    "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m1) Undecided =
     approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m2) Undecided"
  proof(induction m1 arbitrary: m2)
   case Nil thus ?case by simp
   next
   case (Cons m m1)
    show ?case
      proof (cases "m \<in> set m1")
      case True
        from True have "set m1 = set (m # m1)" by auto
        from Cons.IH[OF \<open>set m1 = set (m # m1)\<close>] have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m # m1)) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m1)) Undecided" ..
        thus ?thesis by (metis Cons.IH Cons.prems \<open>set m1 = set (m # m1)\<close>)
      next
      case False
        from False have "m \<notin> set m1" .
        show ?thesis
        proof (cases "m \<notin> set m2")
          case True
          from True \<open>m \<notin> set m1\<close> Cons.prems have "set m1 = set m2" by auto
          from Cons.IH[OF this] show ?thesis by (metis Cons.IH Cons.prems \<open>set m1 = set m2\<close>)
        next
        case False
          hence "m \<in> set m2" by simp
  
          have repl_filter_simp: "(replicate (length [x\<leftarrow>m2 . x = m]) m) = [x\<leftarrow>m2 . x = m]"
            by (metis (lifting, full_types) filter_set member_filter replicate_length_same)
  
          from Cons.prems  \<open>m \<notin> set m1\<close> have "set m1 = set (filter (\<lambda>x. x\<noteq>m) m2)" by auto
          from Cons.IH[OF this] have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m1) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) [x\<leftarrow>m2 . x \<noteq> m]) Undecided" .
          from this have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m#m1)) Undecided = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) (m#[x\<leftarrow>m2 . x \<noteq> m])) Undecided"
            apply(simp split: action.split)
            by fast
          also have "\<dots> = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ([x\<leftarrow>m2 . x = m]@[x\<leftarrow>m2 . x \<noteq> m])) Undecided"
            apply(simp only: list.map)
            thm approximating_bigstep_fun_prepend_replicate[where n="length [x\<leftarrow>m2 . x = m]"]
            apply(subst approximating_bigstep_fun_prepend_replicate[where n="length [x\<leftarrow>m2 . x = m]"])
            apply (metis (full_types) False filter_empty_conv neq0_conv repl_filter_simp replicate_0)
            by (metis (lifting, no_types) map_append map_replicate repl_filter_simp)
          also have "\<dots> =  approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) m2) Undecided"
            proof(induction m2)
            case Nil thus ?case by simp
            next
            case(Cons m2'1 m2')
              have "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x = m] @ Rule m2'1 a # map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x \<noteq> m]) Undecided =
                    approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ([x\<leftarrow>m2' . x = m] @ [m2'1] @ [x\<leftarrow>m2' . x \<noteq> m])) Undecided" by fastforce
              also have "\<dots> = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ([m2'1] @ [x\<leftarrow>m2' . x = m] @ [x\<leftarrow>m2' . x \<noteq> m])) Undecided"
              using fixedaction_reorder by fast 
              finally have XX: "approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x = m] @ Rule m2'1 a # map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x \<noteq> m]) Undecided =
                    approximating_bigstep_fun \<gamma> p (Rule m2'1 a # (map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x = m] @ map (\<lambda>m. Rule m a) [x\<leftarrow>m2' . x \<noteq> m])) Undecided"
              by fastforce
              from Cons show ?case
                apply(case_tac "m2'1 = m")
                 apply(simp split: action.split)
                 apply fast
                apply(simp del: approximating_bigstep_fun.simps)
                apply(simp only: XX)
                apply(case_tac "matches \<gamma> m2'1 a p")
                 apply(simp)
                 apply(simp split: action.split)
                 apply(fast)
                apply(simp)
                done
            qed
          finally show ?thesis .
        qed
      qed
  qed
  thus ?thesis using \<open>s = Undecided\<close> by simp
qed



subsection\<open>@{term match_list}\<close>
  text\<open>Reducing the firewall semantics to short-circuit matching evaluation\<close>

  fun match_list :: "('a, 'packet) match_tac \<Rightarrow> 'a match_expr list \<Rightarrow> action \<Rightarrow> 'packet \<Rightarrow> bool" where
   "match_list \<gamma> [] a p = False" |
   "match_list \<gamma> (m#ms) a p = (if matches \<gamma> m a p then True else match_list \<gamma> ms a p)"


  lemma match_list_matches: "match_list \<gamma> ms a p \<longleftrightarrow> (\<exists>m \<in> set ms. matches \<gamma> m a p)"
    by(induction ms, simp_all)

  lemma match_list_True: "match_list \<gamma> ms a p \<Longrightarrow> approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ms) Undecided = (case a of Accept \<Rightarrow> Decision FinalAllow
              | Drop \<Rightarrow> Decision FinalDeny
              | Reject \<Rightarrow> Decision FinalDeny
              | Log \<Rightarrow> Undecided
              | Empty \<Rightarrow> Undecided
              (*unhandled cases*)
              )"
    apply(induction ms)
     apply(simp)
    apply(simp split: split_if_asm action.split)
    apply(simp add: fixed_action_simps)
    done
  lemma match_list_False: "\<not> match_list \<gamma> ms a p \<Longrightarrow> approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ms) Undecided = Undecided"
    apply(induction ms)
     apply(simp)
    apply(simp split: split_if_asm action.split)
    done

  text\<open>The key idea behind @{const match_list}: Reducing semantics to match list\<close>
  lemma match_list_semantics: "match_list \<gamma> ms1 a p \<longleftrightarrow> match_list \<gamma> ms2 a p \<Longrightarrow>
    approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ms1) s = approximating_bigstep_fun \<gamma> p (map (\<lambda>m. Rule m a) ms2) s"
    apply(rule just_show_all_approximating_bigstep_fun_equalities_with_start_Undecided)
    apply(simp)
    apply(thin_tac "s = Undecided")
    apply(induction ms2)
     apply(simp)
     apply(induction ms1)
      apply(simp)
     apply(simp split: split_if_asm)
    apply(rename_tac m ms2)
    apply(simp del: approximating_bigstep_fun.simps)
    apply(simp split: split_if_asm del: approximating_bigstep_fun.simps)
     apply(simp split: action.split add: match_list_True fixed_action_simps)
    apply(simp)
    done


  text\<open>We can exploit de-morgan to get a disjunction in the match expression!\<close>
  (*but we need to normalize afterwards, which is quite slow*)
  fun match_list_to_match_expr :: "'a match_expr list \<Rightarrow> 'a match_expr" where
    "match_list_to_match_expr [] = MatchNot MatchAny" |
    "match_list_to_match_expr (m#ms) = MatchOr m (match_list_to_match_expr ms)"
  text\<open>@{const match_list_to_match_expr} constructs a unwieldy @{typ "'a match_expr"} from a list.
        The semantics of the resulting match expression is the disjunction of the elements of the list.
        This is handy because the normal match expressions do not directly support disjunction.
        Use this function with care because the resulting match expression is very ugly!\<close>
  lemma match_list_to_match_expr_disjunction: "match_list \<gamma> ms a p \<longleftrightarrow> matches \<gamma> (match_list_to_match_expr ms) a p"
    apply(induction ms rule: match_list_to_match_expr.induct)
     apply(simp add: bunch_of_lemmata_about_matches; fail)
    apply(simp add: MatchOr)
  done

  lemma match_list_singleton: "match_list \<gamma> [m] a p \<longleftrightarrow> matches \<gamma> m a p" by(simp)

  lemma match_list_append: "match_list \<gamma> (m1@m2) a p \<longleftrightarrow> (\<not> match_list \<gamma> m1 a p \<longrightarrow> match_list \<gamma> m2 a p)"
      by(induction m1) simp+

  lemma match_list_helper1: "\<not> matches \<gamma> m2 a p \<Longrightarrow> match_list \<gamma> (map (\<lambda>x. MatchAnd x m2) m1') a p \<Longrightarrow> False"
    apply(induction m1')
     apply(simp; fail)
    apply(simp split:split_if_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper2: " \<not> matches \<gamma> m a p \<Longrightarrow> \<not> match_list \<gamma> (map (MatchAnd m) m2') a p"
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:split_if_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper3: "matches \<gamma> m a p \<Longrightarrow> match_list \<gamma> m2' a p \<Longrightarrow> match_list \<gamma> (map (MatchAnd m) m2') a p"
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:split_if_asm)
    by (simp add: matches_simps)
  lemma match_list_helper4: "\<not> match_list \<gamma> m2' a p \<Longrightarrow> \<not> match_list \<gamma> (map (MatchAnd aa) m2') a p "
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:split_if_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper5: " \<not> match_list \<gamma> m2' a p \<Longrightarrow> \<not> match_list \<gamma> (concat (map (\<lambda>x. map (MatchAnd x) m2') m1')) a p "
    apply(induction m2')
     apply(simp add:empty_concat; fail)
    apply(simp split:split_if_asm)
    apply(induction m1')
     apply(simp; fail)
    apply(simp add: match_list_append)
    by(auto dest: matches_dest)
  lemma match_list_helper6: "\<not> match_list \<gamma> m1' a p \<Longrightarrow> \<not> match_list \<gamma> (concat (map (\<lambda>x. map (MatchAnd x) m2') m1')) a p "
    apply(induction m2')
     apply(simp add:empty_concat; fail)
    apply(simp split:split_if_asm)
    apply(induction m1')
     apply(simp; fail)
    apply(simp add: match_list_append split: split_if_asm)
    by(auto dest: matches_dest)
  
  lemmas match_list_helper = match_list_helper1 match_list_helper2 match_list_helper3 match_list_helper4 match_list_helper5 match_list_helper6
  hide_fact match_list_helper1 match_list_helper2 match_list_helper3 match_list_helper4 match_list_helper5 match_list_helper6

  lemma match_list_map_And1: "matches \<gamma> m1 a p = match_list \<gamma> m1' a p \<Longrightarrow>
           matches \<gamma> (MatchAnd m1 m2) a p \<longleftrightarrow> match_list \<gamma>  (map (\<lambda>x. MatchAnd x m2) m1') a p"
    apply(induction m1')
     apply(auto dest: matches_dest; fail)[1]
    apply(simp split: split_if_asm)
     apply safe
        apply(simp_all add: matches_simps)
      apply(auto dest: match_list_helper(1))[1]
     by(auto dest: matches_dest)

  lemma matches_list_And_concat: "matches \<gamma> m1 a p = match_list \<gamma> m1' a p \<Longrightarrow> matches \<gamma> m2 a p = match_list \<gamma> m2' a p \<Longrightarrow>
           matches \<gamma> (MatchAnd m1 m2) a p \<longleftrightarrow> match_list \<gamma> [MatchAnd x y. x <- m1', y <- m2'] a p"
    apply(induction m1')
     apply(auto dest: matches_dest; fail)[1]
    apply(simp split: split_if_asm)
     prefer 2
     apply(simp add: match_list_append)
     apply(subgoal_tac "\<not> match_list \<gamma> (map (MatchAnd aa) m2') a p")
      apply(simp; fail)
     apply safe
               apply(simp_all add: matches_simps match_list_append match_list_helper)
    done

  lemma match_list_concat: "match_list \<gamma> (concat lss) a p \<longleftrightarrow> (\<exists>ls \<in> set lss. match_list \<gamma> ls a p)"
    apply(induction lss)
     apply(simp; fail)
    by(auto simp add: match_list_append)
    

lemma fixedaction_wf_ruleset: "wf_ruleset \<gamma> p (map (\<lambda>m. Rule m a) ms) \<longleftrightarrow>
  \<not> match_list \<gamma> ms a p \<or> \<not> (\<exists>chain. a = Call chain) \<and> a \<noteq> Return \<and> \<not> (\<exists>chain. a = Goto chain) \<and> a \<noteq> Unknown"
  proof -
  have helper: "\<And>a b c. a \<longleftrightarrow> c \<Longrightarrow> (a \<longrightarrow> b) = (c \<longrightarrow> b)" by fast
  show ?thesis
    apply(simp add: wf_ruleset_def)
    apply(rule helper)
    apply(induction ms)
     apply(simp; fail)
    apply(simp)
    done
  qed

lemma wf_ruleset_singleton: "wf_ruleset \<gamma> p [Rule m a] \<longleftrightarrow> \<not> matches \<gamma> m a p \<or> \<not> (\<exists>chain. a = Call chain) \<and> a \<noteq> Return \<and> \<not> (\<exists>chain. a = Goto chain) \<and> a \<noteq> Unknown"
  by(simp add: wf_ruleset_def)




end
