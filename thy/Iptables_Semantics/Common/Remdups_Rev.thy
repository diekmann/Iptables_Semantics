section\<open>Reverse Remdups\<close>
theory Remdups_Rev
imports Main
begin

definition remdups_rev :: "'a list \<Rightarrow> 'a list" where
  "remdups_rev rs \<equiv> rev (remdups (rev rs))"

lemma remdups_append: "remdups (rs @ rs2) = remdups [r\<leftarrow>rs . r \<notin> set rs2] @ remdups rs2"
  by(induction rs arbitrary: rs2) (simp_all)

lemma remdups_rev_append: "remdups_rev (rs @ rs2) = remdups_rev rs @ remdups_rev [r\<leftarrow>rs2 . r \<notin> set rs]"
  proof(induction rs arbitrary: rs2)
  case Cons thus ?case by(simp add: remdups_append rev_filter remdups_rev_def)
  qed(simp add: remdups_rev_def)

lemma remdups_rev_fst:
  "remdups_rev (r#rs) = (if r \<in> set rs then r#remdups_rev (removeAll r rs) else r#remdups_rev rs)"
proof -
  have 1: "r \<notin> set rs \<Longrightarrow> remdups_rev (r # rs) = r # remdups_rev rs"
    unfolding remdups_rev_def
    proof(induction rs)
    case (Cons r rs)
      { fix rs and rs2::"'a list"
        have "set rs \<inter> set rs2 = {} \<Longrightarrow> remdups (rs @ rs2) = remdups rs @ remdups rs2"
          by(induction rs arbitrary: rs2) (simp_all)
      } note h=this
      { fix r and rs::"'a list"
        from h[of "rev rs" "[r]"] have "r \<notin> set rs \<Longrightarrow> remdups (rev rs @ [r]) = remdups (rev rs) @ [r]" by simp
      }
      with Cons show ?case by fastforce  
    qed(simp)

  have 2: "r \<in> set rs \<Longrightarrow> remdups_rev (r # rs) = r # remdups_rev (rev (removeAll r (rev rs)))"
    unfolding remdups_rev_def
    proof(induction rs)
    case Cons thus ?case
      apply(simp add: removeAll_filter_not_eq remdups_append)
      apply(safe)
        apply(simp_all)
       apply metis
      apply metis
      done
    qed(simp)

  have "rev (removeAll r (rev rs)) = removeAll r rs" by (simp add: removeAll_filter_not_eq rev_filter)
  with 1 2 show ?thesis by simp
qed

lemma remdups_rev_set: "set (remdups_rev rs) = set rs" by (simp add: remdups_rev_def) 

lemma remdups_rev_removeAll: "remdups_rev (removeAll r rs) = removeAll r (remdups_rev rs)"
  by (simp add: remdups_filter remdups_rev_def removeAll_filter_not_eq rev_filter)

text\<open>Faster code equations\<close>
fun remdups_rev_code :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_rev_code _ [] = []" |
  "remdups_rev_code ps (r#rs) = (if r \<in> set ps then remdups_rev_code ps rs else r#remdups_rev_code (r#ps) rs)"

lemma remdups_rev_code[code_unfold]: "remdups_rev rs = remdups_rev_code [] rs"
proof -
  { fix ps1 ps2 p and rs::"'a list"
    have "set ps1 = set ps2 \<Longrightarrow> remdups_rev_code ps1 rs = remdups_rev_code ps2 rs"
      proof(induction rs arbitrary: ps1 ps2)
      case Nil thus ?case by simp
      next
      case (Cons r rs) show ?case
        apply(subst remdups_rev_code.simps)+ (*simplifier loops*)
        apply(case_tac "r \<in> set ps1")
         using Cons apply metis
        using Cons apply(simp)
        done
      qed
  } note remdups_rev_code_ps_seteq=this
  { fix ps1 ps2 p and rs::"'a list"
    have "remdups_rev_code (ps1@ps2) rs = remdups_rev_code ps2 (filter (\<lambda>r. r \<notin> set ps1) rs)"
      proof(induction rs arbitrary: ps1 ps2)
      case (Cons r rs)
        have "remdups_rev_code (r # ps1 @ ps2) rs = remdups_rev_code (ps1 @ r # ps2) rs"
          by(rule remdups_rev_code_ps_seteq) simp
        with Cons.IH have "remdups_rev_code (r # ps1 @ ps2) rs = remdups_rev_code (r#ps2) [r\<leftarrow>rs . r \<notin> set ps1]" by simp
        from this show ?case by(simp add: Cons)
      qed(simp add: remdups_rev_def)
   } note remdups_rev_code_ps_append=this
  { fix ps p and rs::"'a list"
    have "remdups_rev_code (p # ps) rs = remdups_rev_code ps (removeAll p rs)"
      by(simp add: remdups_rev_code_ps_append[of "[p]" "ps" rs, simplified] removeAll_filter_not_eq) metis
  } note remdups_rev_code_ps_fst=this
  { fix ps p and rs::"'a list"
    have "remdups_rev_code ps (removeAll p rs) = removeAll p (remdups_rev_code ps rs)"
      apply(induction rs arbitrary: ps)
       apply(simp_all)
      apply(safe)
       apply(simp_all)
      apply(simp add: remdups_rev_code_ps_fst removeAll_filter_not_eq)
      done
  } note remdups_rev_code_removeAll=this
  {fix ps
    have "\<forall>p \<in> set ps. p \<notin> set rs \<Longrightarrow> remdups_rev rs = remdups_rev_code ps rs"
      apply(induction rs arbitrary: ps)
       apply(simp add: remdups_rev_def)
      apply(simp add: remdups_rev_fst remdups_rev_removeAll)
      apply safe
        apply(simp_all)
       apply(simp add: remdups_rev_code_ps_fst remdups_rev_code_removeAll)
       apply metis
      by blast
  }
  thus ?thesis by simp
qed
  

end
