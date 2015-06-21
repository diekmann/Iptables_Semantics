theory Remdups_Rev
imports Main
begin

definition "remdups_rev rs = (rev (remdups (rev rs)))"


lemma remdups_append: "remdups (rs @ rs2) = remdups [r\<leftarrow>rs . r \<notin> set rs2] @ remdups rs2"
  by(induction rs arbitrary: rs2) (simp_all)

lemma remdups_rev_append: "remdups_rev (rs @ rs2) = remdups_rev rs @ remdups_rev [r\<leftarrow>rs2 . r \<notin> set rs]"
  proof(induction rs arbitrary: rs2)
  case Cons thus ?case by(simp add: remdups_append rev_filter remdups_rev_def)
  qed(simp add: remdups_rev_def)

lemma remdups_rev_fst: "remdups_rev (r#rs) = (if r \<in> set rs then r#remdups_rev (removeAll r rs) else r#remdups_rev rs)"
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

lemma remdups_rev_removeAll: "remdups_rev (removeAll r rs) = removeAll r (remdups_rev rs)"
  by (simp add: remdups_filter remdups_rev_def removeAll_filter_not_eq rev_filter)

end
