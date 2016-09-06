theory Packet_Set
imports Packet_Set_Impl
begin


section\<open>Packet Set\<close>
text\<open>
An explicit representation of sets of packets allowed/denied by a firewall.
Very work in progress, such pre-alpha, wow.
Probably everything here wants a simple ruleset.
\<close>

(* Not really used because it is not awesome :-( *)



subsection\<open>The set of all accepted packets\<close>
  text\<open>
  Collect all packets which are allowed by the firewall.
\<close>
  fun collect_allow :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
    "collect_allow _ [] P = {}" |
    "collect_allow \<gamma> ((Rule m Accept)#rs) P = {p \<in> P. matches \<gamma> m Accept p} \<union> (collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p})" |
    "collect_allow \<gamma> ((Rule m Drop)#rs) P = (collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p})"
  
  lemma collect_allow_subset: "simple_ruleset rs \<Longrightarrow> collect_allow \<gamma> rs P \<subseteq> P"
  apply(induction rs arbitrary: P)
   apply(simp)
  apply(rename_tac r rs P)
  apply(case_tac r, rename_tac m a)
  apply(case_tac a)
          apply(simp_all add: simple_ruleset_def)
   apply(fast)
  apply blast
  done
  
  
  lemma collect_allow_sound: "simple_ruleset rs \<Longrightarrow> p \<in> collect_allow \<gamma> rs P \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
    from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
    from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
    show ?case
    proof(cases a)
      case Accept
        from Accept Cons.IH[where P="{p \<in> P. \<not> matches \<gamma> m Accept p}"] simple_rs have IH:
          "p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p} \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" by simp
        from Accept Cons.prems have "(p \<in> P \<and> matches \<gamma> m Accept p) \<or> p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p}"
          by(simp add: r)
        with Accept show ?thesis
        apply -
        apply(erule disjE)
         apply(simp add: r)
        apply(simp add: r)
        using IH by blast
      next
      case Drop 
        from Drop Cons.prems have "p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p}"
          by(simp add: r)
        with Cons.IH simple_rs have "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" by simp
        with Cons show ?thesis
         apply(simp add: r Drop del: approximating_bigstep_fun.simps)
         apply(simp)
         using collect_allow_subset[OF simple_rs] by fast
      qed(insert a_cases, simp_all)
  qed
  
  
  lemma collect_allow_complete: "simple_ruleset rs \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<Longrightarrow> p \<in> P \<Longrightarrow> p \<in> collect_allow \<gamma> rs P"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
    from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
    from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
    show ?case
    proof(cases a)
      case Accept
        from Accept Cons.IH simple_rs have IH: "\<forall>P. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<longrightarrow> p \<in> P \<longrightarrow> p \<in> collect_allow \<gamma> rs P" by simp
        with Accept Cons.prems show ?thesis
          apply(cases "matches \<gamma> m Accept p")
           apply(simp add: r)
          apply(simp add: r)
          done
      next
      case Drop
        with Cons show ?thesis 
          apply(case_tac "matches \<gamma> m Drop p")
           apply(simp add: r)
          apply(simp add: r simple_rs)
          done
      qed(insert a_cases, simp_all)
  qed
  
  
  theorem collect_allow_sound_complete: "simple_ruleset rs \<Longrightarrow> {p. p \<in> collect_allow \<gamma> rs UNIV} = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
  apply(safe)
  using collect_allow_sound[where P=UNIV] apply fast
  using collect_allow_complete[where P=UNIV] by fast


  text\<open>the complement of the allowed packets\<close>
  fun collect_allow_compl :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
    "collect_allow_compl _ [] P = UNIV" |
    "collect_allow_compl \<gamma> ((Rule m Accept)#rs) P = (P \<union> {p. \<not>matches \<gamma> m Accept p}) \<inter> (collect_allow_compl \<gamma> rs (P \<union> {p. matches \<gamma> m Accept p}))" |
    "collect_allow_compl \<gamma> ((Rule m Drop)#rs) P = (collect_allow_compl \<gamma> rs (P \<union> {p. matches \<gamma> m Drop p}))"
  
  lemma collect_allow_compl_correct: "simple_ruleset rs \<Longrightarrow> (- collect_allow_compl \<gamma> rs ( - P)) = collect_allow \<gamma> rs P"
    proof(induction \<gamma> rs P arbitrary: P rule: collect_allow.induct)
    case 1 thus ?case by simp
    next
    case (2 \<gamma> r rs)
      have set_simp1: "- {p \<in> P. \<not> matches \<gamma> r Accept p} = - P \<union> {p. matches \<gamma> r Accept p}" by blast
      from 2 have IH: "\<And>P. - collect_allow_compl \<gamma> rs (- P) = collect_allow \<gamma> rs P" using simple_ruleset_tail by blast
      from IH[where P="{p \<in> P. \<not> matches \<gamma> r Accept p}"] set_simp1 have
        "- collect_allow_compl \<gamma> rs (- P \<union> Collect (matches \<gamma> r Accept)) = collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> r Accept p}" by simp
      thus ?case by auto
    next
    case (3 \<gamma> r rs)
      have set_simp1: "- {p \<in> P. \<not> matches \<gamma> r Drop p} = - P \<union> {p. matches \<gamma> r Drop p}" by blast
      from 3 have IH: "\<And>P. - collect_allow_compl \<gamma> rs (- P) = collect_allow \<gamma> rs P" using simple_ruleset_tail by blast
      from IH[where P="{p \<in> P. \<not> matches \<gamma> r Drop p}"] set_simp1 have
        "- collect_allow_compl \<gamma> rs (- P \<union> Collect (matches \<gamma> r Drop)) = collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> r Drop p}" by simp
      thus ?case by auto
    qed(simp_all add: simple_ruleset_def)

subsection\<open>The set of all dropped packets\<close>
  text\<open>
  Collect all packets which are denied by the firewall.
\<close>
  fun collect_deny :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
    "collect_deny _ [] P = {}" |
    "collect_deny \<gamma> ((Rule m Drop)#rs) P = {p \<in> P. matches \<gamma> m Drop p} \<union> (collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p})" |
    "collect_deny \<gamma> ((Rule m Accept)#rs) P = (collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p})"
  
  lemma collect_deny_subset: "simple_ruleset rs \<Longrightarrow> collect_deny \<gamma> rs P \<subseteq> P"
  apply(induction rs arbitrary: P)
   apply(simp)
  apply(rename_tac r rs P)
  apply(case_tac r, rename_tac m a)
  apply(case_tac a)
          apply(simp_all add: simple_ruleset_def)
   apply(fast)
  apply blast
  done
  
  
  lemma collect_deny_sound: "simple_ruleset rs \<Longrightarrow> p \<in> collect_deny \<gamma> rs P \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
    from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
    from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
    show ?case
    proof(cases a)
      case Drop
        from Drop Cons.IH[where P="{p \<in> P. \<not> matches \<gamma> m Drop p}"] simple_rs have IH:
          "p \<in> collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p} \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny" by simp
        from Drop Cons.prems have "(p \<in> P \<and> matches \<gamma> m Drop p) \<or> p \<in> collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p}"
          by(simp add: r)
        with Drop show ?thesis
        apply -
        apply(erule disjE)
         apply(simp add: r)
        apply(simp add: r)
        using IH by blast
      next
      case Accept 
        from Accept Cons.prems have "p \<in> collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p}"
          by(simp add: r)
        with Cons.IH simple_rs have "approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny" by simp
        with Cons show ?thesis
         apply(simp add: r Accept del: approximating_bigstep_fun.simps)
         apply(simp)
         using collect_deny_subset[OF simple_rs] by fast
      qed(insert a_cases, simp_all)
  qed
  
  
  lemma collect_deny_complete: "simple_ruleset rs \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny \<Longrightarrow> p \<in> P \<Longrightarrow> p \<in> collect_deny \<gamma> rs P"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons obtain m a where r: "r = Rule m a" by (cases r) simp
    from Cons.prems have simple_rs: "simple_ruleset rs" by (simp add: r simple_ruleset_def)
    from Cons.prems r have a_cases: "a = Accept \<or> a = Drop" by (simp add: r simple_ruleset_def)
    show ?case
    proof(cases a)
      case Accept
        from Accept Cons.IH simple_rs have IH: "\<forall>P. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny \<longrightarrow> p \<in> P \<longrightarrow> p \<in> collect_deny \<gamma> rs P" by simp
        with Accept Cons.prems show ?thesis
          apply(cases "matches \<gamma> m Accept p")
           apply(simp add: r)
          apply(simp add: r)
          done
      next
      case Drop
        with Cons show ?thesis 
          apply(case_tac "matches \<gamma> m Drop p")
           apply(simp add: r)
          apply(simp add: r simple_rs)
          done
      qed(insert a_cases, simp_all)
  qed
  
  
  theorem collect_deny_sound_complete: "simple_ruleset rs \<Longrightarrow> {p. p \<in> collect_deny \<gamma> rs UNIV} = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny}"
  apply(safe)
  using collect_deny_sound[where P=UNIV] apply fast
  using collect_deny_complete[where P=UNIV] by fast
  
  text\<open>the complement of the denied packets\<close>
  fun collect_deny_compl :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
    "collect_deny_compl _ [] P = UNIV" |
    "collect_deny_compl \<gamma> ((Rule m Drop)#rs) P = (P \<union> {p. \<not>matches \<gamma> m Drop p}) \<inter> (collect_deny_compl \<gamma> rs (P \<union> {p. matches \<gamma> m Drop p}))" |
    "collect_deny_compl \<gamma> ((Rule m Accept)#rs) P = (collect_deny_compl \<gamma> rs (P \<union> {p. matches \<gamma> m Accept p}))"
  
  lemma collect_deny_compl_correct: "simple_ruleset rs \<Longrightarrow> (- collect_deny_compl \<gamma> rs ( - P)) = collect_deny \<gamma> rs P"
    proof(induction \<gamma> rs P arbitrary: P rule: collect_deny.induct)
    case 1 thus ?case by simp
    next
    case (3 \<gamma> r rs)
      have set_simp1: "- {p \<in> P. \<not> matches \<gamma> r Accept p} = - P \<union> {p. matches \<gamma> r Accept p}" by blast
      from 3 have IH: "\<And>P. - collect_deny_compl \<gamma> rs (- P) = collect_deny \<gamma> rs P" using simple_ruleset_tail by blast
      from IH[where P="{p \<in> P. \<not> matches \<gamma> r Accept p}"] set_simp1 have
        "- collect_deny_compl \<gamma> rs (- P \<union> Collect (matches \<gamma> r Accept)) = collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> r Accept p}" by simp
      thus ?case by auto
    next
    case (2 \<gamma> r rs)
      have set_simp1: "- {p \<in> P. \<not> matches \<gamma> r Drop p} = - P \<union> {p. matches \<gamma> r Drop p}" by blast
      from 2 have IH: "\<And>P. - collect_deny_compl \<gamma> rs (- P) = collect_deny \<gamma> rs P" using simple_ruleset_tail by blast
      from IH[where P="{p \<in> P. \<not> matches \<gamma> r Drop p}"] set_simp1 have
        "- collect_deny_compl \<gamma> rs (- P \<union> Collect (matches \<gamma> r Drop)) = collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> r Drop p}" by simp
      thus ?case by auto
    qed(simp_all add: simple_ruleset_def)

subsection\<open>Rulesets with default rules\<close>
  definition has_default :: "'a rule list \<Rightarrow> bool" where
    "has_default rs \<equiv> length rs > 0 \<and> ((last rs = Rule MatchAny Accept) \<or> (last rs = Rule MatchAny Drop))"

  lemma has_default_UNIV: "good_ruleset rs \<Longrightarrow> has_default rs \<Longrightarrow>
    {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow} \<union> {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny} = UNIV"
  apply(induction rs)
   apply(simp add: has_default_def)
  apply(rename_tac r rs)
  apply(simp add: has_default_def good_ruleset_tail split: split_if_asm)
   apply(elim disjE)
    apply(simp add: bunch_of_lemmata_about_matches; fail)
   apply(simp add: bunch_of_lemmata_about_matches; fail)
  apply(case_tac r, rename_tac m a)
  apply(case_tac a)
          apply(auto simp: good_ruleset_def)
  done


  lemma allow_set_by_collect_deny_compl: assumes "simple_ruleset rs" and "has_default rs"
   shows "collect_deny_compl \<gamma> rs {} = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
  proof -
    from assms have univ: "{p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow} \<union> {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny} = UNIV"
    using simple_imp_good_ruleset has_default_UNIV by fast
    from assms(1) collect_deny_compl_correct[where P=UNIV] have "collect_deny_compl \<gamma> rs {} = - collect_deny \<gamma> rs UNIV" by fastforce
    moreover with collect_deny_sound_complete assms(1) have "\<dots> =  - {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny}" by fast
    ultimately show ?thesis using univ by fastforce
  qed
  lemma deny_set_by_collect_allow_compl: assumes "simple_ruleset rs" and "has_default rs"
   shows "collect_allow_compl \<gamma> rs {} = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny}"
  proof -
    from assms have univ: "{p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow} \<union> {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny} = UNIV"
    using simple_imp_good_ruleset has_default_UNIV by fast
    from assms(1) collect_allow_compl_correct[where P=UNIV] have "collect_allow_compl \<gamma> rs {} = - collect_allow \<gamma> rs UNIV" by fastforce
    moreover with collect_allow_sound_complete assms(1) have "\<dots> =  - {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}" by fast
    ultimately show ?thesis using univ by fastforce
  qed
  


text\<open>with @{thm packet_set_constrain_correct} and @{thm packet_set_constrain_not_correct}, it should be possible to build an executable version of the algorithm above.\<close>





subsection\<open>The set of all accepted packets -- Executable Implementation\<close>
fun collect_allow_impl_v1 :: "'a rule list \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
  "collect_allow_impl_v1 [] P = packet_set_Empty" |
  "collect_allow_impl_v1 ((Rule m Accept)#rs) P = packet_set_union (packet_set_constrain Accept m P) (collect_allow_impl_v1 rs (packet_set_constrain_not Accept m P))" |
  "collect_allow_impl_v1 ((Rule m Drop)#rs) P = (collect_allow_impl_v1 rs (packet_set_constrain_not Drop m P))"

lemma collect_allow_impl_v1: "simple_ruleset rs \<Longrightarrow> packet_set_to_set \<gamma> (collect_allow_impl_v1 rs P) = collect_allow \<gamma> rs (packet_set_to_set \<gamma> P)"
apply(induction \<gamma> rs "(packet_set_to_set \<gamma> P)"arbitrary: P  rule: collect_allow.induct)
apply(simp_all add: packet_set_union_correct packet_set_constrain_correct packet_set_constrain_not_correct packet_set_Empty simple_ruleset_def)
done


fun collect_allow_impl_v2 :: "'a rule list \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
  "collect_allow_impl_v2 [] P = packet_set_Empty" |
  "collect_allow_impl_v2 ((Rule m Accept)#rs) P = packet_set_opt ( packet_set_union 
    (packet_set_opt (packet_set_constrain Accept m P)) (packet_set_opt (collect_allow_impl_v2 rs (packet_set_opt (packet_set_constrain_not Accept m (packet_set_opt P))))))" |
  "collect_allow_impl_v2 ((Rule m Drop)#rs) P = (collect_allow_impl_v2 rs (packet_set_opt (packet_set_constrain_not Drop m (packet_set_opt P))))"

lemma collect_allow_impl_v2: "simple_ruleset rs \<Longrightarrow> packet_set_to_set \<gamma> (collect_allow_impl_v2 rs P) = packet_set_to_set \<gamma> (collect_allow_impl_v1 rs P)"
apply(induction rs P arbitrary: P  rule: collect_allow_impl_v1.induct)
apply(simp_all add: simple_ruleset_def packet_set_union_correct packet_set_opt_correct packet_set_constrain_not_correct collect_allow_impl_v1)
done


text\<open>executable! But not really usable.\<close>
export_code collect_allow_impl_v2 checking SML


theorem collect_allow_impl_v1_sound_complete: "simple_ruleset rs \<Longrightarrow> 
  packet_set_to_set \<gamma> (collect_allow_impl_v1 rs packet_set_UNIV) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
apply(simp add: collect_allow_impl_v1 packet_set_UNIV)
using collect_allow_sound_complete by fast

corollary collect_allow_impl_v2_sound_complete: "simple_ruleset rs \<Longrightarrow> 
  packet_set_to_set \<gamma> (collect_allow_impl_v2 rs packet_set_UNIV) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
using collect_allow_impl_v1_sound_complete collect_allow_impl_v2 by fast




text\<open>instead of the expensive invert and intersect operations, we try to build the algorithm primarily by union\<close>
lemma "(UNIV - A) \<inter> (UNIV - B) = UNIV - (A \<union> B)" by blast
lemma "A \<inter> (- P) = UNIV - (-A \<union> P)" by blast
lemma "UNIV - ((- P) \<inter> A) = P \<union> - A" by blast
lemma "((- P) \<inter> A) = UNIV - (P \<union> - A)" by blast

lemma "UNIV - ((P \<union> - A) \<inter> X) = UNIV - ((P \<inter> X) \<union> (- A \<inter> X))" by blast
lemma "UNIV - ((P \<inter> X) \<union> (- A \<inter> X)) = (- P \<union> -X) \<inter> (A \<union> - X)" by blast
lemma "(- P \<union> -X) \<inter> (A \<union> -X) = (- P \<inter> A) \<union> - X" by blast

lemma "(((- P) \<inter> A) \<union> X) = UNIV - ((P \<union> - A) \<inter> - X)" by blast

lemma set_helper1: 
  "(- P \<inter> - {p. matches \<gamma> m a p}) = {p. p \<notin> P \<and> \<not> matches \<gamma> m a p}" 
  "- {p \<in> - P. matches \<gamma> m a p} = (P \<union> - {p. matches \<gamma> m a p})"
  "- {p. matches \<gamma> m a p} =  {p. \<not> matches \<gamma> m a p}"
by blast+


fun collect_allow_compl_impl :: "'a rule list \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
  "collect_allow_compl_impl [] P = packet_set_UNIV" |
  "collect_allow_compl_impl ((Rule m Accept)#rs) P = packet_set_intersect 
      (packet_set_union P  (packet_set_not (to_packet_set Accept m))) (collect_allow_compl_impl rs (packet_set_opt (packet_set_union P (to_packet_set Accept m))))" |
  "collect_allow_compl_impl ((Rule m Drop)#rs) P = (collect_allow_compl_impl rs (packet_set_opt (packet_set_union P (to_packet_set Drop m))))"


lemma collect_allow_compl_impl: "simple_ruleset rs \<Longrightarrow> 
  packet_set_to_set \<gamma> (collect_allow_compl_impl rs P) = - collect_allow \<gamma> rs (- packet_set_to_set \<gamma>  P)"
apply(simp add: collect_allow_compl_correct[symmetric] )
apply(induction rs P arbitrary: P rule: collect_allow_impl_v1.induct)
apply(simp_all add: simple_ruleset_def packet_set_union_correct packet_set_opt_correct packet_set_intersect_intersect packet_set_not_correct
    to_packet_set_set set_helper1 packet_set_UNIV )
done


text\<open>take @{text "UNIV"} setminus the intersect over the result and get the set of allowed packets\<close>
fun collect_allow_compl_impl_tailrec :: "'a rule list \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set list \<Rightarrow> 'a packet_set list" where
  "collect_allow_compl_impl_tailrec [] P PAs = PAs" |
  "collect_allow_compl_impl_tailrec ((Rule m Accept)#rs) P PAs =
     collect_allow_compl_impl_tailrec rs (packet_set_opt (packet_set_union P (to_packet_set Accept m)))  ((packet_set_union P  (packet_set_not (to_packet_set Accept m)))# PAs)" |
  "collect_allow_compl_impl_tailrec ((Rule m Drop)#rs) P PAs = collect_allow_compl_impl_tailrec rs (packet_set_opt (packet_set_union P (to_packet_set Drop m))) PAs"


lemma collect_allow_compl_impl_tailrec_helper: "simple_ruleset rs \<Longrightarrow> 
  (packet_set_to_set \<gamma> (collect_allow_compl_impl rs P)) \<inter> (\<Inter> set (map (packet_set_to_set \<gamma>) PAs)) =
  (\<Inter> set (map (packet_set_to_set \<gamma>) (collect_allow_compl_impl_tailrec rs P PAs)))"
proof(induction rs P arbitrary: PAs P rule: collect_allow_compl_impl.induct)
  case (2 m rs)
    from 2 have IH: "(\<And>P PAs. packet_set_to_set \<gamma> (collect_allow_compl_impl rs P) \<inter> (\<Inter>x\<in>set PAs. packet_set_to_set \<gamma> x) =
                       (\<Inter>x\<in>set (collect_allow_compl_impl_tailrec rs P PAs). packet_set_to_set \<gamma> x))"
    by(simp add: simple_ruleset_def)
    from IH[where P="(packet_set_opt (packet_set_union P (to_packet_set Accept m)))" and PAs="(packet_set_union P (packet_set_not (to_packet_set Accept m)) # PAs)"] have
      "(packet_set_to_set \<gamma> P \<union> {p. \<not> matches \<gamma> m Accept p}) \<inter> 
       packet_set_to_set \<gamma> (collect_allow_compl_impl rs (packet_set_opt (packet_set_union P (to_packet_set Accept m)))) \<inter>
       (\<Inter>x\<in>set PAs. packet_set_to_set \<gamma> x) =
       (\<Inter>x\<in>set
        (collect_allow_compl_impl_tailrec rs (packet_set_opt (packet_set_union P (to_packet_set Accept m))) (packet_set_union P (packet_set_not (to_packet_set Accept m)) # PAs)).
          packet_set_to_set \<gamma> x)"
        apply(simp add: packet_set_union_correct packet_set_not_correct to_packet_set_set) by blast
    thus ?case
    by(simp add: packet_set_union_correct packet_set_opt_correct packet_set_intersect_intersect packet_set_not_correct
        to_packet_set_set set_helper1 packet_set_constrain_not_correct)
qed(simp_all add: simple_ruleset_def packet_set_union_correct packet_set_opt_correct packet_set_intersect_intersect packet_set_not_correct
      to_packet_set_set set_helper1 packet_set_constrain_not_correct packet_set_UNIV packet_set_Empty_def)


lemma collect_allow_compl_impl_tailrec_correct: "simple_ruleset rs \<Longrightarrow> 
  (packet_set_to_set \<gamma> (collect_allow_compl_impl rs P)) = (\<Inter>x\<in>set (collect_allow_compl_impl_tailrec rs P []). packet_set_to_set \<gamma> x)"
using collect_allow_compl_impl_tailrec_helper[where PAs="[]", simplified]
by metis


definition allow_set_not_inter :: "'a rule list \<Rightarrow> 'a packet_set list" where
  "allow_set_not_inter rs \<equiv> collect_allow_compl_impl_tailrec rs packet_set_Empty []"

text\<open>Intersecting over the result of @{const allow_set_not_inter} and inverting is the list of all allowed packets\<close>
lemma allow_set_not_inter: "simple_ruleset rs \<Longrightarrow> 
  - (\<Inter>x\<in>set (allow_set_not_inter rs). packet_set_to_set \<gamma> x) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
  unfolding allow_set_not_inter_def
  apply(simp add: collect_allow_compl_impl_tailrec_correct[symmetric])
  apply(simp add:collect_allow_compl_impl)
  apply(simp add: packet_set_Empty)
  using collect_allow_sound_complete by fast 

text\<open>this gives the set of denied packets\<close>
lemma "simple_ruleset rs \<Longrightarrow> has_default rs \<Longrightarrow> 
  (\<Inter>x\<in>set (allow_set_not_inter rs). packet_set_to_set \<gamma> x) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny}"
apply(frule simple_imp_good_ruleset)
apply(drule(1) has_default_UNIV[where \<gamma>=\<gamma>])
apply(drule allow_set_not_inter[where \<gamma>=\<gamma>])
(*apply(drule HOL.arg_cong[where f="\<lambda>x. - x"])
back
apply(simp)
try0 now its fast*)
by force (*>2s on my system!*)



end
