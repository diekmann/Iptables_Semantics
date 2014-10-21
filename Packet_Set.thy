theory Packet_Set
imports Fixed_Action "Output_Format/Negation_Type_Matching" Datatype_Selectors
begin


section{*Util: listprod*}
    definition listprod :: "nat list \<Rightarrow> nat" where "listprod as \<equiv> foldr (op *) as 1"
    (*better: "'a::comm_semiring_1 list \<Rightarrow> 'a"*)
    lemma listprod_append[simp]: "listprod (as @ bs) =  listprod as * listprod bs"
     apply(induction as arbitrary: bs)
      apply(simp_all add: listprod_def)
     done
    lemma listprod_simps [simp]:
      "listprod [] = 1"
      "listprod (x # xs) = x * listprod xs"
      by (simp_all add: listprod_def)
    lemma "distinct as \<Longrightarrow> listprod as = \<Prod>(set as)"
      by(induction as) simp_all



section{*Packet Set*}
(*probably everything here wants a simple ruleset*)


(*TODO: collect_by_action
has_Default \<Longrightarrow> UNIV - collect_drop = collect_allow
*)

subsection{*The set of all accepted packets*}
  text{*
  Collect all packets which are allowed by the firewall.
  *}
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
    show ?case (is ?goal)
    proof(cases a)
      case Accept
        from Accept Cons.IH[where P="{p \<in> P. \<not> matches \<gamma> m Accept p}"] simple_rs have IH:
          "p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p} \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow" by simp
        from Accept Cons.prems have "(p \<in> P \<and> matches \<gamma> m Accept p) \<or> p \<in> collect_allow \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Accept p}"
          by(simp add: r)
        with Accept show ?goal
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
        with Cons show ?goal
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
    show ?case (is ?goal)
    proof(cases a)
      case Accept
        from Accept Cons.IH simple_rs have IH: "\<forall>P. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow \<longrightarrow> p \<in> P \<longrightarrow> p \<in> collect_allow \<gamma> rs P" by simp
        with Accept Cons.prems show ?goal
          apply(cases "matches \<gamma> m Accept p")
           apply(simp add: r)
          apply(simp add: r)
          done
      next
      case Drop
        with Cons show ?goal 
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


  text{*the complement of the allowed packets*}
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

subsection{*The set of all dropped packets*}
  text{*
  Collect all packets which are denied by the firewall.
  *}
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
    show ?case (is ?goal)
    proof(cases a)
      case Drop
        from Drop Cons.IH[where P="{p \<in> P. \<not> matches \<gamma> m Drop p}"] simple_rs have IH:
          "p \<in> collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p} \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny" by simp
        from Drop Cons.prems have "(p \<in> P \<and> matches \<gamma> m Drop p) \<or> p \<in> collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> m Drop p}"
          by(simp add: r)
        with Drop show ?goal
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
        with Cons show ?goal
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
    show ?case (is ?goal)
    proof(cases a)
      case Accept
        from Accept Cons.IH simple_rs have IH: "\<forall>P. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny \<longrightarrow> p \<in> P \<longrightarrow> p \<in> collect_deny \<gamma> rs P" by simp
        with Accept Cons.prems show ?goal
          apply(cases "matches \<gamma> m Accept p")
           apply(simp add: r)
          apply(simp add: r)
          done
      next
      case Drop
        with Cons show ?goal 
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
  
  text{*the complement of the denied packets*}
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
      from 3 have IH: "\<And>P. - collect_deny_compl \<gamma> rs (- P) = collect_deny \<gamma> rs P" using simple_ruleset_tail by blast
      from IH[where P="{p \<in> P. \<not> matches \<gamma> r Drop p}"] set_simp1 have
        "- collect_deny_compl \<gamma> rs (- P \<union> Collect (matches \<gamma> r Drop)) = collect_deny \<gamma> rs {p \<in> P. \<not> matches \<gamma> r Drop p}" by simp
      thus ?case by auto
    qed(simp_all add: simple_ruleset_def)

subsection{*Rulesets with default rules*}
  definition has_default :: "'a rule list \<Rightarrow> bool" where
    "has_default rs \<equiv> length rs > 0 \<and> ((last rs = Rule MatchAny Accept) \<or> (last rs = Rule MatchAny Drop))"

  lemma has_default_UNIV: "good_ruleset rs \<Longrightarrow> has_default rs \<Longrightarrow>
    {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow} \<union> {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalDeny} = UNIV"
  apply(induction rs)
   apply(simp add: has_default_def)
  apply(rename_tac r rs)
  apply(simp add: has_default_def good_ruleset_tail split: split_if_asm)
   apply(elim disjE)
    apply(simp add: bunch_of_lemmata_about_matches)
   apply(simp add: bunch_of_lemmata_about_matches)
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
  


subsection{*Executable Packet Set Representation*}

text{*Recall: @{const alist_and} transforms @{typ "'a negation_type list \<Rightarrow> 'a match_expr"} and uses conjunction as connective. *}

text{*Symbolic (executable) representation. inner is @{text \<and>}, outer is @{text \<or>}*}
(*we remember the action which might be necessary for applying \<alpha>*)
(*the @{typ "'a"} negation type tells whether to negate the match expression*)
(*test: the action negation tells whether to negate the result of the match*)
(*due to unknowns, this may make a huge difference!*)
datatype_new 'a packet_set = PacketSet (packet_set_repr: "(('a negation_type \<times> action negation_type) list) list")

text{*Essentially, the @{typ "'a list list"} structure represents a DNF. See @{file "Negation_Type_DNF.thy"} for a pure Boolean version (without matching).*}

definition to_packet_set :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set" where
 "to_packet_set a m = PacketSet (map (map (\<lambda>m'. (m',Pos a)) o to_negation_type_nnf) (normalize_match m))"

fun get_action :: "action negation_type \<Rightarrow> action" where
  "get_action (Pos a) = a" |
  "get_action (Neg a) = a"

fun get_action_sign :: "action negation_type \<Rightarrow> (bool \<Rightarrow> bool)" where
  "get_action_sign (Pos _) = id" |
  "get_action_sign (Neg _) = (\<lambda>m. \<not> m)"

text{*
We collect all entries of the outer list.
For the inner list, we request that a packet matches all the entries.
A negated action means that the expression must not match.
Recall: @{term "matches \<gamma> (MatchNot m) a p \<noteq> (\<not> matches \<gamma> m a p)"}, due to @{const TernaryUnknown}
*}
definition packet_set_to_set :: "('a, 'packet) match_tac \<Rightarrow> 'a packet_set \<Rightarrow> 'packet set" where
  "packet_set_to_set \<gamma> ps \<equiv> \<Union> ms \<in> set (packet_set_repr ps).  {p. \<forall> (m, a) \<in> set ms. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)}"

lemma packet_set_to_set_alt:  "packet_set_to_set \<gamma> ps = (\<Union> ms \<in> set (packet_set_repr ps).  
  {p. \<forall> m a. (m, a) \<in> set ms \<longrightarrow> get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)})"
unfolding packet_set_to_set_def
by fast

lemma to_packet_set_correct: "p \<in> packet_set_to_set \<gamma> (to_packet_set a m) \<longleftrightarrow> matches \<gamma> m a p"
apply(simp add: to_packet_set_def packet_set_to_set_def)
apply(rule iffI)
 apply(clarify)
 apply(induction m rule: normalize_match.induct)
       apply(simp_all add: bunch_of_lemmata_about_matches)
   apply force
apply (metis matches_DeMorgan)
apply(induction m rule: normalize_match.induct)
      apply(simp_all add: bunch_of_lemmata_about_matches)
 apply (metis Un_iff)
apply (metis Un_iff matches_DeMorgan)
done

lemma to_packet_set_set: "packet_set_to_set \<gamma> (to_packet_set a m) = {p. matches \<gamma> m a p}"
using to_packet_set_correct by fast

definition packet_set_UNIV :: "'a packet_set" where
  "packet_set_UNIV \<equiv> PacketSet [[]]"
lemma packet_set_UNIV: "packet_set_to_set \<gamma> packet_set_UNIV = UNIV"
by(simp add: packet_set_UNIV_def packet_set_to_set_def)

definition packet_set_Empty :: "'a packet_set" where
  "packet_set_Empty \<equiv> PacketSet []"
lemma packet_set_Empty: "packet_set_to_set \<gamma> packet_set_Empty = {}"
by(simp add: packet_set_Empty_def packet_set_to_set_def)

text{*If the matching agrees for two actions, then the packet sets are also equal*}
lemma "\<forall>p. matches \<gamma> m a1 p \<longleftrightarrow> matches \<gamma> m a2 p \<Longrightarrow> packet_set_to_set \<gamma> (to_packet_set a1 m) = packet_set_to_set \<gamma> (to_packet_set a2 m)"
apply(subst(asm) to_packet_set_correct[symmetric])+
apply safe
apply simp_all
done

subsubsection{*Basic Set Operations*}
  
  text{* @text{\<inter>} *}
    fun packet_set_intersect :: "'a packet_set \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_intersect (PacketSet olist1) (PacketSet olist2) = PacketSet [andlist1 @ andlist2. andlist1 <- olist1, andlist2 <- olist2]"
    
    lemma "packet_set_intersect (PacketSet [[a,b], [c,d]]) (PacketSet [[v,w], [x,y]]) = PacketSet [[a, b, v, w], [a, b, x, y], [c, d, v, w], [c, d, x, y]]" by simp
    
    declare packet_set_intersect.simps[simp del]
    
    
    lemma packet_set_intersect_intersect: "packet_set_to_set \<gamma> (packet_set_intersect P1 P2) = packet_set_to_set \<gamma> P1 \<inter> packet_set_to_set \<gamma> P2"
    unfolding packet_set_to_set_def
     apply(cases P1)
     apply(cases P2)
     apply(simp)
     apply(simp add: packet_set_intersect.simps)
     apply blast
    done
    
    
    lemma packet_set_intersect_correct: "packet_set_to_set \<gamma> (packet_set_intersect (to_packet_set a m1) (to_packet_set a m2)) = packet_set_to_set \<gamma> (to_packet_set a (MatchAnd m1 m2))"
     apply(simp add: to_packet_set_def packet_set_intersect.simps packet_set_to_set_alt)
     (*by fast very slow!*)
     apply safe
     apply simp_all
     apply blast+
     done
     
    lemma packet_set_intersect_correct': "p \<in> packet_set_to_set \<gamma> (packet_set_intersect (to_packet_set a m1) (to_packet_set a m2)) \<longleftrightarrow> matches \<gamma> (MatchAnd m1 m2) a p"
    apply(simp add: to_packet_set_correct[symmetric])
    using packet_set_intersect_correct by fast
  
    text{*The length of the result is the product of the input lengths*}
    lemma packet_set_intersetc_length: "length (packet_set_repr (packet_set_intersect (PacketSet ass) (PacketSet bss))) = length ass * length bss"
      by(induction ass) (simp_all add: packet_set_intersect.simps)
      

  
  text{* @text{\<union>} *}
    fun packet_set_union :: "'a packet_set \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_union (PacketSet olist1) (PacketSet olist2) = PacketSet (olist1 @ olist2)"
    declare packet_set_union.simps[simp del]
    
    lemma packet_set_union_correct: "packet_set_to_set \<gamma> (packet_set_union P1 P2) = packet_set_to_set \<gamma> P1 \<union> packet_set_to_set \<gamma> P2"
    unfolding packet_set_to_set_def
     apply(cases P1)
     apply(cases P2)
     apply(simp add: packet_set_union.simps)
    done
  
    lemma packet_set_append:
      "packet_set_to_set \<gamma> (PacketSet (p1 @ p2)) = packet_set_to_set \<gamma> (PacketSet p1) \<union> packet_set_to_set \<gamma> (PacketSet p2)"
      by(simp add: packet_set_to_set_def)
    lemma packet_set_cons: "packet_set_to_set \<gamma> (PacketSet (a # p3)) =  packet_set_to_set \<gamma> (PacketSet [a]) \<union> packet_set_to_set \<gamma> (PacketSet p3)"
      by(simp add: packet_set_to_set_def)
  
  

  text{* @text{-} *}
    fun listprepend :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
      "listprepend [] ns = []" |
      "listprepend (a#as) ns = (map (\<lambda>xs. a#xs) ns) @ (listprepend as ns)"
    
    text{*The returned result of @{const listprepend} can get long.*}
    lemma listprepend_length: "length (listprepend as bss) = length as * length bss"
      by(induction as) (simp_all)
    
    lemma packet_set_map_a_and: "packet_set_to_set \<gamma> (PacketSet (map (op # a) ds)) = packet_set_to_set \<gamma> (PacketSet [[a]]) \<inter> packet_set_to_set \<gamma> (PacketSet ds)"
      apply(induction ds)
       apply(simp_all add: packet_set_to_set_def)
      apply(case_tac a)
       apply(simp_all)
       apply blast+
      done
    lemma listprepend_correct: "packet_set_to_set \<gamma> (PacketSet (listprepend as ds)) = packet_set_to_set \<gamma> (PacketSet (map (\<lambda>a. [a]) as)) \<inter> packet_set_to_set \<gamma> (PacketSet ds)"
      apply(induction as arbitrary: )
       apply(simp add: packet_set_to_set_alt)
      apply(simp)
      apply(rename_tac a as)
      apply(simp add: packet_set_map_a_and packet_set_append)
      (*using packet_set_cons by fast*)
      apply(subst(2) packet_set_cons)
      by blast
    
    lemma packet_set_to_set_map_singleton: "packet_set_to_set \<gamma> (PacketSet (map (\<lambda>a. [a]) as)) = (\<Union> a \<in> set as. packet_set_to_set \<gamma> (PacketSet [[a]]))"
    by(simp add: packet_set_to_set_alt)
    
    fun invertt :: "('a negation_type \<times> action negation_type) \<Rightarrow> ('a negation_type \<times> action negation_type)" where
      "invertt (n, a) = (n, invert a)"
    
    lemma singleton_invertt: "packet_set_to_set \<gamma> (PacketSet [[invertt n]]) =  - packet_set_to_set \<gamma> (PacketSet [[n]])"
     apply(simp add: to_packet_set_def packet_set_intersect.simps packet_set_to_set_alt)
     apply(case_tac n, rename_tac m a)
     apply(simp)
     apply(case_tac a)
      apply(simp_all)
      apply safe
     done
    
    lemma packet_set_to_set_map_singleton_invertt: 
      "packet_set_to_set \<gamma> (PacketSet (map ((\<lambda>a. [a]) \<circ> invertt) d)) = - (\<Inter> a \<in> set d. packet_set_to_set \<gamma> (PacketSet [[a]]))"
    apply(induction d)
     apply(simp)
     apply(simp add: packet_set_to_set_alt)
    apply(simp add: )
    apply(subst(1) packet_set_cons)
    apply(simp)
    apply(simp add: packet_set_to_set_map_singleton singleton_invertt)
    done
    
    fun packet_set_not_internal :: " ('a negation_type \<times> action negation_type) list list \<Rightarrow>  ('a negation_type \<times> action  negation_type) list list" where
      "packet_set_not_internal [] = [[]]" |
      "packet_set_not_internal (ns#nss) = listprepend (map invertt ns) (packet_set_not_internal nss)"

    lemma packet_set_not_internal_length: "length (packet_set_not_internal ass) = listprod ([length n. n <- ass])"
      by(induction ass) (simp_all add: listprepend_length)
    
    lemma packet_set_not_internal_correct: "packet_set_to_set \<gamma> (PacketSet (packet_set_not_internal d)) = - packet_set_to_set \<gamma> (PacketSet d)"
      apply(induction d)
       apply(simp add: packet_set_to_set_alt)
      apply(rename_tac d ds)
      apply(simp add: )
      apply(simp add: listprepend_correct)
      apply(simp add: packet_set_to_set_map_singleton_invertt)
      apply(simp add: packet_set_to_set_alt)
      by blast
    
    fun packet_set_not :: "'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_not (PacketSet ps) = PacketSet (packet_set_not_internal ps)"
    declare packet_set_not.simps[simp del]

    text{*The length of the result of @{const packet_set_not} is the multiplication over the length of all the inner sets.
      Warning: gets huge!
      See @{thm packet_set_not_internal_length}
    *}
    
    lemma packet_set_not_correct: "packet_set_to_set \<gamma> (packet_set_not P) = - packet_set_to_set \<gamma> P"
    apply(cases P)
    apply(simp)
    apply(simp add: packet_set_not.simps)
    apply(simp add: packet_set_not_internal_correct)
    done

subsubsection{*Derived Operations*}
  definition packet_set_constrain :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_constrain a m ns = packet_set_intersect ns (to_packet_set a m)"
  
  theorem packet_set_constrain_correct: "packet_set_to_set \<gamma> (packet_set_constrain a m P) = {p \<in> packet_set_to_set \<gamma> P. matches \<gamma> m a p}"
  unfolding packet_set_constrain_def
  unfolding packet_set_intersect_intersect
  unfolding to_packet_set_set
  by blast
  
  text{*Warning: result gets hue*}
  definition packet_set_constrain_not :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_constrain_not a m ns = packet_set_intersect ns (packet_set_not (to_packet_set a m))"
  
  theorem packet_set_constrain_not_correct: "packet_set_to_set \<gamma> (packet_set_constrain_not a m P) = {p \<in> packet_set_to_set \<gamma> P. \<not> matches \<gamma> m a p}"
  unfolding packet_set_constrain_not_def
  unfolding packet_set_intersect_intersect
  unfolding packet_set_not_correct
  unfolding to_packet_set_set
  by blast


subsubsection{*Optimizing*}
  fun packet_set_opt1 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt1 (PacketSet ps) = PacketSet (map remdups (remdups ps))"
  declare packet_set_opt1.simps[simp del]
  
  lemma packet_set_opt1_correct: "packet_set_to_set \<gamma> (packet_set_opt1 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_to_set_alt packet_set_opt1.simps)


  fun packet_set_opt2_internal :: "(('a negation_type \<times> action negation_type) list) list \<Rightarrow> (('a negation_type \<times> action negation_type) list) list" where
    "packet_set_opt2_internal [] = []" |

    "packet_set_opt2_internal ([]#ps) = [[]]" | (*If UNIV is included, the whole expression is UNIV*)

    (*"packet_set_opt2_internal ([a]#ps) = ([a]#(filter (\<lambda>as. a \<notin> set as) ps))" |*)

    (*if a more permissive expression is encountered, we can drop all less-permissive ones*)
    "packet_set_opt2_internal (as#ps) = (as#(filter (\<lambda>ass. \<not> set as \<subseteq> set ass) ps))" (*this might be horribly inefficient ...*)

  lemma packet_set_opt2_internal_correct: "packet_set_to_set \<gamma> (PacketSet (packet_set_opt2_internal ps)) = packet_set_to_set \<gamma> (PacketSet ps)"
    apply(induction ps rule:packet_set_opt2_internal.induct)
    apply(simp_all add: packet_set_UNIV)
    apply(simp add: packet_set_to_set_alt)
    apply(simp add: packet_set_to_set_alt)
    apply(safe)[1]
    apply(simp_all)
    apply blast+
    (*apply(simp add: packet_set_to_set_alt)
    apply(safe)[1]
    apply(simp_all)
    apply blast+*)
    done
    
  export_code packet_set_opt2_internal in SML

  fun packet_set_opt2 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt2 (PacketSet ps) = PacketSet (packet_set_opt2_internal ps)" 
  declare packet_set_opt2.simps[simp del]

  lemma packet_set_opt2_correct: "packet_set_to_set \<gamma> (packet_set_opt2 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_opt2.simps packet_set_opt2_internal_correct)


  text{*If we sort by length, we will hopefully get better results when applying @{const packet_set_opt2}.*}
  fun packet_set_opt3 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt3 (PacketSet ps) = PacketSet (sort_key (\<lambda>p. length p) ps)" (*quadratic runtime of sort?*)
  declare packet_set_opt3.simps[simp del]
  lemma packet_set_opt3_correct: "packet_set_to_set \<gamma> (packet_set_opt3 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_opt3.simps packet_set_to_set_alt)
  

  (*TODO: ugly proof*)
  fun packet_set_opt4_internal_internal :: "(('a negation_type \<times> action negation_type) list) \<Rightarrow> bool" where
    "packet_set_opt4_internal_internal cs = (\<forall> (m, a) \<in> set cs. (m, invert a) \<notin> set cs)"
  fun packet_set_opt4 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt4 (PacketSet ps) = PacketSet (filter packet_set_opt4_internal_internal ps)"
  declare packet_set_opt4.simps[simp del]
  lemma packet_set_opt4_internal_internal_helper: assumes
      "\<forall>m a. (m, a) \<in> set xb \<longrightarrow> get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (Packet_Set.get_action a) xa)"
   shows "\<forall>(m, a)\<in>set xb. (m, invert a) \<notin> set xb"
   proof(clarify)
    fix a b
    assume a1: "(a, b) \<in> set xb" and a2: "(a, invert b) \<in> set xb"
    from assms a1 have 1: "get_action_sign b (matches \<gamma> (negation_type_to_match_expr a) (Packet_Set.get_action b) xa)" by simp
    from assms a2 have 2: "get_action_sign (invert b) (matches \<gamma> (negation_type_to_match_expr a) (Packet_Set.get_action (invert b)) xa)" by simp
    from 1 2 show "False"
      by(cases b) (simp_all)
   qed
  lemma packet_set_opt4_correct: "packet_set_to_set \<gamma> (packet_set_opt4 ps) = packet_set_to_set \<gamma> ps"
    apply(cases ps, clarify)
    apply(simp add: packet_set_opt4.simps packet_set_to_set_alt)
    apply(rule)
     apply blast
    apply(clarify)
    apply(simp)
    apply(rule_tac x=xb in exI)
    apply(simp)
    using packet_set_opt4_internal_internal_helper by fast


  definition packet_set_opt :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt ps = packet_set_opt1 (packet_set_opt2 (packet_set_opt3 (packet_set_opt4 ps)))" 

  lemma packet_set_opt_correct: "packet_set_to_set \<gamma> (packet_set_opt ps) = packet_set_to_set \<gamma> ps"
    using packet_set_opt_def packet_set_opt2_correct packet_set_opt3_correct packet_set_opt4_correct packet_set_opt1_correct by metis


text{*with @{thm packet_set_constrain_correct} and @{thm packet_set_constrain_not_correct}, it should be possible to build an executable version of the algorithm above.*}




subsection{*The set of all accepted packets -- Executable Implementation*}
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

(*
not needed atm
lemma opt_packet_set_constrain_not: "packet_set_to_set \<gamma> (opt P) = packet_set_to_set \<gamma> P \<Longrightarrow> 
  packet_set_to_set \<gamma> (packet_set_constrain_not a m (opt P)) = packet_set_to_set \<gamma> (packet_set_constrain_not a m P)"
apply(simp_all add: packet_set_union_correct packet_set_constrain_correct packet_set_constrain_not_correct)
done

lemma collect_allow_impl_unoptimized_optP: "simple_ruleset rs \<Longrightarrow> packet_set_to_set \<gamma> (opt P) = packet_set_to_set \<gamma> P \<Longrightarrow>
  packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (opt P)) = packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs P)"
proof(induction \<gamma> rs P arbitrary: P opt  rule: collect_allow_impl_unoptimized.induct)
  case 1 thus ?case by simp
next
  case (2 \<gamma> m rs)
  from 2 have "simple_ruleset rs" by (simp add: simple_ruleset_def)
  with 2 have IH: "(\<And>P opt. packet_set_to_set \<gamma> (opt P) = packet_set_to_set \<gamma> P \<Longrightarrow>
                 packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (opt P)) = packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs P))" by simp
  from 2 opt_packet_set_constrain_not have" packet_set_to_set \<gamma> (packet_set_constrain_not Accept m (opt P)) = packet_set_to_set \<gamma> (packet_set_constrain_not Accept m P)" by metis
  from IH[OF this] have IH': "packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (packet_set_constrain_not Accept m (opt P))) =
      packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (packet_set_constrain_not Accept m P))" by simp
  from 2 have prems: "packet_set_to_set \<gamma> (opt P) = packet_set_to_set \<gamma> P" by simp
  from prems IH' show ?case
    apply(simp_all add: packet_set_union_correct packet_set_constrain_correct packet_set_constrain_not_correct)
    done
next
  case (3 \<gamma> m rs)
  from 3 have "simple_ruleset rs" by (simp add: simple_ruleset_def)
  with 3 have IH: "(\<And>P opt. packet_set_to_set \<gamma> (opt P) = packet_set_to_set \<gamma> P \<Longrightarrow>
                 packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (opt P)) = packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs P))" by simp
  from 3 opt_packet_set_constrain_not have"packet_set_to_set \<gamma> (packet_set_constrain_not Drop m (opt P)) = packet_set_to_set \<gamma> (packet_set_constrain_not Drop m P)" by metis
  from IH[OF this] have IH': "packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (packet_set_constrain_not Drop m (opt P))) =
      packet_set_to_set \<gamma> (collect_allow_impl_unoptimized \<gamma> rs (packet_set_constrain_not Drop m P))" by simp
  thus ?case by simp
qed(simp_all add: simple_ruleset_def)
*)

lemma collect_allow_impl_v2: "simple_ruleset rs \<Longrightarrow> packet_set_to_set \<gamma> (collect_allow_impl_v2 rs P) = packet_set_to_set \<gamma> (collect_allow_impl_v1 rs P)"
apply(induction rs P arbitrary: P  rule: collect_allow_impl_v1.induct)
apply(simp_all add: simple_ruleset_def packet_set_union_correct packet_set_opt_correct packet_set_constrain_not_correct collect_allow_impl_v1)
done


text{*executable!*}
export_code collect_allow_impl_v2 in SML


theorem collect_allow_impl_v1_sound_complete: "simple_ruleset rs \<Longrightarrow> 
  packet_set_to_set \<gamma> (collect_allow_impl_v1 rs packet_set_UNIV) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
apply(simp add: collect_allow_impl_v1 packet_set_UNIV)
using collect_allow_sound_complete by fast

corollary collect_allow_impl_v2_sound_complete: "simple_ruleset rs \<Longrightarrow> 
  packet_set_to_set \<gamma> (collect_allow_impl_v2 rs packet_set_UNIV) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
using collect_allow_impl_v1_sound_complete collect_allow_impl_v2 by fast




text{*instead of the expensive invert and intersect operations, we try to build the algorithm primarily by union*}
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

(*
fun collect_allow_compl_v1 :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
  "collect_allow_compl_v1 _ [] P = {}" |
  "collect_allow_compl_v1 \<gamma> ((Rule m Accept)#rs) P = {p \<in> - P. matches \<gamma> m Accept p} \<union> (collect_allow_compl_v1 \<gamma> rs (P \<union> {p. matches \<gamma> m Accept p}))" |
  "collect_allow_compl_v1 \<gamma> ((Rule m Drop)#rs) P = (collect_allow_compl_v1 \<gamma> rs (P \<union> {p. matches \<gamma> m Drop p}))"

lemma collect_allow_compl_v1_correct': "simple_ruleset rs \<Longrightarrow> ( collect_allow_compl_v1 \<gamma> rs P) = collect_allow \<gamma> rs (- P)"
apply(induction \<gamma> rs P arbitrary: P rule: collect_allow.induct)
apply(simp_all)
defer defer
apply(simp_all add: simple_ruleset_def)[6]
apply(simp_all add: simple_ruleset_tail)
apply(simp_all add: set_helper1(1))
done
lemma collect_allow_compl_v1_correct: "simple_ruleset rs \<Longrightarrow> ( collect_allow_compl_v1 \<gamma> rs (- P)) = collect_allow \<gamma> rs P"
using collect_allow_compl_v1_correct'[where P="- P", simplified] by blast

fun collect_allow_compl_v2 :: "('a, 'p) match_tac \<Rightarrow> 'a rule list \<Rightarrow> 'p set \<Rightarrow> 'p set" where
  "collect_allow_compl_v2 _ [] P = UNIV" |
  "collect_allow_compl_v2 \<gamma> ((Rule m Accept)#rs) P = (P \<union> {p. \<not>matches \<gamma> m Accept p}) \<inter> (collect_allow_compl_v2 \<gamma> rs (P \<union> {p. matches \<gamma> m Accept p}))" |
  "collect_allow_compl_v2 \<gamma> ((Rule m Drop)#rs) P = (collect_allow_compl_v2 \<gamma> rs (P \<union> {p. matches \<gamma> m Drop p}))"

lemma collect_allow_compl_v2_correct: "simple_ruleset rs \<Longrightarrow> (- collect_allow_compl_v1 \<gamma> rs P) = collect_allow_compl_v2 \<gamma> rs P"
apply(induction \<gamma> rs P arbitrary: P rule: collect_allow.induct)
apply(simp_all)
defer defer
apply(simp_all add: simple_ruleset_def)[6]
apply(simp_all add: simple_ruleset_tail)
apply(simp_all add: set_helper1(3) set_helper1(2)[simplified])
done
*)


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


text{*take @{text "UNIV"} setminus the intersect over the result and get the set of allowed packets*}
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

text{*Intersecting over the result of @{const allow_set_not_inter} and inverting is the list of all allowed packets*}
lemma allow_set_not_inter: "simple_ruleset rs \<Longrightarrow> 
  - (\<Inter>x\<in>set (allow_set_not_inter rs). packet_set_to_set \<gamma> x) = {p. approximating_bigstep_fun \<gamma> p rs Undecided = Decision FinalAllow}"
  unfolding allow_set_not_inter_def
  apply(simp add: collect_allow_compl_impl_tailrec_correct[symmetric])
  apply(simp add:collect_allow_compl_impl)
  apply(simp add: packet_set_Empty)
  using collect_allow_sound_complete by fast 


end
