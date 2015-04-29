theory No_Spoof
imports Common_Primitive_Matcher
  "../Common/Negation_Type_DNF"
        Primitive_Normalization
begin

section{*No Spoofing*}
(* we do this in ternary (not simple firewall) to support things such as negated interfaces *)
  text{*assumes: @{const simple_ruleset}*}

  text{*A mapping from an interface to its assigned ip addresses in CIDR notation*}
  type_synonym ipassignment="iface \<rightharpoonup> (ipv4addr \<times> nat) set"

  (*
  check wool: warning if zone-spanning
  
  warning if interface map has wildcards
  
  warning if interface occurs in ruleset but not in ipassignment (typo?)
  *)

  text{*
  No spoofing means:
  Every packet that is (potentially) allowed by the firewall and comes from an interface @{text iface} 
  must have a Source IP Address in the assigned range @{text iface}.
  
  ``potentially allowed'' means we use the upper closure.
  The definition states: For all interfaces which are configured, every packet that comes from this
  interface and is allowed by the firewall must be in the IP range of that interface.
  *}
  definition no_spoofing :: "ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> bool" where
    "no_spoofing ipassmt rs \<equiv> \<forall> iface \<in> dom ipassmt. \<forall>p.
        ((common_matcher, in_doubt_allow),p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow) \<longrightarrow>
            p_src p \<in> (ipv4cidr_union_set (the (ipassmt iface)))"

  text{* The definition is sound (if that can be said about a definition):
          if @{const no_spoofing} certifies your ruleset, then your ruleset prohibits spoofing.
         The definition may not be complete:
          @{const no_spoofing} may return @{const False} even though your ruleset prevents spoofing
          (should only occur if some strange and unknown primitives occur)*}


text{*everything in the following context is just an unfinished draft*}
context
begin
(*
and now code to check this ....
  only need to trace: src_ip and iiface
  try some packet_set dnf with this?
  collect all src_ips allowed for a specific iiface?
  check collected src_ips subseteq ipassignment(iface)
*)
  (*
  definition get_matching_src_ips :: "common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_matching_src_ips m \<equiv> \<Union> ips \<in> set (fst (primitive_extractor (is_Src, src_sel) m)).  
                                  (case ips of Pos ip \<Rightarrow> ipv4s_to_set ip | Neg ip \<Rightarrow> - ipv4s_to_set ip)"
                (*todo: primitive extractor and 32wordinterval?*)

                (* only makes sense if there is a packet which can match*)

  (*TODO: action!*)
  lemma "normalized_nnf_match m \<Longrightarrow> get_matching_src_ips m = {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_src:= ip\<rparr>)}"
    unfolding get_matching_src_ips_def
    apply(rule Set.equalityI)
     apply(safe)
     apply(cases "primitive_extractor (is_Src, src_sel) m")
     apply(frule_tac p="p\<lparr>p_src:= x\<rparr>" in primitive_extractor_correct(1)[OF _ wf_disc_sel_common_primitive(3), where \<gamma>="(common_matcher, in_doubt_allow)" and a=a])
      apply(simp)
     apply(simp)
     apply(simp split: negation_type.split_asm)
    oops*)


  (*will not be complete, but sound!*)
  private fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr set \<Rightarrow> bool" where
    "no_spoofing_algorithm iface ipassmt [] allowed denied \<longleftrightarrow> 
      (allowed - denied) \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Accept)#rs) allowed denied = no_spoofing_algorithm iface ipassmt rs 
        (allowed \<union> {ip. (*ip \<notin> denied \<and>*) (\<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))}) denied" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Drop)#rs) allowed denied = no_spoofing_algorithm iface ipassmt rs
         allowed (denied \<union> ({ip.(\<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))} - allowed))"  |
    "no_spoofing_algorithm _ _ _ _ _ = undefined"

  (*implementation could store ipv4addr set as 32 wordinterval*)

  (*we can tune accuracy when only adding to allowed if it is not in denied?*)


  private definition "nospoof iface ipassmt rs = (\<forall>p.
          (approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow) \<longrightarrow>
              p_src p \<in> (ipv4cidr_union_set (the (ipassmt iface))))"
  private definition "setbydecision iface rs dec = {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"

  private lemma packet_update_simp: "p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr> = p\<lparr>p_src := x, p_iiface := iface_sel iface\<rparr>" by simp
 
  private lemma nospoof_setbydecision: "nospoof iface ipassmt rs \<longleftrightarrow> setbydecision iface rs FinalAllow \<subseteq> (ipv4cidr_union_set (the (ipassmt iface)))"
  proof
    assume a: "nospoof iface ipassmt rs"
    from a show "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      apply(simp add: nospoof_def setbydecision_def)
      apply(safe)
      apply(rename_tac x p)
      apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr>" in allE)
      apply(simp)
      apply(simp add: packet_update_simp)
      done
  next
    assume a1: "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
    show "nospoof iface ipassmt rs"
      unfolding nospoof_def
      proof(safe)
        fix p
        assume a2: "approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow"
        --{*In @{text setbydecision_fix_p}the @{text \<exists>} quantifier is gone and we consider this set for @{term p}.*}
        let ?setbydecision_fix_p="{ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision FinalAllow}"
        from a1 a2 have 1: "?setbydecision_fix_p \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" by(simp add: nospoof_def setbydecision_def) blast
        from a2 have 2: "p_src p \<in> ?setbydecision_fix_p" by simp
        from 1 2 show "p_src p \<in> ipv4cidr_union_set (the (ipassmt iface))" by blast
      qed
  qed


  private definition "setbydecision_all iface rs dec = {ip. \<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"

  private lemma setbydecision_setbydecision_all_Allow: "(setbydecision iface rs FinalAllow - setbydecision_all iface rs FinalDeny) = 
      setbydecision iface rs FinalAllow"
    apply(safe)
    apply(simp add: setbydecision_def setbydecision_all_def)
    done
  private lemma setbydecision_setbydecision_all_Deny: "(setbydecision iface rs FinalDeny - setbydecision_all iface rs FinalAllow) = 
      setbydecision iface rs FinalDeny"
    apply(safe)
    apply(simp add: setbydecision_def setbydecision_all_def)
    done

  (*follows directly from existing lemmas, move into proof below, do not move to generic thy!*)
  private lemma decision_append: "simple_ruleset rs1 \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs1 Undecided = Decision X \<Longrightarrow>
           approximating_bigstep_fun \<gamma> p (rs1 @ rs2) Undecided = Decision X"
    apply(drule simple_imp_good_ruleset)
    apply(drule good_imp_wf_ruleset[of _ \<gamma> p])
    apply(simp add: approximating_bigstep_fun_seq_wf Decision_approximating_bigstep_fun)
    done

  private lemma setbydecision_append: "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision iface (rs1 @ rs2) FinalAllow =
          setbydecision iface rs1 FinalAllow \<union> {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs2 Undecided = Decision FinalAllow \<and>
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}"
      apply(simp add: setbydecision_def)
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_cong)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      by blast

  private lemma not_FinalAllow: "foo \<noteq> Decision FinalAllow \<longleftrightarrow> foo = Decision FinalDeny \<or> foo = Undecided"
    apply(cases foo)
     apply simp_all
    apply(rename_tac x2)
    apply(case_tac x2)
     apply(simp_all)
    done

  private lemma setbydecision_all_appendAccept: "simple_ruleset (rs @ [Rule r Accept]) \<Longrightarrow> 
    setbydecision_all iface rs FinalDeny = setbydecision_all iface (rs @ [Rule r Accept]) FinalDeny"
      apply(simp add: setbydecision_all_def)
      apply(rule Set.Collect_cong)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(simp add: not_FinalAllow)
      done

  lemma "(\<forall>x. P x \<and> Q x) \<longleftrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)" by blast
  lemma "(\<forall>x. P x) \<or> (\<forall>x. Q x) \<Longrightarrow> (\<forall>x. P x \<or> Q x)" by blast

  private lemma setbydecision_all_append_subset: "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision_all iface rs1 FinalDeny \<union> {ip. \<forall>p.
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs2 Undecided = Decision FinalDeny \<and>
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}
            \<subseteq>
            setbydecision_all iface (rs1 @ rs2) FinalDeny"
      unfolding setbydecision_all_def
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(simp add: not_FinalAllow)
      done

  private lemma Collect_minus_eq: "{x. P x} - {x. Q x} = {x. P x \<and> \<not> Q x}" by blast

  private lemma "setbydecision_all iface rs1 FinalDeny \<union>
                 {ip. \<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}
                 \<subseteq>
                 - setbydecision iface rs1 FinalAllow"
      unfolding setbydecision_all_def
      unfolding setbydecision_def
      apply(subst Set.Collect_neg_eq[symmetric])
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      by(simp)


  private lemma setbydecision_all_append_subset2:
      "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision_all iface rs1 FinalDeny \<union> (setbydecision_all iface rs2 FinalDeny - setbydecision iface rs1 FinalAllow)
            \<subseteq> setbydecision_all iface (rs1 @ rs2) FinalDeny"
      unfolding setbydecision_all_def
      unfolding setbydecision_def
      apply(subst Collect_minus_eq)
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(intro impI allI)
      apply(simp add: not_FinalAllow)
      apply(case_tac "approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr>) rs1 Undecided")
       apply(elim disjE)
        apply(simp_all)[2]
      apply(rename_tac x2)
      apply(case_tac x2)
       prefer 2
       apply simp
      apply(elim disjE)
       apply(simp)
      by blast

  private lemma notin_setbydecisionD: "ip \<notin> setbydecision iface rs FinalAllow \<Longrightarrow> (\<forall>p.
      approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision FinalDeny \<or>
      approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided)"
    by(simp add: setbydecision_def not_FinalAllow)
  
  private lemma helper1: "a \<and> (a \<longrightarrow> b) \<longleftrightarrow> a \<and> b" by auto

  private lemma "simple_ruleset (rs @ [Rule r Accept]) \<Longrightarrow> 
         (setbydecision iface rs FinalAllow \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) r Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}) = 
           setbydecision iface (rs @ [Rule r Accept]) FinalAllow"
      apply(simp add: setbydecision_append)
      apply(simp add: helper1)
      apply(rule)
       prefer 2
       apply blast (*have ?r \<subseteq> ?l. would this suffice for an approximation (sound but not complete) of nospoof?*)
      apply(simp)
      apply(safe)
      apply(drule notin_setbydecisionD)
      apply(rule_tac x="p" in exI)
      apply(simp)
      (* okay, if we can make sure that this particular packet was not denied before, we are done here *)
       oops

  private lemma assumes "simple_ruleset (rs @ [Rule m Drop])" shows "
    (setbydecision_all iface rs FinalDeny \<union> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})
    \<subseteq>
    setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny
    "
    proof -
    from setbydecision_all_append_subset[OF assms, of iface] have 1: "setbydecision_all iface rs FinalDeny \<union>
      {ip. \<forall>p.
        approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) [Rule m Drop] Undecided = Decision FinalDeny \<and>
        approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided}
      \<subseteq> setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny" by simp
    from setbydecision_all_append_subset2[OF assms, of iface] have x1:
      "setbydecision_all iface rs FinalDeny \<union> (setbydecision_all iface [Rule m Drop] FinalDeny - setbydecision iface rs FinalAllow)
      \<subseteq> setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny" by simp
    have 2: "setbydecision_all iface rs FinalDeny \<union>
  {ip. \<forall>p. 
    approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) [Rule m Drop] Undecided = Decision FinalDeny \<and>
    approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided} 
      \<subseteq>
   setbydecision_all iface rs FinalDeny \<union> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}"
    apply(simp add: helper1)
    apply(rule)
    by auto
    have 3: "{ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} =
       setbydecision_all iface [Rule m Drop] FinalDeny"
       by(simp add: setbydecision_all_def)
    show ?thesis
      unfolding 3
      unfolding setbydecision_all_def
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       defer
       apply(simp_all)
    oops

  private lemma no_spoofing_algorithm_sound_generalized: "simple_ruleset rs1 \<Longrightarrow> simple_ruleset rs2 \<Longrightarrow>
        iface \<in> dom ipassmt \<Longrightarrow>
        setbydecision iface rs1 FinalAllow \<subseteq> allowed \<Longrightarrow> (* = *)
        denied \<subseteq> setbydecision_all iface rs1 FinalDeny \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs2 allowed denied \<Longrightarrow> (*\<longleftrightarrow>*)
        nospoof iface ipassmt (rs1@rs2)"
  proof(induction iface ipassmt rs2 allowed denied arbitrary: rs1 allowed denied rule: no_spoofing_algorithm.induct)
  case (1 iface ipassmt)
    from 1 have "allowed - denied \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      by(simp)
    with 1 have "setbydecision iface rs1 FinalAllow - setbydecision_all iface rs1 FinalDeny \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      by blast
    thus ?case by(simp add: nospoof_setbydecision setbydecision_setbydecision_all_Allow)
  next
  case (2 iface ipassmt m rs)
    from 2(2) have simple_rs1: "simple_ruleset rs1" by(simp add: simple_ruleset_def)
    hence simple_rs': "simple_ruleset (rs1 @ [Rule m Accept])" by(simp add: simple_ruleset_def)
    from 2(3) have simple_rs: "simple_ruleset rs" by(simp add: simple_ruleset_def)
    with 2 have IH: "\<And>rs' allowed denied.
      simple_ruleset rs' \<Longrightarrow>
      setbydecision iface rs' FinalAllow \<subseteq> allowed \<Longrightarrow>
      denied \<subseteq> setbydecision_all iface rs' FinalDeny \<Longrightarrow> 
      no_spoofing_algorithm iface ipassmt rs allowed denied \<Longrightarrow> nospoof iface ipassmt (rs' @ rs)"
      by(simp)
    from 2(5) simple_rs' have allowed: "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> 
      (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})" 
      apply(simp add: setbydecision_append)
      apply(simp add: helper1)
      by blast
    from 2(6) setbydecision_all_appendAccept[OF simple_rs'] have denied: "denied \<subseteq> setbydecision_all iface (rs1 @ [Rule m Accept]) FinalDeny" by simp

    from 2(7) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs
         (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}) denied"
      by(simp)

    from IH[OF simple_rs' allowed denied no_spoofing_algorithm_prems] have "nospoof iface ipassmt ((rs1 @ [Rule m Accept]) @ rs)" by blast
    thus ?case by(simp)
  next
  case (3 iface ipassmt m rs)
    from 3(2) have simple_rs1: "simple_ruleset rs1" by(simp add: simple_ruleset_def)
    hence simple_rs': "simple_ruleset (rs1 @ [Rule m Drop])" by(simp add: simple_ruleset_def)
    from 3(3) have simple_rs: "simple_ruleset rs" by(simp add: simple_ruleset_def)
    with 3 have IH: "\<And>rs' allowed denied.
      simple_ruleset rs' \<Longrightarrow>
      setbydecision iface rs' FinalAllow \<subseteq> allowed \<Longrightarrow>
      denied \<subseteq> setbydecision_all iface rs' FinalDeny \<Longrightarrow> 
      no_spoofing_algorithm iface ipassmt rs allowed denied \<Longrightarrow> nospoof iface ipassmt (rs' @ rs)"
      by(simp)
    from 3(5) simple_rs' have allowed: "setbydecision iface (rs1 @ [Rule m Drop]) FinalAllow \<subseteq> allowed "
      by(simp add: setbydecision_append)
    
    have "{ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} \<subseteq> 
          setbydecision_all iface [Rule m Drop] FinalDeny" by(simp add: setbydecision_all_def)
    with 3(5) have "setbydecision_all iface rs1 FinalDeny \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
          setbydecision_all iface rs1 FinalDeny \<union> (setbydecision_all iface [Rule m Drop] FinalDeny - setbydecision iface rs1 FinalAllow)"
      by blast
    with 3(6) setbydecision_all_append_subset2[OF simple_rs', of iface] have denied:
     "denied \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
      setbydecision_all iface (rs1 @ [Rule m Drop]) FinalDeny"
      by blast

    from 3(7) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs allowed
     (denied \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed))"
      by(simp)

    from IH[OF simple_rs' allowed denied no_spoofing_algorithm_prems] have "nospoof iface ipassmt ((rs1 @ [Rule m Drop]) @ rs)" by blast
    thus ?case by(simp)
  next
  case "4_1" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_2" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_3" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_4" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_5" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_6" thus ?case by(simp add: simple_ruleset_def)
  qed
  private corollary no_spoofing_algorithm_sound: "simple_ruleset rs \<Longrightarrow>
        iface \<in> dom ipassmt \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs {} {} \<Longrightarrow> nospoof iface ipassmt rs"
    apply(rule no_spoofing_algorithm_sound_generalized[of "[]" rs iface ipassmt "{}" "{}", simplified])
        apply(simp_all)
     apply(simp add: simple_ruleset_def)
    apply(simp add: setbydecision_def)
    done
    
  
end


end