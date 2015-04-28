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

  (*definition in_iface_matches :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
    "in_iface_matches iiface m = True" (*todo: primitive extractor and (match_iface i (p_iiface p)) for any packet?*)
      (*ANY packet? well any with iiface, this should be straight forward*)*)

  (*TODO: verify this algorithm first*)
  (*will not be complete, but sound!*)
  private fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr set \<Rightarrow> bool" where
    "no_spoofing_algorithm iface ipassmt [] allowed denied \<longleftrightarrow> 
      (allowed - denied) \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Accept)#rs) allowed denied = no_spoofing_algorithm iface ipassmt rs 
        (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>)}) denied" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Drop)#rs) allowed denied = no_spoofing_algorithm iface ipassmt rs
         allowed (denied \<union> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>)})"  |
    "no_spoofing_algorithm _ _ _ _ _ = undefined"

  (*implementation could store ipv4addr set as 32 wordinterval*)


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

  private lemma setbydecision_setbydecision_all: "(setbydecision iface rs FinalAllow - setbydecision_all iface rs FinalDeny) = setbydecision iface rs FinalAllow"
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
       apply blast
      apply(simp)
      apply(safe)
      apply(drule notin_setbydecisionD)
      apply(rule_tac x="p" in exI)
      apply(simp)
      (* okay, if we can make sure that this particular packet was not denied before, we are done here *)
       oops

  private lemma "simple_ruleset rs1 \<Longrightarrow> simple_ruleset rs2 \<Longrightarrow>
        iface \<in> dom ipassmt \<Longrightarrow>
        allowed = setbydecision iface rs1 FinalAllow \<Longrightarrow>
        denied = setbydecision_all iface rs1 FinalDeny \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs2 allowed denied \<longleftrightarrow> 
        nospoof iface ipassmt (rs1@rs2)"
  proof(induction iface ipassmt rs2 allowed denied arbitrary: rs1 allowed denied rule: no_spoofing_algorithm.induct)
  print_cases
  case 1 thus ?case by(simp add: nospoof_setbydecision setbydecision_setbydecision_all)
  next
  case (2 iface ipassmt r rs)
    from 2(2) have simple_rs1: "simple_ruleset rs1" by(simp add: simple_ruleset_def)
    hence simple_rs': "simple_ruleset (rs1 @ [Rule r Accept])" by(simp add: simple_ruleset_def)
    from 2(3) have simple_rs: "simple_ruleset rs" by(simp add: simple_ruleset_def)
    with 2 have IH: "\<And>rs' allowed denied.
      simple_ruleset rs' \<Longrightarrow>
      allowed = setbydecision iface rs' FinalAllow \<Longrightarrow>
      denied = setbydecision_all iface rs' FinalDeny \<Longrightarrow> 
      no_spoofing_algorithm iface ipassmt rs allowed denied = nospoof iface ipassmt (rs' @ rs)"
      by(simp)
    from 2(5) have allowed: "(allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) r Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}) = 
           setbydecision iface (rs1 @ [Rule r Accept]) FinalAllow"
      sorry
    from IH[OF simple_rs' allowed] show ?case
      apply(simp)
      sorry
  next
  case 3 thus ?case sorry
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
  
end


end