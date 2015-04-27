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

  (*should be sound:
      if no_spoofing certifies your ruleset, then your ruleset prohibits spoofing
    may not be complete:
      no_spoofing may return False even though your ruleset prevents spoofing
      (should only occur if some strange and unknown primitives occur)*)

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
    oops

  definition in_iface_matches :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
    "in_iface_matches iiface m = True" (*todo: primitive extractor and (match_iface i (p_iiface p)) for any packet?*)
      (*ANY packet? well any with iiface, this should be straight forward*)

  (*TODO: verify this algorithm first*)
  fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr set \<Rightarrow> bool" where
    "no_spoofing_algorithm iface ipassmt [] allowed denied \<longleftrightarrow> 
      (allowed - denied) \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Accept)#rs) allowed denied = (if in_iface_matches iface m
        then
          no_spoofing_algorithm iface ipassmt rs (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_src:= ip\<rparr>)}) denied
        else
          no_spoofing_algorithm iface ipassmt rs allowed denied)" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Drop)#rs) allowed denied = (if in_iface_matches iface m
        then
          no_spoofing_algorithm iface ipassmt rs allowed (denied \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_src:= ip\<rparr>)})
        else
          no_spoofing_algorithm iface ipassmt rs allowed denied)"  |
    "no_spoofing_algorithm _ _ _ _ _ = undefined"

  (*implementation could store ipv4addr set as 32 wordinterval*)


  definition "nospoof iface ipassmt rs = (\<forall>p.
          (approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow) \<longrightarrow>
              p_src p \<in> (ipv4cidr_union_set (the (ipassmt iface))))"
  definition "setbydecition iface rs dec = {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"
  lemma "simple_ruleset rs2 \<Longrightarrow>
        iface \<in> dom ipassmt \<Longrightarrow>
        allowed = setbydecition iface rs1 FinalAllow \<Longrightarrow>
        denied = setbydecition iface rs1 FinalDeny \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs2 allowed denied \<longleftrightarrow> 
        nospoof iface ipassmt (rs1@rs2)"
  apply(induction iface ipassmt rs2 allowed denied arbitrary: rs1 allowed denied rule: no_spoofing_algorithm.induct)
          apply(simp_all add: simple_ruleset_def)
    apply(simp add: setbydecition_def nospoof_def)
    defer
    apply safe
    apply(simp_all)
    
  oops
*)
end