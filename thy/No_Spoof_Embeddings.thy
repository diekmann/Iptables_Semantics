theory No_Spoof_Embeddings
imports "Semantics_Embeddings"
        "Primitive_Matchers/No_Spoof"
begin


section{*Spoofing protection in Ternary Semantics implies Spoofing protection Boolean Semantics*}
text{*If @{const no_spoofing} is shown in the ternary semantics, it implies that no spoofing
        is possible in the Boolean semantics with magic oracle.
        We only assume that the oracle agrees with the @{const common_matcher} on the not-unknown parts.*}
  lemma approximating_imp_booloan_semantics_nospoofing: 
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" and "simple_ruleset rs" and no_spoofing: "no_spoofing ipassmt rs"
      shows "\<forall> iface \<in> dom ipassmt. \<forall>p. (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow) \<longrightarrow>
                p_src p \<in> (ipv4cidr_union_set (set (the (ipassmt iface))))"
      unfolding no_spoofing_def
      proof(intro ballI allI impI)
        fix iface p
        assume i: "iface \<in> dom ipassmt"
           and a: "\<Gamma>,\<gamma>,p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"

        from no_spoofing[unfolded no_spoofing_def] i have no_spoofing':
          "(common_matcher, in_doubt_allow),p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longrightarrow>
           p_src p \<in> ipv4cidr_union_set (set (the (ipassmt iface)))" by blast

        from assms simple_imp_good_ruleset FinalAllows_subseteq_in_doubt_allow[where rs=rs] have
          "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq> {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}" 
          by blast
        with a have "(common_matcher, in_doubt_allow),p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow" by blast
        with no_spoofing' show "p_src p \<in> ipv4cidr_union_set (set (the (ipassmt iface)))"by blast
      qed

 (*expressed as set*)
  corollary
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" and "simple_ruleset rs" and no_spoofing: "no_spoofing ipassmt rs" and "iface \<in> dom ipassmt"
      shows "{p_src p | p . (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipv4cidr_union_set (set (the (ipassmt iface)))"
      using approximating_imp_booloan_semantics_nospoofing[OF assms(1) assms(2) assms(3), where \<Gamma>=\<Gamma>]
      using assms(4) by blast


 (*expressed as set*)
  corollary no_spoofing_executable_set:
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher"
          and "simple_ruleset rs"
          and "\<forall>r\<in>set rs. normalized_nnf_match (get_match r)"
          and no_spoofing_executable: "\<forall>iface \<in> dom ipassmt. no_spoofing_iface iface ipassmt rs"
          and "iface \<in> dom ipassmt"
      shows "{p_src p | p . (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipv4cidr_union_set (set (the (ipassmt iface)))"
  proof -
    { assume no_spoofing: "no_spoofing ipassmt rs"
      have "{p_src p | p . (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipv4cidr_union_set (set (the (ipassmt iface)))"
      using approximating_imp_booloan_semantics_nospoofing[OF assms(1) assms(2) no_spoofing, where \<Gamma>=\<Gamma>]
      using assms(5) by blast
    }
    with no_spoofing_iface[OF assms(2) assms(3) no_spoofing_executable] show ?thesis by blast
  qed

end