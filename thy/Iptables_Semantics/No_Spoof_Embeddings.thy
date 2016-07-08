theory No_Spoof_Embeddings
imports "Semantics_Embeddings"
        "Primitive_Matchers/No_Spoof"
begin


section\<open>Spoofing protection in Ternary Semantics implies Spoofing protection Boolean Semantics\<close>
text\<open>If @{const no_spoofing} is shown in the ternary semantics, it implies that no spoofing
        is possible in the Boolean semantics with magic oracle.
        We only assume that the oracle agrees with the @{const common_matcher} on the not-unknown parts.\<close>
  lemma approximating_imp_booloan_semantics_nospoofing: 
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher"
      and "simple_ruleset rs"
      and no_spoofing: "no_spoofing TYPE('pkt_ext) ipassmt rs"
      shows "\<forall> iface \<in> dom ipassmt. \<forall>p::('i::len,'pkt_ext) tagged_packet_scheme.
                (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow) \<longrightarrow>
                    p_src p \<in> (ipcidr_union_set (set (the (ipassmt iface))))"
      unfolding no_spoofing_def
      proof(intro ballI allI impI)
        fix iface p
        assume i: "iface \<in> dom ipassmt"
           and a: "\<Gamma>,\<gamma>,p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"

        from no_spoofing[unfolded no_spoofing_def] i have no_spoofing':
          "(common_matcher, in_doubt_allow),p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longrightarrow>
           p_src p \<in> ipcidr_union_set (set (the (ipassmt iface)))" by blast

        from assms simple_imp_good_ruleset FinalAllows_subseteq_in_doubt_allow[where rs=rs] have
          "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq> {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}" 
          by blast
        with a have "(common_matcher, in_doubt_allow),p\<lparr>p_iiface := iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow" by blast
        with no_spoofing' show "p_src p \<in> ipcidr_union_set (set (the (ipassmt iface)))"by blast
      qed

 (*expressed as set*)
  corollary
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher" and "simple_ruleset rs"
          and no_spoofing: "no_spoofing TYPE('pkt_ext) ipassmt rs" and "iface \<in> dom ipassmt"
      shows "{p_src p | p :: ('i::len,'pkt_ext) tagged_packet_scheme. (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipcidr_union_set (set (the (ipassmt iface)))"
      using approximating_imp_booloan_semantics_nospoofing[OF assms(1) assms(2) assms(3), where \<Gamma>=\<Gamma>]
      using assms(4) by blast


 (*expressed as set*)
  corollary no_spoofing_executable_set:
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher"
          and "simple_ruleset rs"
          and "\<forall>r\<in>set rs. normalized_nnf_match (get_match r)"
          and no_spoofing_executable: "\<forall>iface \<in> dom ipassmt. no_spoofing_iface iface ipassmt rs"
          and "iface \<in> dom ipassmt"
      shows "{p_src p | p :: ('i::len,'pkt_ext) tagged_packet_scheme. (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipcidr_union_set (set (the (ipassmt iface)))"
  proof -
    { assume no_spoofing: "no_spoofing TYPE('pkt_ext) ipassmt rs"
      have "{p_src p | p :: ('i,'pkt_ext) tagged_packet_scheme. (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
                 ipcidr_union_set (set (the (ipassmt iface)))"
      using approximating_imp_booloan_semantics_nospoofing[OF assms(1) assms(2) no_spoofing, where \<Gamma>=\<Gamma>]
      using assms(5) by blast
    }
    with no_spoofing_iface[OF assms(2) assms(3) no_spoofing_executable] show ?thesis by blast
  qed


  corollary no_spoofing_executable_set_preprocessed:
      fixes ipassmt :: "'i::len ipassignment"
      defines "preprocess rs \<equiv> upper_closure (packet_assume_new rs)"
          and "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
      assumes "matcher_agree_on_exact_matches \<gamma> common_matcher"
          and simplers: "simple_ruleset rs"
          and no_spoofing_executable: "\<forall>iface \<in> dom ipassmt. no_spoofing_iface iface ipassmt (preprocess rs)"
          and "iface \<in> dom ipassmt"
      shows "{p_src p | p :: ('i::len,'pkt_ext) tagged_packet_scheme. newpkt p \<and> \<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow} \<subseteq>
                 ipcidr_union_set (set (the (ipassmt iface)))"
  proof -
   have newpktD: "newpkt p \<Longrightarrow> newpkt (p\<lparr>p_iiface := iface_sel iface\<rparr>)" for p
     by(simp add: newpkt_def)
   from packet_assume_new_simple_ruleset[OF simplers] have s1: "simple_ruleset (packet_assume_new rs)" .
   from transform_upper_closure(2)[OF s1] have s2: "simple_ruleset (upper_closure (packet_assume_new rs))" .
   hence s2': "simple_ruleset (preprocess rs)" unfolding preprocess_def by simp
   have "\<forall>r\<in>set (preprocess rs). normalized_nnf_match (get_match r)"
     unfolding preprocess_def
     using transform_upper_closure(3)[OF s1] by simp

   from no_spoofing_iface[OF s2' this no_spoofing_executable] have nospoof: "no_spoofing TYPE('a) ipassmt (preprocess rs)" .

   from assms(3) have 1: "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p} \<subseteq>
                       {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
    apply(drule_tac rs=rs and \<Gamma>=\<Gamma> in FinalAllows_subseteq_in_doubt_allow)
     using simple_imp_good_ruleset assms(4) apply blast
    by blast
   have 2: "{p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p} \<subseteq>
         {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>preprocess rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}"
     unfolding newpkt_def preprocess_def
     apply(subst transform_upper_closure(1)[OF s1])
     apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF s1]])
     apply(subst approximating_semantics_iff_fun_good_ruleset[OF simple_imp_good_ruleset[OF simplers]])
     using packet_assume_new newpkt_def by force
   from 1 2 have "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p} \<subseteq>
         {p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>preprocess rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}" by simp
   hence p: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p \<Longrightarrow>
           (common_matcher, in_doubt_allow),p\<turnstile> \<langle>preprocess rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p" for p by blast
   have x: "{p_src p | p . newpkt p \<and> (\<Gamma>,\<gamma>,p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow)} \<subseteq>
            {p_src p | p . newpkt p \<and> (common_matcher, in_doubt_allow),p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>preprocess rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}"
     apply(safe, rename_tac p)
     apply(drule newpktD)
     apply(rule_tac x="p\<lparr>p_iiface := iface_sel iface\<rparr>" in exI)
     using p by simp
   note[[show_types]]
   with nospoof have y: 
    "{p_src p | p :: ('i::len,'pkt_ext) tagged_packet_scheme. newpkt p \<and> (common_matcher, in_doubt_allow),p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>preprocess rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow}
    \<subseteq> ipcidr_union_set (set (the (ipassmt iface)))"
    apply(simp add: no_spoofing_def)
    by(blast dest: bspec[OF _ assms(6)])
   from x y show ?thesis by simp
  qed

end