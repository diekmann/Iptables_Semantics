theory Access_Matrix_Embeddings
imports "Semantics_Embeddings"
        "Primitive_Matchers/No_Spoof"
        "../Simple_Firewall/Service_Matrix"
begin

section{*Applying the Access Matrix to the Bigstep Semantics*}
  
text{*
If the real iptables firewall (@{const iptables_bigstep}) accepts a packet, we have a corresponding
edge in the @{const access_matrix}.
*}
corollary access_matrix_and_bigstep_semantics:
  defines "preprocess rs \<equiv> upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs)))"
  and     "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  fixes \<gamma> :: "'i::len common_primitive \<Rightarrow> ('i, 'pkt_ext) tagged_packet_scheme \<Rightarrow> bool"
  and   p :: "('i::len, 'pkt_ext) tagged_packet_scheme"
  assumes agree:"matcher_agree_on_exact_matches \<gamma> common_matcher"
  and     simple: "simple_ruleset rs"
  and     new: "newpkt p"             
  and     matrix: "(V,E) = access_matrix \<lparr>pc_iiface = p_iiface p, pc_oiface = p_oiface p, pc_proto = p_proto p, pc_sport = p_sport p, pc_dport = p_dport p\<rparr> (to_simple_firewall (preprocess rs))"
  and     accept: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"
  shows "\<exists>s_repr d_repr s_range d_range. (s_repr, d_repr) \<in> set E \<and>
              (map_of V) s_repr = Some s_range \<and> (p_src p) \<in> wordinterval_to_set s_range \<and>
              (map_of V) d_repr = Some d_range \<and> (p_dst p) \<in> wordinterval_to_set d_range"
proof -
  let ?c="\<lparr> pc_iiface = p_iiface p, c_oiface = p_oiface p, pc_proto = p_proto p,
           pc_sport = p_sport p, pc_dport = p_dport p \<rparr>"
  from new_packets_to_simple_firewall_overapproximation[OF agree simple] have
    "{p. \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow \<and> newpkt p}
      \<subseteq>
     {p. simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow \<and> newpkt p}"
    unfolding preprocess_def newpkt_def by blast
  with accept new have "simple_fw (to_simple_firewall (preprocess rs)) p = Decision FinalAllow" by blast
  hence "runFw_scheme (p_src p) (p_dst p) ?c p (to_simple_firewall (preprocess rs)) = Decision FinalAllow"
    by(simp add: runFw_scheme_def)
  hence "runFw (p_src p) (p_dst p) ?c (to_simple_firewall (preprocess rs)) = Decision FinalAllow"
    by(simp add: runFw_scheme[symmetric])
  with access_matrix[OF matrix] show ?thesis by presburger
qed

(*Actually, I want to_simple_firewall_without_interfaces so we don't depend on interfaces*)
corollary access_matrix_no_interfaces_and_bigstep_semantics:
  defines "newpkt p \<equiv> match_tcp_flags ipt_tcp_syn (p_tcp_flags p) \<and> p_tag_ctstate p = CT_New"
  fixes \<gamma> :: "'i::len common_primitive \<Rightarrow> ('i, 'pkt_ext) tagged_packet_scheme \<Rightarrow> bool"
  and   p :: "('i::len, 'pkt_ext) tagged_packet_scheme"
  assumes agree:"matcher_agree_on_exact_matches \<gamma> common_matcher"
  and     simple: "simple_ruleset rs"
      --"To get the best results, we want to rewrite all interfaces, which needs some preconditions"
      (*TODO: actually, we use iface_try_rewrite which should work without assumptions but may give bad (but sound) results*)
      --"well-formed ipassmt"
      and wf_ipassmt1: "ipassmt_sanity_nowildcards (map_of ipassmt)" and wf_ipassmt2: "distinct (map fst ipassmt)"
      --"There are no spoofed packets (probably by kernel's reverse path filter or our checker).
         This assumption implies that ipassmt lists ALL interfaces (!!)."
      and nospoofing: "\<forall>(p::('i::len, 'pkt_ext) tagged_packet_scheme).
            \<exists>ips. (map_of ipassmt) (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipcidr_union_set (set ips)"
      --"If a routing table was passed, the output interface for any packet we consider is decided based on it."
      and routing_decided: "\<And>rtbl (p::('i,'pkt_ext) tagged_packet_scheme). rtblo = Some rtbl \<Longrightarrow> output_iface (routing_table_semantics rtbl (p_dst p)) = p_oiface p"
      --"A passed routing table is wellformed"
      and correct_routing: "\<And>rtbl. rtblo = Some rtbl \<Longrightarrow> correct_routing rtbl"
      --"A passed routing table contains no interfaces with wildcard names"
      and routing_no_wildcards: "\<And>rtbl. rtblo = Some rtbl \<Longrightarrow> ipassmt_sanity_nowildcards (map_of (routing_ipassmt rtbl))"
  and     new: "newpkt p"
  --"building the matrix over ANY interfaces, not mentioned anywhere. That means, we don't care about interfaces!"
  and     matrix: "(V,E) = access_matrix \<lparr>pc_iiface = anyI, pc_oiface = anyO, pc_proto = p_proto p, pc_sport = p_sport p, pc_dport = p_dport p\<rparr>
                            (to_simple_firewall_without_interfaces ipassmt rtblo rs)"
  and     accept: "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> Decision FinalAllow"
  shows "\<exists>s_repr d_repr s_range d_range. (s_repr, d_repr) \<in> set E \<and>
              (map_of V) s_repr = Some s_range \<and> (p_src p) \<in> wordinterval_to_set s_range \<and>
              (map_of V) d_repr = Some d_range \<and> (p_dst p) \<in> wordinterval_to_set d_range"
proof -
  let ?c="\<lparr> pc_iiface = p_iiface p, c_oiface = p_oiface p, pc_proto = p_proto p,
           pc_sport = p_sport p, pc_dport = p_dport p \<rparr>"
  let ?srs="to_simple_firewall_without_interfaces ipassmt rtblo rs"
  note tosfw=to_simple_firewall_without_interfaces[OF simple wf_ipassmt1 wf_ipassmt2 nospoofing routing_decided correct_routing routing_no_wildcards, of rtblo, simplified]
  from tosfw(2) have no_ifaces: "simple_firewall_without_interfaces ?srs" unfolding simple_firewall_without_interfaces_def by fastforce
  from simple simple_imp_good_ruleset have "good_ruleset rs" by blast
  with accept FinalAllow_approximating_in_doubt_allow[OF agree] have accept_ternary:
    "(common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow" by blast
  from tosfw(1) have
    "{p.(common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<and> newpkt p}
      \<subseteq>
     {p. simple_fw ?srs p = Decision FinalAllow \<and> newpkt p}"
    unfolding newpkt_def by blast
  with accept_ternary new have "simple_fw ?srs p = Decision FinalAllow" by blast
  hence "runFw_scheme (p_src p) (p_dst p) ?c p ?srs = Decision FinalAllow"
    by(simp add: runFw_scheme_def)
  hence "runFw (p_src p) (p_dst p) ?c ?srs = Decision FinalAllow"
    by(simp add: runFw_scheme[symmetric])
  hence "runFw (p_src p) (p_dst p) 
          \<lparr>pc_iiface = anyI, pc_oiface = anyO, pc_proto = p_proto p, pc_sport = p_sport p, pc_dport = p_dport p\<rparr> ?srs = Decision FinalAllow"
    apply(subst runFw_no_interfaces[OF no_ifaces]) by simp
  with access_matrix[OF matrix] show ?thesis by presburger
qed
 
end