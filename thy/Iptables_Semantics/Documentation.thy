theory Documentation
imports Semantics_Embeddings
    Call_Return_Unfolding
    No_Spoof_Embeddings
    "Primitive_Matchers/Code_Interface"
begin



section\<open>Documentation\<close>

subsection\<open>General Model\<close>
text\<open>
The semantics of the filtering behavior of iptables is expressed by @{const iptables_bigstep}.
The notation @{term "\<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t"} reads as follows:
  @{term "\<Gamma> :: string \<rightharpoonup> 'a rule list"} is the background ruleset (user-defined rules).
  @{term \<gamma>} is a function @{typ "('a, 'p) matcher"} which is called the primitive matcher (i.e. the matching features supported by iptables).
  @{term "p :: 'p"} is the packet inspected by the firewall.
  @{term "rs :: 'a rule list"} is the ruleset.
  @{term "s :: state"} and @{term "t :: state"} are the start state and final state.


The semantics:
\begin{center}
@{thm[mode=Axiom] skip [no_vars]}\\[1ex]
@{thm[mode=Rule] accept [no_vars]}\\[1ex]
@{thm[mode=Rule] drop [no_vars]}\\[1ex]
@{thm[mode=Rule] reject [no_vars]}\\[1ex]
@{thm[mode=Rule] log [no_vars]}\\[1ex]
@{thm[mode=Rule] empty [no_vars]}\\[1ex]
@{thm[mode=Rule] nomatch [no_vars]}\\[1ex]
@{thm[mode=Rule] decision [no_vars]}\\[1ex]
@{thm[mode=Rule] seq [no_vars]} \\[1ex]
@{thm[mode=Rule] call_return [no_vars]}\\[1ex] 
@{thm[mode=Rule] call_result [no_vars]}
\end{center}
\<close>


subsection\<open>Unfolding the Ruleset\<close>

text\<open>We can replace all @{const Goto}s to terminal chains (chains that ultimately yield a final
  decision for every packet) with @{const Call}s.
  Otherwise we don't have as rich goto semantics as iptables has, but this rewriting is safe.

@{thm Semantics_Goto.rewrite_Goto_chain_safe [no_vars]}
\<close>

text\<open>The iptables firewall starts as follows:
  @{term "[Rule MatchAny (Call chain_name), Rule MatchAny default_action]"}
  We call to a built-in chain @{term chain_name}, usually INPUT, OUTPUT, or FORWARD.
  If we don't get a decision, iptables uses the default policy (-P) @{term default_action}.

  We can call @{const unfold_optimize_ruleset_CHAIN} to remove all calls to user-defined chains
  and other unpleasant actions. We get back a @{const simple_ruleset} which as exactly the same 
  behaviour. As a bonus, this @{const simple_ruleset} already has some match conditions optimized.

  For example, if the parser does not find a source IP in a rule, it is okay to specify
  -s 0.0.0.0/0, the unfolding will optimize away these things for you.
  Or if you parse iptables -L -n which always has these annoying 0.0.0.0/0 fields.
  May make the parser easier.
  The following lemma shows that this does not change the semantics.

\<close>
lemma unfold_optimize_common_matcher_univ_ruleset_CHAIN:
    --"for IPv4 and IPv6 packets"
    fixes \<gamma> :: "'i::len common_primitive \<Rightarrow> ('i, 'pkt_ext) tagged_packet_scheme \<Rightarrow> bool"
    and   p :: "('i::len, 'pkt_ext) tagged_packet_scheme"
    assumes "sanity_wf_ruleset \<Gamma>" and "chain_name \<in> set (map fst \<Gamma>)"
    and "default_action = action.Accept \<or> default_action = action.Drop"
    and "matcher_agree_on_exact_matches \<gamma> common_matcher"
    and "unfold_ruleset_CHAIN_safe chain_name default_action (map_of \<Gamma>) = Some rs"
    shows "(map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow> t \<longleftrightarrow>
           (map_of \<Gamma>),\<gamma>,p\<turnstile> \<langle>[Rule MatchAny (Call chain_name), Rule MatchAny default_action], s\<rangle> \<Rightarrow> t"
    and "simple_ruleset rs"
apply(intro unfold_optimize_ruleset_CHAIN[where optimize=optimize_primitive_univ, OF assms(1) assms(2) assms(3)])
  using assms apply(simp_all add: unfold_ruleset_CHAIN_safe_def Semantics_optimize_primitive_univ_common_matcher)
by(simp add: unfold_optimize_ruleset_CHAIN_def Let_def split: if_split_asm)


subsection\<open>Spoofing protection\<close>

text\<open>We provide an executable algorithm @{const no_spoofing_iface} which checks that a ruleset provides spoofing protection:

@{thm no_spoofing_executable_set [no_vars]}

Text the firewall needs normalized match conditions, this is a good way to preprocess the firewall before 
checking spoofing protection:

@{thm no_spoofing_executable_set_preprocessed [no_vars]}

\<close>

subsection\<open>Simple Firewall Model\<close>
text\<open>The simple firewall supports the following match conditions: @{typ "'i::len simple_match"}.

The @{const simple_fw} model is remarkably simple: @{thm simple_fw.simps [no_vars]}

We support translating to a stricter version (a version that accepts less packets): 

@{thm new_packets_to_simple_firewall_underapproximation [no_vars]}


We support translating to a more permissive version (a version that accepts more packets): 

@{thm new_packets_to_simple_firewall_overapproximation [no_vars]}



There is also a different approach to translate to the simple firewall which removes all matches on interfaces:

@{thm to_simple_firewall_without_interfaces[no_vars]}

\<close>


subsection\<open>Service Matrices\<close>
text\<open>
For a @{typ "'i::len simple_rule list"} and a fixed @{typ parts_connection}, 
we support to partition the IPv4 address space the following.

All members of a partition have the same access rights:
@{thm build_ip_partition_same_fw [no_vars]}

Minimal:
@{thm build_ip_partition_same_fw_min [no_vars]}


The resulting access control matrix is sound and complete:

@{thm access_matrix [no_vars]}

Theorem reads: 
For a fixed connection, you can look up IP addresses (source and destination pairs) in the matrix 
if and only if the firewall accepts this src,dst IP address pair for the fixed connection.
Note: The matrix is actually a graph (nice visualization!), you need to look up IP addresses 
in the Vertices and check the access of the representants in the edges. If you want to visualize
the graph (e.g. with Graphviz or tkiz): The vertices are the node description (i.e. header; 
  @{term "dom V"} is the label for each node which will also be referenced in the edges,
  @{term "ran V"} is the human-readable description for each node (i.e. the full IP range it represents)), 
the edges are the edges. Result looks nice. Theorem also tells us that this visualization is correct.
\<close>

  
(*TODO: service matrix without mentioning the simple firewall at all!*)
(*TODO move*)
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
