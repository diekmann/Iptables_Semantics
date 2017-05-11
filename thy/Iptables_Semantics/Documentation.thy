theory Documentation
imports Semantics_Embeddings
    Call_Return_Unfolding
    No_Spoof_Embeddings
    Access_Matrix_Embeddings
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

text\<open>
A final theorem which does not mention the simple firewall at all.
If the real iptables firewall (@{const iptables_bigstep}) accepts a packet, we have a corresponding
edge in the @{const access_matrix}:

@{thm access_matrix_and_bigstep_semantics [no_vars]}


Actually, we want to ignore all interfaces for a service matrix.
This is done in @{thm access_matrix_no_interfaces_and_bigstep_semantics[no_vars]}.
The theorem reads a bit ugly because we need well-formedness assumptions if we rewrite interfaces.
Internally, it uses @{const iface_try_rewrite} which is pretty safe to use, even if you don't have
an @{term ipassmt} or routing tables.
\<close>

end
