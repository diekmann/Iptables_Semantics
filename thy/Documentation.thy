theory Documentation
imports Semantics_Embeddings No_Spoof_Embeddings "Simple_Firewall/IPPartitioning"

begin

section{*Documentation*}

subsection{*General Model*}
text{*
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
*}


subsection{*Spoofing protection*}

text{*We provide an executable algorithm @{const no_spoofing_iface} which checks that a ruleset provides spoofing protection:

@{thm no_spoofing_executable_set [no_vars]}

*}

subsection{*Simple Firewall Model*}
text{*The simple firewall supports the following match conditions: @{typ simple_match}.

The @{const simple_fw} model is remarkably simple: @{thm simple_fw.simps [no_vars]}

We support translating to a stricter version (a version that accepts less packets): 

@{thm new_packets_to_simple_firewall_underapproximation [no_vars]}


We support translating to a more permissive version (a version that accepts more packets): 

@{thm new_packets_to_simple_firewall_overapproximation [no_vars]}

*}


subsection{*Service Matrices*}
text{*
For a @{typ "simple_rule list"} and a fixed @{typ parts_connection}, we support to partition the IPv4 address space the following.

All members of a partition have the same access rights:
@{thm build_ip_partition_same_fw [no_vars]}

Minimal:
@{thm build_ip_partition_same_fw_min [no_vars]}
*}

end
