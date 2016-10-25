text_raw\<open>
\twocolumn
\columnsep 2pc          %    Space between columns
\textwidth 42pc         % Width of text line.
\part{Documentation}
\label{part2}
\<close>
section\<open>Configuration Translation\<close>
text_raw\<open>\label{sec:conv}\<close>
text\<open>
All the results we present in this section are formalized and verified in Isabelle/HOL~\cite{nipkow2002isabelle}.
This means that their formal correctness can be trusted a level close to absolute certainty.
The definitions and lemmas stated here are merely a repetition of lemmas stated in other theory files.
This means that they have been directly set to this document from Isabelle and no typos or hidden assumptions are possible.
Additionally, it allows us to omit various helper lemmas that do not help the understanding.
However, it causes some notation inaccuracy, as type and function definitions are stated as lemmas or schematic goals.
\<close>
theory OpenFlow_Documentation
(*<*)
imports 
  LinuxRouter_OpenFlow_Translation 
  Featherweight_OpenFlow_Comparison
  "~~/src/HOL/Library/LaTeXsugar"
begin
(*>*)

subsection\<open>Linux Firewall Model\<close>
text_raw\<open>\label{sec:lfw}\<close>
text\<open>We want to write a program that translates the configuration of a linux firewall to that of an OpenFlow switch.
We furthermore want to verify that translation.
For this purpose, we need a clear definition of the behavior of the two device types -- we need their models and semantics.
In case of a linux firewall, this is problematic because a linux firewall is a highly complex device that is ultimately capable of general purpose computation.
Creating a comprehensive semantics that encompasses all possible configuration types of a linux firewall is thus 
highly non-trivial and not useful for the purpose of analysis.
We decided to approach the problem from the other side: we created a model that includes only the most basic features. (This implies neglecting IPv6.)
Fortunately, many of the highly complex features are rarely essential and even our basic model is still of some use.
\<close>

text\<open>We first divided the firewall into subsystems.
Given a routing table @{term rt}, the firewall rules @{term fw},
  the routing decision for a packet @{term p} can be obtained by @{term "routing_table_semantics rt (p_dst p)"}, 
  the firewall decision by @{term "simple_fw fw p"}.
We draft the first description of our linux router model:
\begin{enumerate}
  \item The destination MAC address of an arriving packet is checked: Does it match the MAC address of the ingress port? 
  If it does, we continue, otherwise, the packet is discarded.
  \item The routing decision @{term "rd \<equiv> routing_table_semantics rt p"} is obtained.
  \item The packet's output interface is updated based on @{term rd}\footnote{Note that we assume a packet model with input and output interfaces. The origin of this is explained in Section~\ref{sec:lfwfw}}.
  \item The firewall is queried for a decision: @{term "simple_fw fw p"}. If the decision is to @{const[names_short] simple_action.Drop}, the packet is discarded.
  \item The next hop is computed: If @{term rd} provides a next hop, that is used. 
    Otherwise, the destination address of the packet is used.
  \item The MAC address of the next hop is looked up; the packet is updated with it and sent.
\end{enumerate}
We decided that this description is best formalized as an abortable program in the option monad:\<close>
lemma "simple_linux_router rt fw mlf ifl p \<equiv> do {
	_ \<leftarrow> iface_packet_check ifl p;
	let rd (* routing decision *) = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
	let fd (* firewall decision *) = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	let nh = (case next_hop rd of None \<Rightarrow> p_dst p | Some a \<Rightarrow> a);
	ma \<leftarrow> mlf nh;
	Some (p\<lparr>p_l2dst := ma\<rparr>)
}" 
unfolding fromMaybe_def[symmetric] by(fact simple_linux_router_def)
text\<open>where @{term "mlf :: ipv4addr \<Rightarrow> 48 word"} is a function that looks up the MAC address for an IP address.\<close>

text\<open>There are already a few important aspects that have not been modelled, but they are not core essential for the functionality of a firewall.
Namely, there is no local traffic from/to the firewall.
This is problematic since this model can not generate ARP replies — thus, an equivalent OpenFlow device will not do so, either.
Furthermore, this model is problematic because it requires access to a function that looks up a MAC address, 
something that may not be known at the time of time running a translation to an OpenFlow configuration.
\<close>
text\<open>It is possible to circumvent these problems by inserting static ARP table entries in the directly connected devices 
and looking up their MAC addresses \emph{a priori}. 
A test-wise implementation of the translation based on this model showed acceptable results.
However, we deemed the \emph{a priori} lookup of the MAC addresses to be rather inelegant and built a second model.\<close>
definition "simple_linux_router_altered rt fw ifl p \<equiv> do {
	let rd = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
		_ \<leftarrow> if p_oiface p = p_iiface p then None else Some ();
	let fd = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some p
}"
(* TODO: Would a router actually forward a packet on the same interface? *)
text\<open>In this model, all access to the MAC layer has been eliminated.
This is done by the approximation that the firewall will be asked to route a packet 
(i.e. be addressed on the MAC layer) iff the destination IP address of the packet causes it to be routed out on a different interface.
Because this model does not insert destination MAC addresses, the destination MAC address has to be already correct when the packet is sent.
This can only be achieved by changing the subnet of all connected device, moving them into one common subnet\footnote{There are cases where this is not possible — A limitation of our system.}.
\<close>
text\<open>
While a test-wise implementation based on this model also showed acceptable results, the model is still problematic.
The check @{term "p_oiface p = p_iiface p"} and the firewall require access to the output interface.
The details of why this cannot be provided are be elaborated in Section~\ref{sec:convi}. 
The intuitive explanation is that an OpenFlow match can not have a field for the output interface.
We thus simplified the model even further:
\<close>
lemma "simple_linux_router_nol12 rt fw p \<equiv> do {
	let rd = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
	let fd = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some p
}" by(fact simple_linux_router_nol12_def)
text\<open>We continue with this definition as a basis for our translation.
Even this strongly altered version and the original linux firewall still behave the same in a substantial amount of cases:\<close>
theorem
	"\<lbrakk>iface_packet_check ifl pi \<noteq> None;
	mlf (case next_hop (routing_table_semantics rt (p_dst pi)) of None \<Rightarrow> p_dst pi | Some a \<Rightarrow> a) \<noteq> None\<rbrakk> \<Longrightarrow>
	\<exists>x. map_option (\<lambda>p. p\<lparr>p_l2dst := x\<rparr>) (simple_linux_router_nol12 rt fw pi) = simple_linux_router rt fw mlf ifl pi"
by(fact rtr_nomac_eq[unfolded fromMaybe_def])
text\<open>The conditions are to be read as ``The check whether a received packet has the correct destination MAC never returns @{const False}'' and 
``The next hop MAC address for all packets can be looked up''.
Obviously, these conditions do not hold for all packets. 
We will show an example where this makes a difference in Section~\ref{sec:mnex}.\<close>

subsubsection\<open>Routing Table\<close>
text_raw\<open>\label{sec:lfwr}\<close>
text\<open>
The routing system in linux features multiple tables and a system that can use the iptables firewall and an additional match language to select a routing table.
Based on our directive, we only focused on the single most used \texttt{main} routing table.\<close>
text\<open>
We define a routing table entry to be a record (named tuple) of a prefix match, a metric and the routing action, which in turn is a record of an output interface and an optional next-hop address.\<close>
schematic_goal "(?rtbl_entry :: ('a::len) routing_rule) = \<lparr> routing_match = PrefixMatch pfx len, metric = met, routing_action = \<lparr> output_iface = oif_string, next_hop = (h :: 'a word option) \<rparr> \<rparr>" ..
text\<open>A routing table is then a list of these entries:\<close>
lemma "(rtbl :: ('a :: len) prefix_routing) = (rtbl :: 'a routing_rule list)" by rule
text\<open>Not all members of the type @{type prefix_routing} are sane routing tables. There are three different validity criteria that we require so that our definitions are adequate.
\begin{itemize}
  \item The prefixes have to be 0 in bits exceeding their length.
  \item There has to be a default rule, i.e. one with prefix length 0. With the condition above, that implies that all its prefix bits are zero and it thus matches any address.
  \item The entries have to be sorted by prefix length and metric.
\end{itemize}
The first two are set into code in the following way:
\<close>
lemma "valid_prefix (PrefixMatch pfx len) \<equiv> pfx && (2 ^ (32 - len) - 1) = (0 :: 32 word)" 
unfolding valid_prefix_def pfxm_mask_def mask_def by (simp add: word_bw_comms(1))
lemma "has_default_route rt \<longleftrightarrow> (\<exists>r \<in> set rt. pfxm_length (routing_match r) = 0)" 
by(fact has_default_route_alt)
text\<open>The third is not needed in any of the further proofs, so we omit it.\<close>

text\<open>The semantics of a routing table is to simply traverse the list until a matching entry is found.\<close>
schematic_goal "routing_table_semantics (rt_entry # rt) dst_addr = (if prefix_match_semantics (routing_match rt_entry) dst_addr then routing_action rt_entry else routing_table_semantics rt dst_addr)" by(fact routing_table_semantics.simps)
text\<open>If no matching entry is found, the behavior is undefined.\<close>

subsubsection\<open>iptables Firewall\<close>
text_raw\<open>\label{sec:lfwfw}\<close>
text\<open>The firewall subsystem in a linux router is not any less complex than any of the of the other systems.
Fortunately, this complexity has been dealt with in~\cite{diekmann2016verified,Iptables_Semantics-AFP} already and we can directly use the result.\<close>
text\<open>In short, one of the results is that a complex \emph{iptables} configuration can be simplified to be represented by a single list of matches that only support the following match conditions:
\begin{itemize}
  \item (String) prefix matches on the input and output interfaces.
  \item A @{type prefix_match} on the source and destination IP address.
  \item An exact match on the layer 4 protocol.
  \item Interval matches on the source or destination port, e.g. @{term "p\<^sub>d \<in> {(1::16 word)..1023}"}
\end{itemize}
The model/type of the packet is adjusted to fit that: it is a record of the fields matched on.
This also means that input and output interface are coded to the packet.
Given that this information is usually stored alongside the packet content, this can be deemed a reasonable model.
In case the output interface is not needed (e.g., when evaluating an OpenFlow table), it can simply be left blank.

Obviously, a simplification into the above match type cannot always produce an equivalent firewall, and the set of accepted packets has to be over- or underapproximated.
The reader interested in the details of this is strongly referred to~\cite{diekmann2016verified}; we are simply going to continue with the result: @{const simple_fw}.
\<close>
text\<open>One property of the simplification is worth noting here: The simplified firewall does not know state and the simplification approximates stateful matches by stateless ones. 
Thus, the overapproximation of a stateful firewall ruleset that begins with accepting packets of established connections usually begins with a rule that accepts all packets.
Dealing with this by writing a meaningful simplification of stateful firewalls is future work.
\<close>

subsection\<open>OpenFlow Switch Model\<close>
text\<open>In this section, we present our model of an OpenFlow switch.
The requirements for this model are derived from the fact that it models devices that are the target of a configuration translation.
This has two implications:
\begin{itemize}
\item All configurations that are representable in our model should produce the correct behavior wrt. their semantics.
  The problem is that correct here means that the behavior is the same that any real device would produce.
  Since we cannot possibly account for all device types, we instead focus on those that conform to the OpenFlow specifications.
  To account for the multiple different versions of the specification (e.g.~\cite{specification10,specification15}), we tried making our model a subset of 
  both the oldest stable version 1.0~\cite{specification10} and the newest available specification version 1.5.1~\cite{specification15}.
\item Conversely, our model does not need to represent all possible behavior of an OpenFlow switch, just the behavior that can be invoked by the result of our translation.
  This is especially useful regarding for controller interaction, but also for MPLS or VLANs, which we did not model in Section \ref{sec:lfw}.
\end{itemize}\<close>

text\<open>More concretely, we set the following rough outline for our model.
\begin{itemize}
  \item A switch consists of a single flow table.
  \item A flow table entry consists of a priority, a match condition and an action list.
  \item The only possible action (we require) is to forward the packet on a port.
  \item We do not model controller interaction.
\end{itemize}
Additionally, we decided that we wanted to be able to ensure the validity of the flow table in all qualities,
i.e. we want to model the conditions `no overlapping flow entries appear', `all match conditions have their necessary preconditions'.
The details of this are explained in the following sections.
\<close>

subsubsection\<open>Matching Flow Table entries\<close>
text_raw\<open>\label{sec:of_match}\<close>
text\<open>Table 3 of Section 3.1 of \cite{specification10} gives a list of required packet fields that can be used to match packets.
This directly translates into the type for a match expression on a single field:\<close>

schematic_goal "(field_match :: of_match_field) \<in> {
  IngressPort (?s::string),
  EtherSrc (?as::48 word), EtherDst (?ad::48 word),
	EtherType (?t::16 word),
	VlanId (?i::16 word), VlanPriority (?p::16 word),
	IPv4Src (?pms::32 prefix_match), 
	IPv4Dst (?pmd::32 prefix_match),
	IPv4Proto (?ipp :: 8 word),
	L4Src (?ps :: 16 word) (?ms :: 16 word),
	L4Dst (?pd :: 16 word) (?md :: 16 word)
}" by(fact of_match_field_typeset)
text\<open>
Two things are worth additional mention: L3 and L4 ``addressess''.
The @{term IPv4Src} and @{term IPv4Dst} matches are specified as ``can be subnet masked'' in~\cite{specification10}, 
  whereras~\cite{specification15} states clearly that arbitrary bitmasks can be used. We took the conservative approach here.
Our alteration of @{term L4Src} and @{term L4Dst} is more grave. While~\cite{specification10} does not state anything about layer 4 ports and masks,
\cite{specification15} specifically forbids using masks on them. 
Nevertheless, OpenVSwitch \cite{openvswitch} and some other implementations support them.
We will explain in detail why we must include bitmasks on layer 4 ports to obtain a meaningful translation in Section~\ref{sec:convi}.\<close>

text\<open>One @{type of_match_field} is not enough to classify a packet. 
To match packets, we thus use entire sets of match fields.
As Guha \emph{et al.}~\cite{guha2013machine} noted\footnote{See also: \cite[\<section>2.3]{michaelis2016middlebox}}, executing a set of given @{type of_match_field}s on a packet requires careful consideration.
For example, it is not meaningful to use @{term IPv4Dst} if the given packet is not actually an IP packet, i.e.
@{term IPv4Dst} has the prerequisite of @{term "EtherType 0x0800"} being among the match fields.
Guha \emph{et al.} decided to use the fact that the preconditions can be arranged on a directed acyclic graph (or rather: an acyclic forest).
They evaluated match conditions in a manner following that graph:
first, all field matches without preconditions are evaluated.
Upon evaluating a field match (e.g., @{term "EtherType 0x0800"}), the matches that had their precondition fulfilled by it
  (e.g., @{term IPv4Src} and @{term IPv4Src} in this example) are evalutated.
This mirrors the faulty behavior of some implementations (see \cite{guha2013machine}).
Adopting that behavior into our model would mean that any packet matches against the field match set @{term "{IPv4Dst (PrefixMatch 134744072 32)}"} 
instead of just those destined for 8.8.8.8 or causing an error. We found this to be unsatisfactory.\<close>

text\<open>To solve this problem, we made three definitions.
The first, @{term match_no_prereq} matches an @{type of_match_field} against a packet without considering prerequisites.
The second, @{term prerequisites}, checks for a given @{type of_match_field} whether its prerequisites are in a set of given match fields.
Especially:
\<close>
lemma 
  "prerequisites (VlanPriority pri) m = (\<exists>id. let v = VlanId id in v \<in> m \<and> prerequisites v m)"
  "prerequisites (IPv4Proto pr) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)"
  "prerequisites (IPv4Src a) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)"
  "prerequisites (IPv4Dst a) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)"
  "prerequisites (L4Src p msk) m = (\<exists>proto \<in> {TCP,UDP,L4_Protocol.SCTP}. let v = IPv4Proto proto in v \<in> m \<and> prerequisites v m)"
  "prerequisites (L4Dst p msk) m = prerequisites (L4Src undefined undefined) m"
  by(fact prerequisites.simps)+
text\<open>Then, to actually match a set of @{type of_match_field} against a packet, we use the option type:\<close>
lemma "OF_match_fields m p =
  (if \<exists>f \<in> m. \<not>prerequisites f m then None else 
    if \<forall>f \<in> m. match_no_prereq f p then Some True else Some False)"
by(fact OF_match_fields_alt)

subsubsection\<open>Evaluating a Flow Table\<close>
text\<open>In the previous section, we explained how we match the set of match fields belonging to a single flow entry against a packet.
This section explains how the correct flow entry from a table can be selected.
To prevent to much entanglement with the previous section, we assume an arbitrary match function @{term "\<gamma> :: 'match_field set \<Rightarrow> 'packet \<Rightarrow> bool"}.
This function @{term "\<gamma>"} takes the match condition @{term m} from a flow entry @{term "OFEntry (priority::16 word) (m::'match_field set) action"}
and decides whether a packet matches those.\<close>

text\<open>The flow table is simply a list of flow table entries @{type flow_entry_match}.
Deciding the right flow entry to use for a given packet is explained in the OpenFlow specification \cite{specification10}, Section 3.4:
\begin{quote}
  Packets are matched against flow entries based on prioritization. 
  An entry that specifies an exact match (i.e., has no wildcards) is always the highest priority\footnote{This behavior has been deprecated.}.
  All wildcard entries have a priority associated with them. 
  Higher priority entries must match before lower priority ones.
  If multiple entries have the same priority, the switch is free to choose any ordering.
\end{quote}
We use the term ``overlapping'' for  the flow entries that can cause a packet to match multiple flow entries with the same priority.
Guha \emph{et al.}~\cite{guha2013machine} have dealt with overlapping.
However, the semantics for a flow table they presented \cite[Figure 5]{guha2013machine}
  is slightly different from what they actually used in their theory files.
We have tried to reproduce the original inductive definition (while keeping our abstraction @{term \<gamma>}),
 in Isabelle/HOL\footnote{The original is written in Coq~\cite{barras1997coq} and we can not use it directly.}:\<close>
lemma "\<gamma> (ofe_fields fe) p = True \<Longrightarrow>
 \<forall>fe' \<in> set (ft1 @ ft2). ofe_prio fe' > ofe_prio fe \<longrightarrow> \<gamma> (ofe_fields fe') p = False \<Longrightarrow> 
 guha_table_semantics \<gamma> (ft1 @ fe # ft2) p (Some (ofe_action fe))" 
 "\<forall>fe \<in> set ft. \<gamma> (ofe_fields fe) p = False \<Longrightarrow>
 guha_table_semantics \<gamma> ft p None" by(fact guha_matched guha_unmatched)+
text\<open>Guha \emph{et al.} have deliberately made their semantics non-deterministic, to match the fact that the switch ``may choose any ordering''.
This can lead to undesired results:\<close>
lemma "CARD('action) \<ge> 2 \<Longrightarrow> \<exists>ff. \<gamma> ff p \<Longrightarrow> \<exists>ft (a1 :: 'action) (a2 :: 'action). a1 \<noteq> a2 \<and> guha_table_semantics \<gamma> ft p (Some a1) \<and> guha_table_semantics \<gamma> ft p (Some a2)"
by(fact guha_table_semantics_ex2res)
text\<open>This means that, given at least two distinct actions exist and our matcher @{term \<gamma>} is not false for all possible match conditions, 
we can say that a flow table and two actions exist such that both actions are executed. This can be misleading, as the switch might choose an 
ordering on some flow table and never execute some of the (overlapped) actions.\<close>

text\<open>Instead, we decided to follow Section 5.3 of the specification \cite{specification15}, which states:
\begin{quote}
  If there are multiple matching flow entries, the selected flow entry is explicitly undefined.
\end{quote}
This still leaves some room for interpretation, but it clearly states that overlapping flow entries are undefined behavior, 
  and undefined behavior should not be invoked.
Thus, we came up with a semantics that clearly indicates when undefined behavior has been invoked:\<close>
lemma
  "OF_priority_match \<gamma> flow_entries packet = (
  let m  = filter (\<lambda>f. \<gamma> (ofe_fields f) packet) flow_entries;
  	  m' = filter (\<lambda>f. \<forall>fo \<in> set m. ofe_prio fo \<le> ofe_prio f) m in
  	case m' of []  \<Rightarrow> NoAction
             | [s] \<Rightarrow> Action (ofe_action s)
             |  _  \<Rightarrow> Undefined)"
unfolding OF_priority_match_def ..
text\<open>The definition works the following way\footnote{Note that the order of the flow table entries is irrelevant. 
We could have made this definition on sets but chose not to for consistency.}:
\begin{enumerate}
  \item The flow table is filtered for those entries that match, the result is called $m$.
  \item $m$ is filtered again, leaving only those entries for which no entries with lower priority could be found, i.e. the matching flow table entries with minimal priority. The result is called $m'$.
  \item A case distinction on $m'$ is made. If only one matching entry was found, its action is returned for execution. 
  If $m$ is empty, the flow table semantics returns @{term NoAction} to indicate that the flow table does not decide an action for the packet.
  If,  not zero or one entry is found, but more, the special value @{term Undefined} for indicating undefined behavior is returned.
\end{enumerate}
The use of @{term Undefined} immediately raises the question in which condition it cannot occur.
We give the following definition:\<close>
lemma "check_no_overlap \<gamma> ft = (\<forall>a \<in> set ft. \<forall>b \<in> set ft. (a \<noteq> b \<and> ofe_prio a = ofe_prio b) \<longrightarrow> \<not>(\<exists>p. \<gamma> (ofe_fields a) p \<and> \<gamma> (ofe_fields b) p))" unfolding check_no_overlap_alt check_no_overlap2_def by force
text\<open>Together with distinctness of the flow table, this provides the abscence of @{term Undefined}\footnote{It is slightly stronger than necessary, overlapping rules might be shadowed and thus never influence the behavior.}:\<close>
lemma "\<lbrakk>check_no_overlap \<gamma> ft; distinct ft\<rbrakk> \<Longrightarrow>
  OF_priority_match \<gamma> ft p \<noteq> Undefined" by (simp add: no_overlapsI no_overlaps_not_unefined)

text\<open>Given the absence of overlapping or duplicate flow entries, we can show two interesting equivalences.
the first is the equality to the semantics defined by Guha \emph{et al.}:\<close>
lemma "\<lbrakk>check_no_overlap \<gamma> ft; distinct ft\<rbrakk> \<Longrightarrow> 
OF_priority_match \<gamma> ft p = option_to_ftb d \<longleftrightarrow> guha_table_semantics \<gamma> ft p d"
by (simp add: guha_equal no_overlapsI)
text\<open>where @{term option_to_ftb} maps between the return type of @{term OF_priority_match} and an option type as one would expect.\<close>

text\<open>The second equality for @{term OF_priority_match} is one that helps reasoning about flow tables.
We define a simple recursive traversal for flow tables:\<close>
lemma
  "OF_match_linear \<gamma> [] p = NoAction"
  "OF_match_linear \<gamma> (a#as) p = (if \<gamma> (ofe_fields a) p then Action (ofe_action a) else OF_match_linear \<gamma> as p)"
by(fact OF_match_linear.simps)+
text\<open>For this definition to be equivalent, we need the flow table to be sorted:\<close>
lemma"
	\<lbrakk>no_overlaps \<gamma> f ;sorted_descending (map ofe_prio f)\<rbrakk> \<Longrightarrow>
	OF_match_linear \<gamma> f p = OF_priority_match \<gamma> f p"
by(fact  OF_eq)

text\<open>As the last step, we implemented a serialization function for flow entries; it has to remain unverified.
The serialization function deals with one little inaccuracy: We have modelled the @{term IngressPort} match to use the interface name, but OpenFlow requires numerical interface IDs instead.
We deemed that pulling this translation step into the main translation would only make the correctness lemma of the translation more complicated while not increasing the confidence in the correctness significantly.
We thus made replacing interface names by their ID part of the serialization.
\<close>

text\<open>Having collected all important definitions and models, we can move on to the conversion.\<close>
(*text\<open>\todo{Maybe I should make a sweet little subsection that merges this all into a single model definition.}\<close>*)

subsection\<open>Translation Implementation\<close>
text_raw\<open>\label{sec:convi}\<close>
text\<open>This section explains how the functions that are executed sequentially in a linux firewall can be compressed into a single OpenFlow table.
Creating this flow table in a single step would be immensely complicated.
We thus divided the task into several steps using the following key insights:
\begin{itemize}
  \item All steps that are executed in the linux router can be formulated as a firewall, more specifically, a generalization of @{term simple_fw} that allows arbitrary actions instead of just accept and drop.
  \item A function that computes the conjunction of two @{term simple_fw} matches is already present.
    Extending this to a function that computes the join of two firewalls is relatively simple. This is explained in Section \ref{sec:fwconj}
\end{itemize}
\<close>
subsubsection\<open>Chaining Firewalls\<close>
text_raw\<open>\label{sec:fwconj}\<close>
text\<open>This section explains how to compute the join of two firewalls.\<close>
text\<open>The basis of this is a generalization of @{const simple_fw}.
Instead of only allowing @{const simple_action.Accept} or @{const simple_action.Drop} as actions, it allows arbitrary actions. The type of the function that evaluates this generalized simple firewall is
@{term "generalized_sfw :: ('i::len simple_match \<times> 'a) list \<Rightarrow> ('i, 'b) simple_packet_scheme \<Rightarrow> ('i simple_match \<times> 'a) option"}.
The definition is straightforward:\<close>
lemma 
"generalized_sfw [] p = None" 
"generalized_sfw (a # as) p = (if (case a of (m,_) \<Rightarrow> simple_matches m p) then Some a else generalized_sfw as p)"
	by(fact generalized_sfw_simps)+
text\<open>Based on that, we asked: if @{term fw\<^sub>1} makes the decision @{term a} (where @{term a} is the second element of the result tuple from @{const generalized_sfw}) and @{term fw\<^sub>2} makes the decision @{term b}, how can we compute the firewall that
makes the decision @{term "(a,b)"}\footnote{Note that tuples are right-associative in Isabelle/HOL, i.e., @{term "(a::'a,(b,c)::('b\<times>'c))"} is a pair of @{term a} and the pair @{term "(b,c)"}}.
One possible answer is given by the following definition:
\<close>
lemma "generalized_fw_join l1 l2 \<equiv> [(u,a,b). (m1,a) \<leftarrow> l1, (m2,b) \<leftarrow> l2, u \<leftarrow> (case simple_match_and m1 m2 of None \<Rightarrow> [] | Some s \<Rightarrow> [s])]"
by(fact generalized_fw_join_def[unfolded option2list_def])+
text\<open>This definition validates the following lemma:\<close>
lemma "generalized_sfw (generalized_fw_join fw\<^sub>1 fw\<^sub>2) p = Some (u, d\<^sub>1,d\<^sub>2) \<longleftrightarrow> (\<exists>r\<^sub>1 r\<^sub>2. generalized_sfw fw\<^sub>1 p = Some (r\<^sub>1,d\<^sub>1) \<and> generalized_sfw fw\<^sub>2 p = Some (r\<^sub>2,d\<^sub>2) \<and> Some u = simple_match_and r\<^sub>1 r\<^sub>2)"
  by(force dest: generalized_fw_joinD generalized_fw_joinI intro: Some_to_the[symmetric])
text\<open>Thus, @{const generalized_fw_join} has a number of applications.
For example, it could be used to compute a firewall ruleset that represents two firewalls that are executed in sequence.
\<close>
definition "simple_action_conj a b \<equiv> (if a = simple_action.Accept \<and> b = simple_action.Accept then simple_action.Accept else simple_action.Drop)"
definition "simple_rule_conj \<equiv> (uncurry SimpleRule \<circ> apsnd (uncurry simple_action_conj))"
theorem "simple_fw rs\<^sub>1 p = Decision FinalAllow \<and> simple_fw rs\<^sub>2 p = Decision FinalAllow \<longleftrightarrow>
simple_fw (map simple_rule_conj (generalized_fw_join (map simple_rule_dtor rs\<^sub>1) (map simple_rule_dtor rs\<^sub>2))) p = Decision FinalAllow"
unfolding simple_rule_conj_def simple_action_conj_def[abs_def] using simple_fw_join by(force simp add: comp_def apsnd_def map_prod_def case_prod_unfold uncurry_def[abs_def])
text\<open>Using the join, it should be possible to compute any $n$-ary logical operation on firewalls.
We will use it for something somewhat different in the next section.\<close>

subsubsection\<open>Translation Implementation\<close>

text_raw\<open>
\begin{figure*}
\begin{framed}
\<close>
lemma "lr_of_tran rt fw ifs \<equiv> 
if \<not> (no_oif_match fw \<and> has_default_policy fw \<and> simple_fw_valid fw	\<and> valid_prefixes rt \<and> has_default_route rt \<and> distinct ifs)
  then Inl ''Error in creating OpenFlow table: prerequisites not satisifed''
  else (
let
  nfw = map simple_rule_dtor fw; 
  frt = map (\<lambda>r. (route2match r, output_iface (routing_action r))) rt; 
  nrd = generalized_fw_join frt nfw;
  ard = (map (apfst of_nat) \<circ> annotate_rlen) nrd
  in
  if length nrd < unat (max_word :: 16 word)
  then Inr (pack_OF_entries ifs ard)
  else Inl ''Error in creating OpenFlow table: priority number space exhausted''
)"
unfolding Let_def lr_of_tran_def lr_of_tran_fbs_def lr_of_tran_s1_def comp_def route2match_def by force

text_raw\<open>
  \end{framed}
  \caption{Function for translating a @{typ "'i::len simple_rule list"}, a @{typ "'i routing_rule list"}, and a list of interfaces to a flow table.}
  \label{fig:convi}
\end{figure*}
\<close>

text\<open>
This section shows the actual definition of the translation function, in Figure~\ref{fig:convi}.
Before beginning the translation, the definition checks whether the necessary preconditions are valid.
This first two steps are to convert @{term fw} and @{term rt} to lists that can be evaluated by @{const generalized_sfw}.
For @{term fw}, this is done by @{term "map simple_rule_dtor"}, which just deconstructs @{type simple_rule}s into tuples of match and action.
For @{term rt}, we made a firewall ruleset with rules that use prefix matches on the destination IP address.
The next step is to join the two rulesets.
 The result of the join is a ruleset with rules @{term r} that only match if both, the corresponding firewall rule @{term fwr} and the corresponding routing rule @{term rr} matches.
The data accompanying @{term r} is the port from @{term rr} and the firewall decision from @{term fwr}.
Next, descending priorities are added to the rules using @{term "map (apfst word_of_nat) \<circ> annotate_rlen"}.
If the number of rules is too large to fit into the $2^{16}$ priority classes, an error is returned.
Otherwise, the function @{const pack_OF_entries} is used to convert the @{typ "(16 word \<times> 32 simple_match \<times> char list \<times> simple_action) list"} to an OpenFlow table.
While converting the @{typ "char list \<times> simple_action"} tuple is straightforward, converting the @{type simple_match} to an equivalent list of @{typ "of_match_field set"} is non-trivial.
This is done by the function @{const simple_match_to_of_match}.
\<close>
text\<open>The main difficulties for @{const simple_match_to_of_match} lie in making sure that the prerequisites are satisfied
 and in the fact that a @{type simple_match} operates on slightly stronger match expressions.
\begin{itemize}
  \item A @{type simple_match} allows a (string) prefix match on the input and output interfaces.
    Given a list of existing interfaces on the router @{term ifs}, the function has to insert flow entries for each interface matching the prefix.
  \item A @{type simple_match} can match ports by an interval. Now it becomes obvious why Section~\ref{sec:of_match} added bitmasks to @{const L4Src} and @{const L4Dst}.
    Using the algorithm to split word intervals into intervals that can be represented by prefix matches from~\cite{diekmann2016verified},
      we can efficiently represent the original interval by a few (32 in the worst case) prefix matches and insert flow entries for each of them.%
      \footnote{It might be possible to represent the interval match more efficiently than a split into prefixes. However, that would produce overlapping matches (which is not a problem if we assing separate priorities) 
        and we did not have a verified implementation of an algorithm that does so.}
\end{itemize}
The following lemma characterizes @{const simple_match_to_of_match}:
\<close>
lemma simple_match_to_of_match:
assumes
  "simple_match_valid r" 
  "p_iiface p \<in> set ifs" 
  "match_iface (oiface r) (p_oiface p)"
  "p_l2type p = 0x800"
shows
  "simple_matches r p \<longleftrightarrow> (\<exists>gr \<in> set (simple_match_to_of_match r ifs). OF_match_fields gr p = Some True)"
using assms simple_match_to_of_matchD simple_match_to_of_matchI by blast

text\<open>The assumptions are to be read as follows:
\begin{itemize}
  \item The match @{term r} has to be valid, i.e. it has to use @{const valid_prefix} matches, and it cannot use anything other than $0$-$65535$ for the port matches unless its protocol match ensures @{const TCP}, @{const UDP} or @{const L4_Protocol.SCTP}.
  \item @{const simple_match_to_of_match} cannot produce rules for packets that have input interfaces that are not named in the interface list.
  \item The output interface of @{term p} has to match the output interface match of @{term r}. This is a weakened formulation of @{term "oiface r = ifaceAny"}, since @{thm[display] match_ifaceAny[no_vars]}.
    We require this because OpenFlow field matches cannot be used to match on the output port — they are supposed to match a packet and decide an output port.
  \item The @{type simple_match} type was designed for IP(v4) packets, we limit ourselves to them.
\end{itemize}
The conclusion then states that the @{type simple_match} @{term r} matches iff an element of the result of @{const simple_match_to_of_match} matches.
The third assumption is part of the explanation why we did not use @{const simple_linux_router_altered}:
@{const simple_match_to_of_match} cannot deal with output interface matches. 
Thus, before passing a generalized simple firewall to @{const pack_OF_entries}, we would have to set the output ports to @{const ifaceAny}.
A system replace output interface matches with destination IP addresses has already been formalized and will be published in a future version of \cite{Iptables_Semantics-AFP}.
For now, we limit ourselves to firewalls that do not do output port matching, i.e., we require @{term "no_oif_match fw"}.
\<close>

text_raw\<open>\begin{figure*}
\begin{framed}
\<close>
theorem
fixes
  p :: "(32, 'a) simple_packet_ext_scheme"
assumes
  "p_iiface p \<in> set ifs" and "p_l2type p = 0x800"
  "lr_of_tran rt fw ifs = Inr oft"
shows
  "OF_priority_match OF_match_fields_safe oft p = Action [Forward oif] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = (Some (p\<lparr>p_oiface := oif\<rparr>))"
  "OF_priority_match OF_match_fields_safe oft p = Action [] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = None"
  "OF_priority_match OF_match_fields_safe oft p \<noteq> NoAction" "OF_priority_match OF_match_fields_safe oft p \<noteq> Undefined"
  "OF_priority_match OF_match_fields_safe oft p = Action ls \<longrightarrow> length ls \<le> 1"
  "\<exists>ls. length ls \<le> 1 \<and> OF_priority_match OF_match_fields_safe oft p = Action ls"
using assms lr_of_tran_correct by simp_all
text_raw\<open>
\end{framed}
\caption{Central theorem on @{const lr_of_tran}}
\label{fig:central}
\end{figure*}
\<close>

text\<open>
Given discussed properties, we present the central theorem for our translation in Figure~\ref{fig:central}.
The first two assumptions are limitations on the traffic we make a statement about.
Obviously, we will never see any packets with an input interface that is not in the interface list.
Furthermore, we do not state anything about non-IPv4 traffic. (The traffic will remain unmatched in by the flow table, but we have not verified that.)
The last assumption is that the translation does not return a run-time error.
The translation will return a run-time error if the rules can not be assigned priorities from a 16 bit integer, 
or when one of the following conditions on the input data is not satisifed:\<close>
lemma "
  \<not> no_oif_match fw \<or> 
  \<not> has_default_policy fw \<or>
  \<not> simple_fw_valid fw	\<or>
  \<not> valid_prefixes rt \<or>
  \<not> has_default_route rt \<or>
  \<not> distinct ifs \<Longrightarrow> 
\<exists>err. lr_of_tran rt fw ifs = Inl err" unfolding lr_of_tran_def by(simp split: if_splits)

subsubsection\<open>Comparison to Exodus\<close>
text\<open>
  We are not the first researchers to attempt automated static migration to SDN.
  The (only) other attempt we are aware of is \emph{Exodus} by Nelson \emph{et al.}~\cite{nelson2015exodus}.
\<close>
text\<open>
There are some fundamental differences between Exodus and our work:
\begin{itemize}
  \item Exodus focuses on Cisco IOS instead of linux.
  \item Exodus does not produce OpenFlow rulesets, but FlowLog~\cite{nelson2014tierless} controller programs.
  \item Exodus is not limited to using a single flow table.
  \item Exodus requires continuous controller interaction for some of its functions.
  \item Exodus attempts to support as much functionality as possible and has implemented support for dynamic routing, VLANs and NAT.
  \item Nelson \emph{et al.} reject the idea that the translation could or should be proven correct.
\end{itemize}
\<close>

(*<*)
end
(*>*)
