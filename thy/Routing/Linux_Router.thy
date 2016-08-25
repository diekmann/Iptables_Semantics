section "Linux Router"
theory Linux_Router
imports 
	Routing_Table
	"../Simple_Firewall/SimpleFw_Semantics"
	"../Simple_Firewall/Simple_Packet"
	"~~/src/HOL/Library/Monad_Syntax"
begin

definition "fromMaybe a m = (case m of Some a \<Rightarrow> a | None \<Rightarrow> a)" (* mehr Haskell wagen *)

text\<open>Here, we present a heavily simplified model of a linux router. 
(i.e., a linux-based device with \texttt{net.ipv4.ip\_forward})
It covers the following steps in packet processing:
\begin{itemize}
 \item Packet arrives (destination port is empty, destination mac address is own address).
 \item Destination address is extracted and used for a routing table lookup.
 \item Packet is updated with output interface of routing decision.
 \item The FORWARD chain of iptables is considered.
 \item Next hop is extracted from the routing decision, fallback to destination address if directly attached.
 \item MAC address of next hop is looked up (using the mac lookup function mlf)
 \item L2 destination address of packet is updated.
\end{itemize}
This is stripped down to model only the most important and widely used aspects of packet processing.
Here are a few examples of what was abstracted away:
\begin{itemize}
 \item No local traffic.
 \item Only the \texttt{filter} table of iptables is considered, \texttt{raw} and \texttt{nat} are not.
 \item Only one routing table is considered. (Linux can have other tables than the \texttt{default} one.)
 \item No source MAC modification.
 \item \ldots
\end{itemize}
\<close>

record interface =
	iface_name :: string
	iface_mac :: "48 word"
	(*iface_ips :: "(ipv4addr \<times> 32 prefix_match) set" (* there is a set of IP addresses and the reachable subnets for them *), but we don't use that right now, so it is commented out. 
	Also, part of that information is already in the routing table, so careful here... *)

definition iface_packet_check ::  "interface list \<Rightarrow>('i::len,'b) simple_packet_ext_scheme \<Rightarrow> interface option"
where "iface_packet_check ifs p \<equiv> find (\<lambda>i. iface_name i = p_iiface p \<and> iface_mac i = p_l2dst p) ifs" 
term simple_fw
definition simple_linux_router ::
  "'i routing_rule list \<Rightarrow> 'i simple_rule list \<Rightarrow> (('i::len) word \<Rightarrow> 48 word option) \<Rightarrow> 
         interface list \<Rightarrow> 'i simple_packet_ext \<Rightarrow> 'i simple_packet_ext option" where
"simple_linux_router rt fw mlf ifl p \<equiv> do {
	_ \<leftarrow> iface_packet_check ifl p;
	let rd (* routing decision *) = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
	let fd (* firewall decision *) = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	let nh = fromMaybe (p_dst p) (next_hop rd);
	ma \<leftarrow> mlf nh;
	Some (p\<lparr>p_l2dst := ma\<rparr>)
}"
(* Can I find something that looks a bit more semantic. Maybe the option monad can reduce a bit of the foo? *)
(* TODO: What happens in linux, if I send a packet to an interface with the mac of another interface? Hopefully, that is going to be dropped? *) 

text\<open>However, the above model is still too powerful for some use-cases.
Especially, the next hop look-up cannot be done without either a pre-distributed table of all MAC addresses,
or the usual mechanic of sending out an ARP request and caching the answer.
Doing ARP requests in the restricted environment of, e.g., an OpenFlow ruleset seems impossible.
Therefore, we present this model:\<close>
definition simple_linux_router_nol12 ::
    "'i routing_rule list \<Rightarrow> 'i simple_rule list \<Rightarrow> ('i,'a) simple_packet_scheme \<Rightarrow> ('i::len,'a) simple_packet_scheme option" where
"simple_linux_router_nol12 rt fw p \<equiv> do {
	let rd = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
	let fd = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some p
}"
text\<open>The differences to @{const simple_linux_router} are illustrated by the lemmata below.\<close>
(* an alternative formulation would maybe be "if the routing decision for the source is the same as for the destination, don't forward it." 
   This might be advantageous in $cases, however, this formulation is clearly easier to translate to openflow. *)

lemma rtr_nomac_e1:
	assumes "simple_linux_router rt fw mlf ifl pi = Some po"
	assumes "simple_linux_router_nol12 rt fw pi = Some po'"
	shows "\<exists>x. po = po'\<lparr>p_l2dst := x\<rparr>"
using assms
unfolding simple_linux_router_nol12_def simple_linux_router_def
by(simp add: Let_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits) blast+

lemma rtr_nomac_e2:
	assumes "simple_linux_router rt fw mlf ifl pi = Some po"
	shows "\<exists>po'. simple_linux_router_nol12 rt fw pi = Some po'"
using assms
unfolding simple_linux_router_nol12_def simple_linux_router_def
by(clarsimp simp add: Let_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits)

lemma rtr_nomac_e3:
	assumes "simple_linux_router_nol12 rt fw pi = Some po"
	assumes "iface_packet_check ifl pi = Some i(*don'tcare*)"
	assumes "mlf (fromMaybe (p_dst pi) (next_hop (routing_table_semantics rt (p_dst pi)))) = Some i2"
	shows "\<exists>po'. simple_linux_router rt fw mlf ifl pi = Some po'"
using assms
unfolding simple_linux_router_nol12_def simple_linux_router_def
by(clarsimp simp add: Let_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits)

lemma rtr_nomac_eq:
	assumes "iface_packet_check ifl pi \<noteq> None"
	assumes "mlf (fromMaybe (p_dst pi) (next_hop (routing_table_semantics rt (p_dst pi)))) \<noteq> None"
	shows "\<exists>x. map_option (\<lambda>p. p\<lparr>p_l2dst := x\<rparr>) (simple_linux_router_nol12 rt fw pi) = simple_linux_router rt fw mlf ifl pi"
proof(cases "simple_linux_router_nol12 rt fw pi"; cases "simple_linux_router rt fw mlf ifl pi")
	fix a b
	assume as: "simple_linux_router rt fw mlf ifl pi = Some b" "simple_linux_router_nol12 rt fw pi = Some a"
	note rtr_nomac_e1[OF this]
	with as show ?thesis by auto 
next
	fix a assume as: "simple_linux_router_nol12 rt fw pi = None" "simple_linux_router rt fw mlf ifl pi = Some a"
	note rtr_nomac_e2[OF as(2)]
	with as(1) have False by simp
	thus ?thesis ..
next
	fix a assume as: "simple_linux_router_nol12 rt fw pi = Some a" "simple_linux_router rt fw mlf ifl pi = None"
	from \<open>iface_packet_check ifl pi \<noteq> None\<close> obtain i3 where "iface_packet_check ifl pi = Some i3" by blast
	note rtr_nomac_e3[OF as(1) this] assms(2)
	with as(2) have False by force
	thus ?thesis ..
qed simp

end
