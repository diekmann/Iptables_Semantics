theory LinuxRouter
imports 
	(* For obvious reasons *)
	Routing
	"../Simple_Firewall/SimpleFw_Semantics"
	(* for the simple packet extension *)
	"../OpenFlow/OpenFlowMatches"
	"~~/src/HOL/Library/Monad_Syntax"
begin
definition "fromMaybe a m = (case m of Some a \<Rightarrow> a | None \<Rightarrow> a)" (* mehr Haskell wagen *)

(* 
Oversimplified linux router:
 - Packet arrives (destination port is empty, destination mac address is own address).
 - Destination address is extracted and used for a routing table lookup.
 - Packet is updated with output interface of routing decision.
 - The FORWARD table of iptables is considered.
 - Next hop is extracted from the routing decision, fallback to destination address if directly attached.
 - MAC address of next hop is looked up (using the mac lookup function mlf)
 - Destination address of packet is updated.
 (net.ipv4.ip_forward enabled)
 TODO: Source mac.
*)

record interface =
	iface_name :: string
	iface_mac :: "48 word"
	(*iface_ips :: "(ipv4addr \<times> 32 prefix_match) set" (* there is a set of IP addresses and the reachable subnets for them *), but we don't use that right now, so it is commented out. 
	Also, part of that information is already in the routing table, so careful here\<dots> *)

definition iface_packet_check ::  "interface list \<Rightarrow>('i::len,'b) simple_packet_ext_scheme \<Rightarrow> interface option"
where "iface_packet_check ifs p \<equiv> find (\<lambda>i. iface_name i = p_iiface p \<and> iface_mac i = p_l2dst p) ifs" 
term simple_fw
definition simple_linux_router ::
  "routing_rule list \<Rightarrow> 32 simple_rule list \<Rightarrow> (32 word \<Rightarrow> 48 word option) \<Rightarrow> 
      interface list \<Rightarrow> 32 simple_packet_ext \<Rightarrow> 32 simple_packet_ext option" where
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

(* Limitations:
 - Unicast only. 
 - Only one routing table.
 - Only default iptables table (no raw, nat)
 - No traffic to localhost (might be a limit to lift\<dots>)
*)

definition simple_linux_router_nol12 ::
    "routing_rule list \<Rightarrow> 32 simple_rule list \<Rightarrow> (32,'a) simple_packet_scheme \<Rightarrow> (32,'a) simple_packet_scheme option" where
"simple_linux_router_nol12 rt fw p \<equiv> do {
	let rd = routing_table_semantics rt (p_dst p);
	let p = p\<lparr>p_oiface := output_iface rd\<rparr>;
	let fd = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some p
}"
(* an alternative formulation would maybe be "if the routing decision for the source is the same as for the destination, don't forward it." 
   This might be advantageous in $cases, however, this formulation is clearly easier to translate *)

lemma update_unfold_hlps:
	"p\<lparr>p_l2dst := x\<rparr> = p_l2dst_update (const x) p"
	"p\<lparr>p_oiface := y\<rparr> = p_oiface_update (const y) p"
by(simp_all add: const_def)

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
unfolding update_unfold_hlps
proof(cases "simple_linux_router_nol12 rt fw pi"; cases "simple_linux_router rt fw mlf ifl pi")
	case goal4
	note rtr_nomac_e1[OF goal4(2) goal4(1)]
	with goal4 show ?case by(auto simp add: update_unfold_hlps) 
next
	case (goal2 a)
	note rtr_nomac_e2[OF goal2(2)]
	with goal2(1) have False by simp
	thus ?case ..
next
	case (goal3 a)
	from \<open>iface_packet_check ifl pi \<noteq> None\<close> obtain i3 where "iface_packet_check ifl pi = Some i3" by blast
	note rtr_nomac_e3[OF goal3(1) this] assms(2)
	with goal3(2) have False by force
	thus ?case ..
qed simp

end