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

definition iface_packet_check ::  "interface list \<Rightarrow> 'b simple_packet_ext_scheme \<Rightarrow> interface option"
where "iface_packet_check ifs p \<equiv> find (\<lambda>i. iface_name i = p_iiface p \<and> iface_mac i = p_l2dst p) ifs" 
term simple_fw
definition simple_linux_router :: "routing_rule list \<Rightarrow> simple_rule list \<Rightarrow> (32 word \<Rightarrow> 48 word option) \<Rightarrow> interface list \<Rightarrow> simple_packet_ext \<Rightarrow> simple_packet_ext option" where
"simple_linux_router rt fw mlf ifl p \<equiv> do {
	_ \<leftarrow> iface_packet_check ifl p;
	let rd = routing_table_semantics rt (p_dst p);
	let p = p_oiface_update (const (output_iface rd)) p;
	let fd = simple_fw fw p;
	let nh = fromMaybe (p_dst p) (next_hop rd);
	ma \<leftarrow> mlf nh;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some (p_l2dst_update (const ma) p)
}"
(* Can I find something that looks a bit more semantic. Maybe the option monad can reduce a bit of the foo? *)
(* TODO: What happens in linux, if I send a packet to an interface with the mac of another interface? Hopefully, that is going to be dropped? *) 

(* Limitations:
 - Unicast only. 
 - Only one routing table.
 - Only default iptables table (no raw, nat)
 - No traffic to localhost (might be a limit to lift\<dots>)
*)

text{* Transformed linux router: does not do layer 2 modifications and throws away packets that would leave on the same interface that they came in on. 
 The entire idea is that @{term iface_packet_check} will only fail if the packet is bound for someone else on that subnet, so the routing decision would, if applied, just output the packet where it came from.*}
definition simple_linux_router_nomac :: "routing_rule list \<Rightarrow> simple_rule list \<Rightarrow> 'a simple_packet_scheme \<Rightarrow> 'a simple_packet_scheme option" where
"simple_linux_router_nomac rt fw p \<equiv> do {
	let rd = routing_table_semantics rt (p_dst p);
	_ \<leftarrow> (if output_iface rd = p_oiface p then None else Some ());
	let p = p_oiface_update (const (output_iface rd)) p;
	let fd = simple_fw fw p;
	_ \<leftarrow> (case fd of Decision FinalAllow \<Rightarrow> Some () | Decision FinalDeny \<Rightarrow> None);
	Some p
}"
(* an alternative formulation would maybe be "if the routing decision for the source is the same as for the destination, don't forward it." 
   This might be advantageous in $cases, however, this formulation is clearly easier to translate *)

lemma rtr_nomac_e1:
	assumes "simple_linux_router rt fw mlf ifl pi = Some po"
	assumes "simple_linux_router_nomac rt fw pi = Some po'"
	shows "\<exists>x. po = p_l2dst_update x po'"
using assms
unfolding simple_linux_router_nomac_def simple_linux_router_def
by(simp add: Let_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits) blast+

lemma rtr_nomac_e2:
	assumes "simple_linux_router rt fw mlf ifl pi = Some po"
	assumes "p_oiface pi \<noteq> p_oiface po"
	shows "\<exists>po'. simple_linux_router_nomac rt fw pi = Some po'"
using assms
unfolding simple_linux_router_nomac_def simple_linux_router_def
by(clarsimp simp add: Let_def const_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits)

lemma rtr_nomac_e3:
	assumes "simple_linux_router_nomac rt fw pi = Some po"
	assumes "iface_packet_check ifl pi = Some i(*don'tcare*)"
	assumes "mlf (fromMaybe (p_dst pi) (next_hop (routing_table_semantics rt (p_dst pi)))) = Some i2"
	shows "\<exists>po'. simple_linux_router rt fw mlf ifl pi = Some po'"
using assms
unfolding simple_linux_router_nomac_def simple_linux_router_def
by(clarsimp simp add: Let_def const_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits)

lemma rtr_nomac_eq:
	assumes "iface_packet_check ifl pi = None \<longleftrightarrow> output_iface (routing_table_semantics rt (p_dst pi)) = p_oiface pi"
	assumes "mlf (fromMaybe (p_dst pi) (next_hop (routing_table_semantics rt (p_dst pi)))) = Some i2"
	shows "\<exists>x. map_option (p_l2dst_update x) (simple_linux_router_nomac rt fw pi) = simple_linux_router rt fw mlf ifl pi"
proof(cases "simple_linux_router_nomac rt fw pi"; cases "simple_linux_router rt fw mlf ifl pi")
	case goal4
	note rtr_nomac_e1[OF goal4(2) goal4(1)]
	with goal4 show ?case by auto 
next
	case (goal2 a)
	from goal2(2) have "iface_packet_check ifl pi \<noteq> None" by(simp add: simple_linux_router_def Let_def const_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits) 
	hence "p_oiface pi \<noteq> p_oiface a" using assms(1) goal2(2) by(clarsimp simp add: simple_linux_router_def Let_def const_def split: option.splits state.splits final_decision.splits Option.bind_splits if_splits)
	note rtr_nomac_e2[OF goal2(2) this]
	with goal2(1) have False by simp
	thus ?case ..
next
	case (goal3 a)
	from goal3(1) have "p_oiface pi \<noteq> p_oiface a" 
		by(clarsimp simp add: simple_linux_router_nomac_def Let_def const_def split:  state.splits final_decision.splits if_splits Option.bind_splits) (* woha, the order of the splits is important\<dots> *) 
	hence "iface_packet_check ifl pi \<noteq> None" using goal3(1) by(clarsimp simp add: simple_linux_router_nomac_def Let_def const_def assms split:  state.splits final_decision.splits if_splits Option.bind_splits)
	then obtain i3 where "iface_packet_check ifl pi = Some i3" by blast
	note rtr_nomac_e3[OF goal3(1) this] assms(2)
	with goal3(2) have False by force
	thus ?case ..
qed simp

(* another limitation for the nol2-router: It can never ever properly support bridges. *)

lemma rtr_nomac_eq_halfinv:
	assumes fw_ac_all: "fw = [SimpleRule simple_match_any Accept]"
	assumes a1: "\<exists>x. map_option (p_l2dst_update x) (simple_linux_router_nomac rt fw pi) = simple_linux_router rt fw mlf ifl pi"
	assumes a2: "mlf (fromMaybe (p_dst pi) (next_hop (routing_table_semantics rt (p_dst pi)))) = Some i2"
	shows "iface_packet_check ifl pi = None \<longleftrightarrow> output_iface (routing_table_semantics rt (p_dst pi)) = p_oiface pi"
using a1 a2
	apply(clarify)
	apply(cases "simple_linux_router rt fw mlf ifl pi")
	apply(unfold fw_ac_all)
	apply(simp_all add: simple_linux_router_nomac_def simple_linux_router_def Let_def simple_match_any split: Option.bind_splits if_splits)
done

end