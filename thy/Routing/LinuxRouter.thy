theory LinuxRouter
imports 
	(* For obvious reasons *)
	Routing
	"../Simple_Firewall/SimpleFw_Semantics"
	(* for the simple packet extension *)
	"../OpenFlow/OpenFlowMatches"
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
	(*iface_ips :: "(ipv4addr \<times> 32 prefix_match) set" (* there is a set of IP addresses and the reachable subnets for them *), but we don't use that right now, so it is commented out *)

definition iface_packet_check ::  "interface list \<Rightarrow> 'b simple_packet_ext_scheme \<Rightarrow> interface option"
where "iface_packet_check ifs p \<equiv> find (\<lambda>i. iface_name i = p_iiface p \<and> iface_mac i = p_l2dst p) ifs" 
term simple_fw
definition simple_linux_router :: "routing_rule list \<Rightarrow> simple_rule list \<Rightarrow> (32 word \<Rightarrow> 48 word) \<Rightarrow> interface list \<Rightarrow> simple_packet_ext \<Rightarrow> simple_packet_ext option" where
"simple_linux_router rt fw mlf ifl p \<equiv> (
case iface_packet_check ifl p of
   	None \<Rightarrow> None |
   	Some i \<Rightarrow>
   		(let
		rd = routing_table_semantics rt (p_dst p);
		p = p_oiface_update (const (output_iface rd)) p;
		fd = simple_fw fw p;
		nh = fromMaybe (p_dst p) (next_hop rd);
		ma = mlf nh
		in case fd of
			Decision FinalAllow \<Rightarrow> Some (p_oiface_update (const (output_iface rd)) p) |
			Decision FinalDeny \<Rightarrow> None
	)
)"
(* Can I find something that looks a bit more semantic. Maybe the option monad can reduce a bit of the foo? *)
(* TODO: What happens in linux, if I send a packet to an interface with the mac of another interface? Hopefully, that is going to be dropped? *) 

(* Limitations:
 - Unicast only. 
 - Only one routing table.
 - Only default iptables table (no raw, nat)
 - No traffic to localhost (might be a limit to lift\<dots>)
*)

end