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

term "routing_table_semantics rt (p_dst p)"
definition "simple_linux_router rt fw mlf p \<equiv> (let
	rd = routing_table_semantics rt (p_dst p);
	p = p_oiface_update (const (output_iface rd)) p;
	fd = simple_fw fw p;
	nh = fromMaybe (p_dst p) (next_hop rd);
	ma = mlf nh;
	p = p_oiface_update (const (output_iface rd)) p
	in case fd of
		Decision FinalAllow \<Rightarrow> Some p |
		Decision FinalDeny \<Rightarrow> None
	)"
(* Can I find something that looks a bit more semantic. *)
term p_l2dst_update

(* Limitations:
 - Unicast only. 
 - Only one routing table.
 - Only default iptables table (no raw, nat)
 - No traffic to localhost (might be a limit to lift\<dots>)
*)

end