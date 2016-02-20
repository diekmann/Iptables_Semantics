theory LinuxRouter
imports 
	(* For obvious reasons *)
	Routing
	"../Simple_Firewall/SimpleFw_Semantics"
	(* for the simple packet extension *)
	"../OpenFlow/OpenFlowMatches"
begin
definition "fromMaybe a m = (case m of Some a \<Rightarrow> a | None \<Rightarrow> a)" (* mehr Haskell wagen *)
term "routing_table_semantics rt (p_dst p)"
definition "simple_linux_router rt fw p \<equiv> let
	rd = routing_table_semantics rt (p_dst p) in
	concat (map (\<lambda>pt. case (simple_fw fw (p_oiface_update (const (port_sel pt)) p)) of 
		Decision FinalAllow \<Rightarrow> [pt] |
		Decision FinalDeny \<Rightarrow> []
	) rd)"
(* Todo: Find something that looks a bit more semantic. And update source and destination macs *)
term p_l2dst_update

end