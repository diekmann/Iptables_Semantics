theory LinuxRouter
imports Routing "../Simple_Firewall/SimpleFw_Semantics"
begin

term "map port_sel $ routing_table_semantics rt (p_dst p)"
definition "simple_linux_router rt fw p \<equiv> let
	rd = routing_table_semantics rt (p_dst p) in
	concat (map (\<lambda>pt. case (simple_fw fw (p_oiface_update (const (port_sel pt)) p)) of 
		Decision FinalAllow \<Rightarrow> [pt] |
		Decision FinalDeny \<Rightarrow> []
	) rd)"
(* Todo: Find something that looks a bit more semantic *)

end