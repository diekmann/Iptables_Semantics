theory LinuxRouter
imports AnnotateRouting "../Simple_Firewall/SimpleFw_Semantics"
begin

datatype forwarding_decision = ForwardOn string | Drop

definition "simple_linux_router rt fw p \<equiv> let
	rd = routing_table_semantics rt (p_dst p);
	pt = port_sel (hd rd);
	fd = simple_fw fw (p_oiface_update (const pt) p) in
	case fd of 
		Decision FinalAllow \<Rightarrow> ForwardOn pt|
		Decision FinalDeny \<Rightarrow> Drop"


end