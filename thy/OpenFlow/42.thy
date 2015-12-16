theory 42
imports "../Simple_Firewall/SimpleFw_Compliance" "Semantics_OpenFlow" "../Routing/AnnotateRouting"
begin

fun filter_nones where
"filter_nones [] = []" |
"filter_nones (s#ss) = (case s of None \<Rightarrow> [] | Some s \<Rightarrow> [s]) @ filter_nones ss"

(* For reference:
iiface :: "iface" --"in-interface"
oiface :: "iface" --"out-interface"
src :: "(ipv4addr \<times> nat) " --"source IP address"
dst :: "(ipv4addr \<times> nat) " --"destination"
proto :: "protocol"
sports :: "(16 word \<times> 16 word)" --"source-port first:last"
dports :: "(16 word \<times> 16 word)" --"destination-port first:last"
*)
fun route2match :: "routing_rule \<Rightarrow> simple_match list \<Rightarrow> simple_match list" where
"route2match _ [] = []" |
"route2match r (m#ms) = filter_nones ((map (\<lambda>oi.
	let cr = \<lparr>iiface = Iface ''+'', oiface = Iface (port_sel oi), src = (0,0), dst=(pfxm_prefix (routing_match r),pfxm_length (routing_match r)), proto=ProtoAny, sports=(0,max_word), ports=(0,max_word)\<rparr>;
	     s = route2match r ms in
	simple_match_and cr m
	) (routing_action r)))"


end