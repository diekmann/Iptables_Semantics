theory OpenFlowMatches
imports Main "../Bitmagic/NumberWangCaesar" "../Primitive_Matchers/Simple_Packet" "~~/src/HOL/Library/Monad_Syntax"
	"../Primitive_Matchers/Simple_Packet" (* I just want those TCP,UDP,\<dots> defs *)
begin                                                                   

(* From OpenFlow 1.1, Table 3: *)
datatype of_match_field = 
	  IngressPort string
	| EtherSrc "48 word"
	| EtherDst "48 word"
	| EtherType "16 word"
	| VlanId "16 word"
	| VlanPriority "16 word"
(*	| MplsLabel
	| MplsClass *)
	| IPv4Src prefix_match (* could also be arbitrary bitmask - see page 80 of 1.5.1 *)
	| IPv4Dst prefix_match (* ditto *)
	| IPv4Proto "8 word"
(*	| IPv4ToS "16 word" *)
	| L4Src "16 word" (* openvswitch 1.6 supports bitmasks - does not seem to be in of 1.5.1 *)
	| L4Dst "16 word"

(*

The semantics of an openflow match is by no means trivial. See Specification 7.2.3.6, v1.5.1
For example:
• An OXM TLV for oxm_type=OXM OF IPV4 SRC is allowed only if it is preceded by another en-
try with oxm_type=OXM_OF_ETH_TYPE, oxm_hasmask=0, and oxm_value=0x0800. That is, match-
ing on the IPv4 source address is allowed only if the Ethernet type is explicitly set to IPv4.
\<dots>
Even if OpenFlow 1.0 does not require this behavior, some switches may still silently drop matches without prerequsites.

*)

(* subtable of table in 7.2.3.8 of spec1.5 (also present in 1.3, and less cluttered) for the matches we implement *) 
function prerequisites :: "of_match_field \<Rightarrow> of_match_field set \<Rightarrow> bool" where
"prerequisites (IngressPort _) _ = True" |
(* OF_ETH_DST None *)
"prerequisites (EtherDst _) _ = True" |
(* OF_ETH_SRC None *)
"prerequisites (EtherSrc _) _ = True" |
(* OF_ETH_TYPE None *)
"prerequisites (EtherType _) _ = True" |
(* OF_VLAN_VID None *)
"prerequisites (VlanId _) _ = True" |
(* OF_VLAN_PCP VLAN_VID!=NONE *)
"prerequisites (VlanPriority _) m = (\<exists>id. let v = VlanId id in v \<in> m \<and> prerequisites v m)" |
(* OF_IPV4_PROTO ETH_TYPE=0x0800 or ETH_TYPE=0x86dd *)
"prerequisites (IPv4Proto _) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)" (* IPv6 nah *) |
(* OF_IPV4_SRC ETH_TYPE=0x0800 *)
"prerequisites (IPv4Src _) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)" |
(* OF_IPV4_DST ETH_TYPE=0x0800 *)
"prerequisites (IPv4Dst _) m = (let v = EtherType 0x0800 in v \<in> m \<and> prerequisites v m)" |
(* Now here goes a bit of fuzz: OF specifies differen OXM_OF_(TCP,UDP,SCTP,\<dots>)_(SRC,DST). I only have L4Src. So gotta make do with that. *)
"prerequisites (L4Src _) m = (\<exists>proto \<in> {TCP,UDP,SCTP}. let v = IPv4Proto proto in v \<in> m \<and> prerequisites v m)" |
"prerequisites (L4Dst dm) m = prerequisites (L4Src dm) m"
by pat_completeness auto
(* Ignoredd PACKET_TYPE=foo *)

fun match_layer_terminator :: "of_match_field \<Rightarrow> nat" where
"match_layer_terminator (IngressPort _) = 1" |
"match_layer_terminator (EtherDst _) = 2" |
"match_layer_terminator (EtherSrc _) = 2" |
"match_layer_terminator (EtherType _) = 2" |
"match_layer_terminator (VlanId _) = 1" |
"match_layer_terminator (VlanPriority _) = 2" |
"match_layer_terminator (IPv4Proto _) = 3" |
"match_layer_terminator (IPv4Src _) = 3" |
"match_layer_terminator (IPv4Dst _) = 3" |
"match_layer_terminator (L4Src _) = 4" |
"match_layer_terminator (L4Dst _) = 5"

termination prerequisites by(relation "measure (match_layer_terminator \<circ> fst)", simp_all)

record simple_packet_ext = simple_packet +
	p_l2type :: "16 word"
	p_l2src :: "48 word"
	p_l2dst :: "48 word"
	p_vlanid :: "16 word"
	p_vlanprio :: "16 word"
	p_l3proto :: "8 word"

definition "simple_packet_unext p = 
\<lparr>p_iiface = p_iiface p, p_oiface = p_oiface p, p_src = p_src p, p_dst = p_dst p, p_proto = p_proto p, 
p_sport = p_sport p, p_dport = p_dport p, p_tcp_flags = p_tcp_flags p, p_tag_ctstate = p_tag_ctstate p\<rparr>"


fun match_no_prereq :: "of_match_field \<Rightarrow> simple_packet_ext \<Rightarrow> bool" where
"match_no_prereq (IngressPort i) p = (p_iiface p = i)" |
"match_no_prereq (EtherDst i) p = (p_l2src p = i)" |
"match_no_prereq (EtherSrc i) p = (p_l2dst p = i)" |
"match_no_prereq (EtherType i) p = (p_l2type p = i)" |
"match_no_prereq (VlanId i) p = (p_vlanid p = i)" | (* hack, otherwise it would be iso/osi *)
"match_no_prereq (VlanPriority i) p = (p_vlanprio p = i)" |
"match_no_prereq (IPv4Proto i) p = (p_l3proto p = i)" |
"match_no_prereq (IPv4Src i) p = (prefix_match_semantics i (p_src p))" |
"match_no_prereq (IPv4Dst i) p = (prefix_match_semantics i (p_dst p))" |
"match_no_prereq (L4Src i) p = (p_sport p = i)" |
"match_no_prereq (L4Dst i) p = (p_dport p = i)"

definition match_prereq :: "of_match_field \<Rightarrow> of_match_field set \<Rightarrow> simple_packet_ext \<Rightarrow> bool option" where
"match_prereq i s p = (if prerequisites i s then Some (match_no_prereq i p) else None)"

definition "set_seq s \<equiv> if (\<forall>x \<in> s. x \<noteq> None) then Some (the ` s) else None"
definition "all_true s \<equiv> \<forall>x \<in> s. x"
term map_option
definition OF_match_fields :: "of_match_field set \<Rightarrow> simple_packet_ext \<Rightarrow> bool option" where "OF_match_fields m p = map_option all_true (set_seq ((\<lambda>f. match_prereq f m p) ` m))"
definition OF_match_fields_unsafe :: "of_match_field set \<Rightarrow> simple_packet_ext \<Rightarrow> bool" where "OF_match_fields_unsafe m p = (\<forall>f \<in> m. match_no_prereq f p)"

definition "all_prerequisites f m \<equiv> \<forall>f \<in> m. prerequisites f m"

lemma of_safe_unsafe_match_eq: "all_prerequisites f m \<Longrightarrow> OF_match_fields m p = Some (OF_match_fields_unsafe m p)"
unfolding OF_match_fields_def OF_match_fields_unsafe_def comp_def set_seq_def match_prereq_def all_prerequisites_def
proof -	
	case goal1
	have 1: "(\<lambda>f. if prerequisites f m then Some (match_no_prereq f p) else None) ` m = (\<lambda>f. Some (match_no_prereq f p)) ` m"
		using goal1 by fastforce
	have 2: "\<forall>x\<in>(\<lambda>f. Some (match_no_prereq f p)) ` m. x \<noteq> None" by blast
	show ?case
		unfolding 1 unfolding eqTrueI[OF 2] unfolding if_True unfolding image_comp comp_def unfolding option.sel by(simp add: all_true_def)
qed



end