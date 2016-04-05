theory OpenFlowMatches
imports Main "../Bitmagic/NumberWangCaesar" "../Primitive_Matchers/Simple_Packet" "~~/src/HOL/Library/Monad_Syntax"
	"../Primitive_Matchers/Simple_Packet" (* I just want those TCP,UDP,\<dots> defs *)
	"~~/src/HOL/Library/Char_ord" (* For a linorder on strings. See below. *)
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
	| IPv4Src "32 prefix_match" (* could also be arbitrary bitmask - see page 80 of 1.5.1 *)
	| IPv4Dst "32 prefix_match" (* ditto *)
	| IPv4Proto "8 word"
(*	| IPv4ToS "16 word" *)
	| L4Src "16 word" "16 word" (* openvswitch 1.6 supports bitmasks - does not seem to be in of 1.5.1, but I need it. *)
	| L4Dst "16 word" "16 word"

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
"prerequisites (L4Src _ _) m = (\<exists>proto \<in> {TCP,UDP,SCTP}. let v = IPv4Proto proto in v \<in> m \<and> prerequisites v m)" |
"prerequisites (L4Dst _ _) m = prerequisites (L4Src undefined undefined) m"
by pat_completeness auto
(* Ignoredd PACKET_TYPE=foo *)

fun match_sorter :: "of_match_field \<Rightarrow> nat" where
"match_sorter (IngressPort _) = 1" |
"match_sorter (VlanId _) = 2" |
"match_sorter (VlanPriority _) = 3" |
"match_sorter (EtherType _) = 4" |
"match_sorter (EtherSrc _) = 5" |
"match_sorter (EtherDst _) = 6" |
"match_sorter (IPv4Proto _) = 7" |
"match_sorter (IPv4Src _) = 8" |
"match_sorter (IPv4Dst _) = 9" |
"match_sorter (L4Src _ _) = 10" |
"match_sorter (L4Dst _ _) = 11"

termination prerequisites by(relation "measure (match_sorter \<circ> fst)", simp_all)

definition "less_eq_of_match_field1 (a::of_match_field) (b::of_match_field) \<equiv> (case (a, b) of
		(IngressPort a, IngressPort b) \<Rightarrow> String.implode a \<le> String.implode b |
		(VlanId a, VlanId b) \<Rightarrow> a \<le> b |
		(EtherDst a, EtherDst b) \<Rightarrow> a \<le> b |
		(EtherSrc a, EtherSrc b) \<Rightarrow> a \<le> b |
		(EtherType a, EtherType b) \<Rightarrow> a \<le> b |
		(VlanPriority a, VlanPriority b) \<Rightarrow> a \<le> b |
		(IPv4Proto a, IPv4Proto b) \<Rightarrow> a \<le> b |
		(IPv4Src a, IPv4Src b) \<Rightarrow> a \<le> b |
		(IPv4Dst a, IPv4Dst b) \<Rightarrow> a \<le> b |
		(L4Src a1 a2, L4Src b1 b2) \<Rightarrow> if a2 = b2 then a1 \<le> b1 else a2 \<le> b2 |
		(L4Dst a1 a2, L4Dst b1 b2) \<Rightarrow> if a2 = b2 then a1 \<le> b1 else a2 \<le> b2 |
		(a, b) \<Rightarrow> match_sorter a < match_sorter b)"
(* feel free to move this to OpenFlowSerialize if it gets in the way. *)
instantiation of_match_field :: linorder
begin
	definition "less_eq_of_match_field (a::of_match_field) (b::of_match_field) \<equiv> less_eq_of_match_field1 a b"	
	definition "less_of_match_field (a::of_match_field) (b::of_match_field) \<equiv> (a \<noteq> b \<and> less_eq_of_match_field1 a b)"
instance by default (auto simp: less_eq_of_match_field_def less_eq_of_match_field1_def less_of_match_field_def implode_def split: prod.splits of_match_field.splits if_splits)
end

record simple_packet_ext = simple_packet +
	p_l2type :: "16 word"
	p_l2src :: "48 word"
	p_l2dst :: "48 word"
	p_vlanid :: "16 word"
	p_vlanprio :: "16 word"

definition "simple_packet_unext p = 
\<lparr>p_iiface = p_iiface p, p_oiface = p_oiface p, p_src = p_src p, p_dst = p_dst p, p_proto = p_proto p, 
p_sport = p_sport p, p_dport = p_dport p, p_tcp_flags = p_tcp_flags p, p_tag_ctstate = p_tag_ctstate p\<rparr>"


fun match_no_prereq :: "of_match_field \<Rightarrow> 'a simple_packet_ext_scheme \<Rightarrow> bool" where
"match_no_prereq (IngressPort i) p = (p_iiface p = i)" |
"match_no_prereq (EtherDst i) p = (p_l2src p = i)" |
"match_no_prereq (EtherSrc i) p = (p_l2dst p = i)" |
"match_no_prereq (EtherType i) p = (p_l2type p = i)" |
"match_no_prereq (VlanId i) p = (p_vlanid p = i)" | (* hack, otherwise it would be iso/osi *)
"match_no_prereq (VlanPriority i) p = (p_vlanprio p = i)" |
"match_no_prereq (IPv4Proto i) p = (p_proto p = i)" |
"match_no_prereq (IPv4Src i) p = (prefix_match_semantics i (p_src p))" |
"match_no_prereq (IPv4Dst i) p = (prefix_match_semantics i (p_dst p))" |
"match_no_prereq (L4Src i m) p = (p_sport p && m = i)" |
"match_no_prereq (L4Dst i m) p = (p_dport p && m = i)"

definition match_prereq :: "of_match_field \<Rightarrow> of_match_field set \<Rightarrow> 'a simple_packet_ext_scheme \<Rightarrow> bool option" where
"match_prereq i s p = (if prerequisites i s then Some (match_no_prereq i p) else None)"

definition "set_seq s \<equiv> if (\<forall>x \<in> s. x \<noteq> None) then Some (the ` s) else None"
definition "all_true s \<equiv> \<forall>x \<in> s. x"
term map_option
definition OF_match_fields :: "of_match_field set \<Rightarrow> 'a simple_packet_ext_scheme \<Rightarrow> bool option" where "OF_match_fields m p = map_option all_true (set_seq ((\<lambda>f. match_prereq f m p) ` m))"
definition OF_match_fields_unsafe :: "of_match_field set \<Rightarrow> 'a simple_packet_ext_scheme \<Rightarrow> bool" where "OF_match_fields_unsafe m p = (\<forall>f \<in> m. match_no_prereq f p)"
definition "OF_match_fields_safe m \<equiv> the \<circ> OF_match_fields m"

definition "all_prerequisites m \<equiv> \<forall>f \<in> m. prerequisites f m"

lemma (* as stated in paper *)
	"all_prerequisites p \<Longrightarrow>
	 L4Src x y \<in> p \<Longrightarrow>
	 IPv4Proto ` {TCP, UDP, SCTP} \<inter> p \<noteq> {}"
unfolding all_prerequisites_def by auto

lemma of_safe_unsafe_match_eq: "all_prerequisites m \<Longrightarrow> OF_match_fields m p = Some (OF_match_fields_unsafe m p)"
unfolding OF_match_fields_def OF_match_fields_unsafe_def comp_def set_seq_def match_prereq_def all_prerequisites_def
proof -	
	case goal1
	have 1: "(\<lambda>f. if prerequisites f m then Some (match_no_prereq f p) else None) ` m = (\<lambda>f. Some (match_no_prereq f p)) ` m"
		using goal1 by fastforce
	have 2: "\<forall>x\<in>(\<lambda>f. Some (match_no_prereq f p)) ` m. x \<noteq> None" by blast
	show ?case
		unfolding 1 unfolding eqTrueI[OF 2] unfolding if_True unfolding image_comp comp_def unfolding option.sel by(simp add: all_true_def)
qed

lemma of_match_fields_safe_eq: assumes "all_prerequisites m" shows "OF_match_fields_safe m = OF_match_fields_unsafe m"
unfolding OF_match_fields_safe_def[abs_def] fun_eq_iff comp_def unfolding of_safe_unsafe_match_eq[OF assms] unfolding option.sel by clarify 



end