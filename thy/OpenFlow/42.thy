theory 42
imports "../Simple_Firewall/SimpleFw_Compliance" "Semantics_OpenFlow" "../Routing/AnnotateRouting"
begin

fun filter_nones where
"filter_nones [] = []" |
"filter_nones (s#ss) = (case s of None \<Rightarrow> [] | Some s \<Rightarrow> [s]) @ filter_nones ss"

lemma set_filter_nones: "k \<in> set (filter_nones ko) = (Some k \<in> set ko)"
	by(induction ko rule: filter_nones.induct) auto


(* For reference:
iiface :: "iface" --"in-interface"
oiface :: "iface" --"out-interface"
src :: "(ipv4addr \<times> nat) " --"source IP address"
dst :: "(ipv4addr \<times> nat) " --"destination"
proto :: "protocol"
sports :: "(16 word \<times> 16 word)" --"source-port first:last"
dports :: "(16 word \<times> 16 word)" --"destination-port first:last"

p_iiface :: string
p_oiface :: string
p_src :: ipv4addr
p_dst :: ipv4addr
p_proto :: primitive_protocol
p_sport :: "16 word"
p_dport :: "16 word"
p_tcp_flags :: "tcp_flag set"
p_tag_ctstate :: ctstate
*)
fun route2match :: "routing_rule \<Rightarrow> simple_rule list \<Rightarrow> simple_rule list" where
"route2match _ [] = []" |
"route2match r (m#ms) = filter_nones ((map (\<lambda>oi.
	let cr = \<lparr>iiface = ifaceAny, oiface = Iface (port_sel oi), src = (0,0), dst=(pfxm_prefix (routing_match r),pfxm_length (routing_match r)), proto=ProtoAny, sports=(0,max_word), ports=(0,max_word)\<rparr> in
	option_map (\<lambda>k. SimpleRule k (action_sel m)) (simple_match_and cr (match_sel m))
	) (routing_action r))) @ route2match r ms"

lemma r1: "\<not>a \<Longrightarrow> \<not>(a \<and> b)" by simp
lemma prepend_singleton: "[a] @ b = a # b" by simp

lemma simple_match_and_SomeD: "simple_match_and m1 m2 = Some m \<Longrightarrow> simple_matches m p = (simple_matches m1 p \<and> simple_matches m2 p)"
	using simple_match_and_correct by simp

lemma simple_fw_prepend_nonmatching: "\<forall>r \<in> set rs. \<not>simple_matches (match_sel r) p \<Longrightarrow> simple_fw_alt (rs @ rss) p = simple_fw_alt rss p"
	by(induction rs) simp_all

lemma 
	assumes "op = p \<circ> p_oiface_update (const i) \<circ> p_dst_update (const a) $ p'"
	assumes "valid_prefix pfx"
	assumes "prefix_match_semantics pfx a"
	shows "simple_fw fw p = simple_fw (route2match \<lparr>routing_match = pfx, routing_action = [Port i]\<rparr> fw) p"
unfolding comp_def fun_app_def simple_fw_alt
proof(induction fw)
	case (Cons s ss)
	thm simple_fw.cases
	thus ?case 
	proof(cases "simple_matches (match_sel s) p")
		case False 
		hence "\<forall>vr \<in> set (filter_nones (map (\<lambda>oi. map_option (\<lambda>k. SimpleRule k (action_sel s))
                    (simple_match_and
                      \<lparr>iiface = ifaceAny, oiface = Iface (port_sel oi), src = (0, 0), dst = (PrefixMatch.prefix_match.pfxm_prefix pfx, PrefixMatch.prefix_match.pfxm_length pfx), proto = ProtoAny, sports = (0, max_word),
                         dports = (0, max_word)\<rparr>
                      (match_sel s))) [Port i])). \<not>simple_matches (match_sel vr) p"
                      by(clarsimp simp only: set_filter_nones set_map Set.image_iff set_simps option_map_Some_eq2 simple_rule.sel) (fast dest: simple_match_and_SomeD) 
		from simple_fw_prepend_nonmatching[OF this] show ?thesis by(simp add: Let_def False Cons.IH)
	next
		let ?rr = "\<lparr>iiface = ifaceAny, oiface = Iface i, src = (0, 0), dst = (pfxm_prefix pfx, pfxm_length pfx), proto = ProtoAny, sports = (0, max_word), dports = (0, max_word)\<rparr>"
		note harr = simple_matches.simps assms(1)[unfolded comp_def fun_app_def] const_def match_ifaceAny ipv4range_set_from_bitmask_UNIV match_iface_refl iffD1[OF prefix_match_if_in_corny_set2, OF assms(2,3)]
		case True
		obtain a where a: "simple_match_and ?rr (match_sel s) = Some a"
           proof -
           	case goal1
           	have m: "simple_matches ?rr p"
           	unfolding assms(1)[unfolded comp_def fun_app_def] by(simp add: harr)
           	with True simple_match_and_correct[of ?rr p "match_sel s"] show thesis using goal1 by(simp split: option.splits)  
           qed
        moreover have "simple_matches a p"  apply(simp only: True simp_thms simple_match_and_SomeD[OF a]) by(simp add: harr)
		ultimately show ?thesis using True by(clarsimp)
	qed
qed(simp)

end