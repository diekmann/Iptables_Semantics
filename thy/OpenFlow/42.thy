theory 42
imports 
	"../Simple_Firewall/SimpleFw_Compliance" 
	"Semantics_OpenFlow"
	"OpenFlowMatches"
	"../Routing/AnnotateRouting"
	"../Routing/LinuxRouter"
begin

fun filter_nones where
"filter_nones [] = []" |
"filter_nones (s#ss) = (case s of None \<Rightarrow> [] | Some s \<Rightarrow> [s]) @ filter_nones ss"

lemma set_filter_nones: "k \<in> set (filter_nones ko) = (Some k \<in> set ko)"
	by(induction ko rule: filter_nones.induct) auto
lemma set_filter_nones_simp: "set (filter_nones ko) = {k. Some k \<in> set ko}"
	using set_filter_nones by fast

lemma set_maps: "set (List.maps f a) = (\<Union>a\<in>set a. set (f a))" 
unfolding List.maps_def set_concat set_map UN_simps(10) ..


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

definition "route2match r = map (\<lambda>oi.
	\<lparr>iiface = ifaceAny, oiface = Iface (port_sel oi), 
	src = (0,0), dst=(pfxm_prefix (routing_match r),pfxm_length (routing_match r)), 
	proto=ProtoAny, sports=(0,max_word), ports=(0,max_word)\<rparr>)
	(routing_action r)"
                                    
fun simple_match_list_and :: "simple_match \<Rightarrow> simple_rule list \<Rightarrow> simple_rule list" where
"simple_match_list_and _ [] = []" |
"simple_match_list_and cr (m#ms) = filter_nones [option_map (\<lambda>k. SimpleRule k (action_sel m)) (simple_match_and cr (match_sel m))] @ simple_match_list_and cr ms"

lemma r1: "\<not>a \<Longrightarrow> \<not>(a \<and> b)" by simp
lemma prepend_singleton: "[a] @ b = a # b" by simp

lemma simple_match_and_SomeD: "simple_match_and m1 m2 = Some m \<Longrightarrow> simple_matches m p = (simple_matches m1 p \<and> simple_matches m2 p)"
	using simple_match_and_correct by simp

lemma simple_fw_prepend_nonmatching: "\<forall>r \<in> set rs. \<not>simple_matches (match_sel r) p \<Longrightarrow> simple_fw_alt (rs @ rss) p = simple_fw_alt rss p"
	by(induction rs) simp_all

(* this used to be two proofs in one, so it might be slightly more complicated than necessary *)
lemma simple_match_list_and_correct:
	assumes m: "simple_matches r p"
	shows "simple_fw fw p = simple_fw (simple_match_list_and r fw) p"
unfolding simple_fw_alt
proof(induction fw)
	case (Cons s ss)
	thm simple_fw.cases (* brrr *)
	thus ?case 
	proof(cases "simple_matches (match_sel s) p")
		case False
		hence "\<forall>vr \<in> set (filter_nones [option_map (\<lambda>k. SimpleRule k (action_sel s)) (simple_match_and r (match_sel s))]). \<not>simple_matches (match_sel vr) p"
			by(clarsimp simp only: set_filter_nones set_map Set.image_iff set_simps option_map_Some_eq2 simple_rule.sel)(fast dest: simple_match_and_SomeD) 
		from simple_fw_prepend_nonmatching[OF this] show ?thesis by(simp add: Let_def False Cons.IH)
	next
		case True
		obtain a where a: "simple_match_and r (match_sel s) = Some a" (*using True m simple_match_and_correct by force*)
           proof -
           	case goal1
           	have m: "simple_matches r p"
           	unfolding assms(1)[unfolded comp_def fun_app_def] using m .
           	with True simple_match_and_correct[of r p "match_sel s"] show thesis using goal1 by(simp split: option.splits)  
           qed
        moreover have "simple_matches a p"  by(simp only: m True simple_match_and_SomeD[OF a])
		ultimately show ?thesis using True by(clarsimp)
	qed
qed(simp)

lemma
	assumes "(op = p) \<circ> p_oiface_update (const i) \<circ> p_dst_update (const a) $ p'"
	assumes "valid_prefix pfx"
	assumes "prefix_match_semantics pfx a"
	assumes "Port i \<in> set ifs"
	shows "\<exists>r \<in> set (route2match \<lparr>routing_match = pfx, routing_action = ifs\<rparr>). simple_matches r p"
apply(simp add: simple_matches.simps assms(1)[unfolded comp_def fun_app_def] const_def route2match_def 
	match_ifaceAny ipv4range_set_from_bitmask_UNIV match_iface_refl iffD1[OF prefix_match_if_in_corny_set2, OF assms(2,3)])
apply(force intro: match_iface_eqI assms(4))
(* apply(rule bexI[OF _ assms(4)], simp add: match_iface_refl) *)
done

lemma
	assumes "(op = p) \<circ> p_oiface_update (const i) \<circ> p_dst_update (const a) $ p'"
	assumes "valid_prefix pfx"
	assumes "m \<in> set (route2match \<lparr>routing_match = pfx, routing_action = ifs\<rparr>)"
	assumes "simple_matches m p"
	assumes "Port i \<in> set ifs"
	shows "prefix_match_semantics pfx a"
oops

definition "option2set n \<equiv> (case n of None \<Rightarrow> {} | Some s \<Rightarrow> {s})"

definition toprefixmatch where
"toprefixmatch m \<equiv> PrefixMatch (fst m) (snd m)"
(* todo: disambiguate that prefix_match mess *)
lemma prefix_match_semantics_simple_match: 
	assumes vld: "NumberWangCaesar.valid_prefix (toprefixmatch m)" 
	shows "NumberWangCaesar.prefix_match_semantics (toprefixmatch m) = simple_match_ip m"
	apply(clarsimp simp add: fun_eq_iff)
	apply(subst NumberWangCaesar.prefix_match_if_in_corny_set[OF vld])
	apply(cases m)
	apply(clarsimp simp add: fun_eq_iff toprefixmatch_def ipv4range_set_from_bitmask_alt1 maskshift_eq_not_mask pfxm_mask_def)
done

definition "simple_match_to_of_match_single m iif prot sport dport \<equiv>
L4Src ` option2set sport \<union> L4Dst ` option2set dport
	 \<union> IPv4Proto ` (case prot of ProtoAny \<Rightarrow> {} | Proto p \<Rightarrow> {p}) (* protocol is an 8 word option anyway\<dots> *)
	 \<union> IngressPort ` option2set iif
	 \<union> {IPv4Src (toprefixmatch (src m)), IPv4Dst (toprefixmatch (dst m))}
	 \<union> {EtherType 0x0800}"
definition simple_match_to_of_match :: "simple_match \<Rightarrow> string list \<Rightarrow> of_match_field set list" where
"simple_match_to_of_match m ifs \<equiv> (let
	npm = (\<lambda>p. fst p = 0 \<and> snd p = max_word);
	sb = (\<lambda>p. (if npm p then [None] else if fst p \<le> snd p then map Some (word_upto (fst p) (snd p)) else []))
	in [simple_match_to_of_match_single m iif prot sport dport .
		iif \<leftarrow> (if iiface m = ifaceAny then [None] else [Some i. i \<leftarrow> ifs, match_iface (iiface m) i]),
		prot \<leftarrow> filter_nones \<circ> map (simple_proto_conjunct (proto m)) $
			(if npm (sports m) \<and> npm (dports m) then [ProtoAny] else map Proto [TCP,UDP,SCTP]),
		sport \<leftarrow> sb (sports m),
		dport \<leftarrow> sb (dports m)]
)"

lemma smtoms_cong: "a = e \<Longrightarrow> b = f \<Longrightarrow> c = g \<Longrightarrow> d = h \<Longrightarrow> simple_match_to_of_match_single r a b c d = simple_match_to_of_match_single r e f g h" by simp
(* this lemma is a bit stronger than what I actually need, but unfolds are convenient *)
lemma smtoms_eq_hlp: "simple_match_to_of_match_single r a b c d = simple_match_to_of_match_single r e f g h \<longleftrightarrow> (a = e \<and> b = f \<and> c = g \<and> d = h)"
apply(rule, simp_all)
apply(auto simp add: option2set_def simple_match_to_of_match_single_def toprefixmatch_def split: option.splits protocol.splits)
(* give this some time, it creates and solves 255 subgoals\<dots> *)
done

lemma conjunctSomeProtoAnyD: "Some ProtoAny = simple_proto_conjunct a (Proto b) \<Longrightarrow> False"
by(cases a) (simp_all split: if_splits)
lemma conjunctSomeProtoD: "Some (Proto x) = simple_proto_conjunct a (Proto b) \<Longrightarrow> x = b \<and> (a = ProtoAny \<or> a = Proto b)"
by(cases a) (simp_all split: if_splits)
lemma conjunctProtoD: "Some x = simple_proto_conjunct a (Proto b) \<Longrightarrow> x = Proto b \<and> (a = ProtoAny \<or> a = Proto b)"
by(cases a) (simp_all split: if_splits)

lemma simple_match_to_of_match_generates_prereqs: "r \<in> set (simple_match_to_of_match m ifs) \<Longrightarrow> all_prerequisites r"
unfolding simple_match_to_of_match_def simple_match_to_of_match_single_def all_prerequisites_def option2set_def
apply(clarsimp)
apply(erule disjE, (simp; fail))+
apply(unfold Set.image_iff)
apply(erule disjE)
 apply(case_tac xb)
  apply(simp; fail)
 apply(simp del: prerequisites.simps)
 apply(cases "fst (sports m) = 0 \<and> snd (sports m) = max_word \<and> fst (dports m) = 0 \<and> snd (dports m) = max_word")
  apply(simp; fail)
 apply(simp)
 apply(case_tac xa)
  apply(blast dest: conjunctSomeProtoAnyD)
 apply(auto dest: conjunctSomeProtoD)[1]
apply(erule disjE)
 apply(case_tac dport)
  apply(simp; fail)
 apply(simp del: prerequisites.simps)
 apply(cases "fst (sports m) = 0 \<and> snd (sports m) = max_word \<and> fst (dports m) = 0 \<and> snd (dports m) = max_word")
  apply(simp; fail)
 apply(simp)
 apply(case_tac xa)
 (* we could continue this pattern, but auto will take it from here. *)
  apply(force dest: conjunctSomeProtoD conjunctSomeProtoAnyD)+
done

lemma and_assoc: "a \<and> b \<and> c \<longleftrightarrow> (a \<and> b) \<and> c" by simp
lemma ex_bexI: "x \<in> A \<Longrightarrow> (x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<exists>x\<in>A. P x"
proof assume "x \<in> A \<Longrightarrow> P x" and "x \<in> A" thus "P x" .
next  assume "x \<in> A" thus "x \<in> A" . 
qed

lemmas custom_simpset = simple_match_to_of_match_def Let_def set_concat set_map map_map comp_def concat_map_maps set_maps UN_iff fun_app_def Set.image_iff

lemma bex_singleton: "\<exists>x\<in>{s}.P x = P s" by simp

lemma 
	assumes mm: "simple_matches r (simple_packet_unext p)"
	assumes ii: "p_iiface p \<in> set ifs"
	assumes ippkt: "p_l2type p = 0x800"
	assumes validr: "(proto r) \<notin> Proto ` {TCP,UDP,SCTP} \<Longrightarrow> ((fst (sports r) = 0 \<and> snd (sports r) = max_word) \<and> fst (dports r) = 0 \<and> snd (dports r) = max_word)"
	assumes validpfx1: "NumberWangCaesar.valid_prefix (toprefixmatch (src r))" (is "?vpfx (src r)") 
	assumes validpfx2: "?vpfx (dst r)"
	shows eq: "\<exists>gr \<in> set (simple_match_to_of_match r ifs). OF_match_fields gr p = Some True"
proof
	let ?npm = "\<lambda>p. fst p = 0 \<and> snd p = max_word"
	let ?sb = "\<lambda>p r. (if ?npm p then None else Some r)"
	let ?protcond = "?npm (sports r) \<and> ?npm (dports r) \<and> proto r = ProtoAny"
	let ?foo = "simple_match_to_of_match_single r 
		(if iiface r = ifaceAny then None else Some (p_iiface p)) 
		(if ?protcond then ProtoAny else Proto (p_proto p))
		(?sb (sports r) (p_sport p)) (?sb (dports r) (p_dport p))"
	note mfu = simple_match_port.simps[of "fst (sports r)" "snd (sports r)", unfolded surjective_pairing[of "sports r",symmetric]]
			   simple_match_port.simps[of "fst (dports r)" "snd (dports r)", unfolded surjective_pairing[of "dports r",symmetric]]
	note u = mm[unfolded simple_matches.simps mfu ord_class.atLeastAtMost_iff simple_packet_unext_def simple_packet.simps]
	note of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs]
	from u have ple: "fst (sports r) \<le> snd (sports r)" "fst (dports r) \<le> snd (dports r)" by force+
	have sdpe: "(p_sport p) \<in> set (word_upto (fst (sports r)) (snd (sports r)))" "(p_dport p) \<in> set (word_upto (fst (dports r)) (snd (dports r)))" 
		unfolding word_upto_set_eq[OF ple(1)] word_upto_set_eq[OF ple(2)] using u by simp_all 
	show eg: "?foo \<in> set (simple_match_to_of_match r ifs)"
		unfolding simple_match_to_of_match_def
		unfolding custom_simpset
		unfolding smtoms_eq_hlp
		proof(rule,rule,rule,rule,rule,rule refl,rule,rule refl,rule,rule refl,rule refl)
			case goal1 thus ?case using ple(2) sdpe(2) by simp
		next
			case goal2 thus ?case using ple(1) sdpe(1) by simp
		next
			case goal3 thus ?case 
				apply(simp only: set_filter_nones list.map set_simps singleton_iff simple_proto_conjunct_asimp  split: if_splits)
				apply(rule)
				 apply(rule)
				  apply(rule)
				  apply(simp)
				 apply(clarsimp)
				 apply(metis u match_proto.elims(2))
				apply(rule)
				 apply(rule)
				apply(rule)
				 apply(clarsimp;fail)
				apply(rule)
				apply(erule contrapos_np)
				apply(rule validr)
				apply(clarsimp)
				apply(cases "proto r")
				 apply(simp;fail)
				using u apply(simp split: if_splits)
			done
		next
			case goal4 thus ?case by(simp add: set_maps ii u)
		qed
	show "OF_match_fields ?foo p = Some True"
	unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF eg]]
		by(simp_all add: simple_match_to_of_match_single_def OF_match_fields_unsafe_def option2set_def prefix_match_semantics_simple_match validpfx1 validpfx2 u ippkt)
qed

lemma 
	assumes eg: "gr \<in> set (simple_match_to_of_match r ifs)"
	assumes mo: "OF_match_fields gr p = Some True"
	assumes me: "match_iface (oiface r) (p_oiface p)"
	assumes validpfx1: "NumberWangCaesar.valid_prefix (toprefixmatch (src r))" (is "?vpfx (src r)")
	assumes validpfx2: "?vpfx (dst r)"
	shows "simple_matches r (simple_packet_unext p)"
proof -
	from mo have mo: "OF_match_fields_unsafe gr p" 
		unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF eg]]
		by simp
	note this[unfolded OF_match_fields_unsafe_def]
	note eg[unfolded custom_simpset simple_match_to_of_match_single_def]
	then guess x ..
	moreover from this(2) guess xa ..
	moreover from this(2) guess xb ..
	moreover from this(2) guess xc ..
	moreover from calculation(3)[unfolded set_filter_nones_simp set_map mem_Collect_eq Set.image_iff] guess xd ..
	note xx = calculation(8,1,5,7) this
	show ?thesis unfolding simple_matches.simps
	proof(unfold and_assoc, (rule)+)
		case goal1 thus ?case 
			apply(cases "iiface r = ifaceAny") 
			 apply (simp add: match_ifaceAny) 
			using mo xx(2) unfolding xx(1) OF_match_fields_unsafe_def
			apply(simp only: if_False set_maps UN_iff)
			apply(clarify)
			apply(rename_tac a; subgoal_tac "match_iface (iiface r) a") 
			 apply(clarsimp simp add: simple_packet_unext_def option2set_def)
			apply(rule ccontr,simp;fail)
		done
	next
		case goal2 thus ?case unfolding simple_packet_unext_def simple_packet.simps using me .
	next
		case goal3 thus ?case
			using mo unfolding xx(1) OF_match_fields_unsafe_def
			 by(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match validpfx1)
	next
		case goal4 thus ?case
			using mo unfolding xx(1) OF_match_fields_unsafe_def
			 by(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match validpfx2)
	next
		case goal5 thus ?case
			using mo unfolding xx(1) OF_match_fields_unsafe_def
			apply(simp)
			apply(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match)
			using xx(5,6)
			apply(simp only: set_simps singleton_iff simple_proto_conjunct_asimp split: if_splits protocol.splits)
			   apply(simp;fail)
			  apply(simp)
			  apply(metis match_proto.simps(2))
			 apply(simp)
			 apply(blast dest: conjunctSomeProtoAnyD)
			apply(simp)
			apply(erule disjE | simp, drule conjunctSomeProtoD, cases "proto r", (simp;fail), (simp;fail))+
		done
	next
		case goal6 thus ?case
			using mo xx(3) unfolding xx(1) OF_match_fields_unsafe_def
			apply(cases "sports r")
			apply(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
			apply(rule word_upto_set_eq2)
			 apply(simp_all)
		done
	next
		case goal7 thus ?case using mo xx(4) unfolding xx(1) OF_match_fields_unsafe_def
			apply(cases "dports r")
			apply(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
			apply(rule word_upto_set_eq2)
			 apply(simp_all)
		done
    qed
qed

fun annotate_rlen where
"annotate_rlen [] = []" |
"annotate_rlen (a#as) = (length as, a) # annotate_rlen as"
value "annotate_rlen ''asdf''"

lemma fst_annotate_rlen_le: "(k, a) \<in> set (annotate_rlen l) \<Longrightarrow> k < length l"
	apply(induction l arbitrary: k)
	 apply simp
	apply fastforce
done
lemma distinct_fst_annotate_rlen: "distinct (map fst (annotate_rlen l))"
	using fst_annotate_rlen_le by(induction l) (simp, fastforce)
lemma distinct_annotate_rlen: "distinct (annotate_rlen l)"
	using distinct_fst_annotate_rlen unfolding distinct_map by blast

fun annotate_rlen_code where
"annotate_rlen_code [] = (0,[])" |
"annotate_rlen_code (a#as) = (case annotate_rlen_code as of (r,aas) \<Rightarrow> (Suc r, (r, a) # aas))"
lemma annotate_rlen_len: "fst (annotate_rlen_code r) = length r"
by(induction r) (clarsimp split: prod.splits)+
lemma annotate_rlen_code[code]: "annotate_rlen s = snd (annotate_rlen_code s)"
	apply(induction s)
	 apply(simp)
	apply(clarsimp split: prod.split)
	apply(metis annotate_rlen_len fst_conv)
done

lemma "sorted_descending (map fst (annotate_rlen l))"
apply(induction l)
apply(simp)
apply(clarsimp)
apply(force dest: fst_annotate_rlen_le)
done

(* why is there curry *)
find_consts "(('a \<times> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
(* but no "uncurry" *)
find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'c"
definition "split3 f p \<equiv> case p of (a,b,c) \<Rightarrow> f a b c"
find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<times> 'b \<times> 'c) \<Rightarrow> 'd"

find_theorems "word_of_nat"
find_consts "nat \<Rightarrow> 'a word"

lemma suc2plus_inj_on: "inj_on (word_of_nat :: nat \<Rightarrow> ('l :: len) word) {0..unat (max_word :: 'l word)}"
proof(rule inj_onI)
	let ?mmw = "(max_word :: 'l word)"
	let ?mstp = "(word_of_nat :: nat \<Rightarrow> 'l word)"
	fix x y :: nat
	assume "x \<in> {0..unat ?mmw}" "y \<in> {0..unat ?mmw}"
	hence se: "x \<le> unat ?mmw" "y \<le> unat ?mmw" by simp_all
	assume eq: "?mstp x = ?mstp y"
	note f = le_unat_uoi[OF se(1)] le_unat_uoi[OF se(2)]
	(*show "x = y"
	apply(subst f(1)[symmetric])
	apply(subst f(2)[symmetric])
	apply(subst word_unat.Rep_inject)
	using eq .*)
	show "x = y" using eq le_unat_uoi se by metis
qed

lemma distinct_word_of_nat_list: (* TODO: Move to CaesarWordLemmaBucket *)
	"distinct l \<Longrightarrow> \<forall>e \<in> set l. e \<le> unat (max_word :: ('l::len) word) \<Longrightarrow> distinct (map (word_of_nat :: nat \<Rightarrow> 'l word) l)"
proof(induction l)
	let ?mmw = "(max_word :: 'l word)"
	let ?mstp = "(word_of_nat :: nat \<Rightarrow> 'l word)"
	case (Cons a as)
	have "distinct as" "\<forall>e\<in>set as. e \<le> unat ?mmw" using Cons.prems by simp_all 
	note mIH = Cons.IH[OF this]
	moreover have "?mstp a \<notin> ?mstp ` set as"
	proof 
		have representable_set: "set as \<subseteq> {0..unat ?mmw}" using `\<forall>e\<in>set (a # as). e \<le> unat max_word` by fastforce
		have a_reprbl: "a \<in> {0..unat ?mmw}" using `\<forall>e\<in>set (a # as). e \<le> unat max_word` by simp
		assume "?mstp a \<in> ?mstp ` set as"
		with inj_on_image_mem_iff[OF suc2plus_inj_on a_reprbl representable_set]
		have "a \<in> set as" by simp
		with `distinct (a # as)` show False by simp
	qed
	ultimately show ?case by simp
qed simp

lemma annotate_first_le_hlp:
	"length l < unat (max_word :: ('l :: len) word) \<Longrightarrow> \<forall>e\<in>set (map fst (annotate_rlen l)). e \<le> unat (max_word :: 'l word)"
	by(clarsimp) (meson fst_annotate_rlen_le less_trans nat_less_le)
lemmas distinct_of_prio_hlp = distinct_word_of_nat_list[OF distinct_fst_annotate_rlen annotate_first_le_hlp]
(* don't need these right now, but maybe later? *)
lemma distinct_fst_won_list_unused:
	"distinct (map fst l) \<Longrightarrow> 
	\<forall>e \<in> set l. fst e \<le> unat (max_word :: ('l::len) word) \<Longrightarrow> 
	distinct (map (apfst (word_of_nat :: nat \<Rightarrow> 'l word)) l)"
proof -
	let ?mw = "(max_word :: 'l word)"
	let ?won = "(word_of_nat :: nat \<Rightarrow> 'l word)"
	case goal1
	obtain fl where fl: "fl = map fst l" by simp
	with goal1 have "distinct fl" "\<forall>e \<in> set fl. e \<le> unat ?mw" by simp_all
	note distinct_word_of_nat_list[OF this, unfolded fl]
	hence "distinct (map fst (map (apfst ?won) l))" by simp
	thus ?case by (metis distinct_zipI1 zip_map_fst_snd)
qed
lemma annotate_first_le_hlp_unused:
	"length l < unat (max_word :: ('l :: len) word) \<Longrightarrow> \<forall>e\<in>set (annotate_rlen l). fst e \<le> unat (max_word :: 'l word)"
	by(clarsimp) (meson fst_annotate_rlen_le less_trans nat_less_le)


lemma fst_annotate_rlen: "map fst (annotate_rlen l) = rev [0..<length l]"
by(induction l) (simp_all)

lemma sorted_annotated:
	assumes "length l \<le> unat (max_word :: ('l :: len) word)"
	shows "sorted_descending (map fst (map (apfst (word_of_nat :: nat \<Rightarrow> 'l word)) (annotate_rlen l)))"
proof -
	let ?won = "(word_of_nat :: nat \<Rightarrow> 'l word)"
	have zero_subst: "?won 0 = (0 :: 'l word)" by simp
	have "sorted_descending (rev (word_upto 0 (?won (length l))))" 
		unfolding sorted_descending by(rule sorted_word_upto) simp
	hence "sorted_descending (map ?won (rev [0..<Suc (length l)]))" 
		unfolding word_upto_eq_upto[OF le0 assms, unfolded zero_subst] rev_map .
	hence "sorted_descending (map ?won (map fst (annotate_rlen l)))" by(simp add: fst_annotate_rlen)
	thus "sorted_descending (map fst (map (apfst ?won) (annotate_rlen l)))" by simp
qed

definition "fourtytwo_s3 ard ifs = [(a, b, case action_sel r of simple_action.Accept \<Rightarrow> c | simple_action.Drop \<Rightarrow> []).
		(a,r,c) \<leftarrow> ard, b \<leftarrow> simple_match_to_of_match (match_sel r) ifs]"
		(* take prepared rule list and make openflow matches from the simple_rules *) 

definition "fourtytwo rt fw ifs \<equiv> let
	mrt = [(m, routing_action  r). r \<leftarrow> rt, m \<leftarrow> route2match r]; (* make matches from those rt entries *)
	frd = [Pair b c. (a,c) \<leftarrow> mrt, b \<leftarrow> simple_match_list_and a fw]; (* bring down the firewall over all rt matches *)
	ard = map (apfst word_of_nat) $ annotate_rlen frd in (* give them a priority *)
	if length frd < unat (max_word :: 16 word)
	then Inr (map (split3 OFEntry) $ fourtytwo_s3 ard ifs)
	else Inl ''Error in creating OpenFlow table: priority number space exhausted''
"
thm fourtytwo_def[unfolded Let_def comp_def fun_app_def fourtytwo_s3_def] (* it's a monster *)

lemma map_injective_eq: "map f xs = map g ys \<Longrightarrow> (\<And>e. f e = g e) \<Longrightarrow> inj f \<Longrightarrow> xs = ys"
	apply(rule map_injective, defer_tac)
	 apply(simp)+
done

lemma "distinct x \<Longrightarrow> inj_on g (set x) \<Longrightarrow> inj_on f (set (concat (map g x))) \<Longrightarrow> distinct [f a. b \<leftarrow> x, a \<leftarrow> g b]"
apply(clarify;fail | rule distinct_concat | subst distinct_map, rule)+
apply(rule inj_onI)
apply(unfold set_concat set_map)
find_theorems "map ?f _ = map ?f _"
oops

lemma list_at_eqD: "aa @ ab = ba @ bb \<Longrightarrow> length aa = length ba \<Longrightarrow> length ab = length bb \<Longrightarrow> aa = ba \<and> ab = bb"
by simp
lemma list_induct_2simul:
	"P [] [] \<Longrightarrow> (\<And>a as bs. P as bs \<Longrightarrow> P (a # as) bs) \<Longrightarrow> (\<And>b as bs. P as bs \<Longrightarrow> P as (b # bs)) \<Longrightarrow> P x y"
	apply(induction x)
	 apply(metis list_nonempty_induct)
	apply(induction y)
	 apply(simp)
	apply(simp)
done
lemma list_induct_3simul:
	"P [] [] [] \<Longrightarrow> 
	(\<And>e a b c. P a b c \<Longrightarrow> P (e # a) b c) \<Longrightarrow>
	(\<And>e a b c. P a b c \<Longrightarrow> P a (e # b) c) \<Longrightarrow>
	(\<And>e a b c. P a b c \<Longrightarrow> P a b (e # c)) \<Longrightarrow>
	P x y z"
	apply(induction x)
	 apply(induction y)
	  apply(induction z)
	    apply(simp_all)
done
lemma list_induct_4simul:
	"P [] [] [] [] \<Longrightarrow> 
	(\<And>e a b c d. P a b c d \<Longrightarrow> P (e # a) b c d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a (e # b) c d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a b (e # c) d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a b c (e # d)) \<Longrightarrow>
	P x y z w"
	apply(induction x)
	 apply(induction y)
	  apply(induction z)
	   apply(induction w)
	    apply(simp_all)
done

lemma "distinct (e # a) = distinct (f (e # a))"
oops

lemma distinct_2lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow>
	(\<And>a b e i. f a b = f e i \<Longrightarrow> a = e \<and> b = i) \<Longrightarrow>
	distinct [f a b. a \<leftarrow> as, b \<leftarrow> bs]"
apply(induction as)
apply(simp;fail)
apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
apply(rule)
defer
apply fastforce
apply(clarify;fail | subst distinct_map, rule)+
apply(rule inj_onI)
apply(simp)
done

lemma distinct_3lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow> distinct cs \<Longrightarrow>
	(\<And>a b c e i g. f a b c = f e i g \<Longrightarrow> a = e \<and> b = i \<and> c = g) \<Longrightarrow>
	distinct [f a b c. a \<leftarrow> as, b \<leftarrow> bs, c \<leftarrow> cs]"
apply(induction as)
apply(simp;fail)
apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
apply(rule)
apply(rule distinct_2lcomprI; simp_all; fail)
apply fastforce
done

lemma distinct_4lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow> distinct cs \<Longrightarrow> distinct ds \<Longrightarrow>
	(\<And>a b c d e i g h. f a b c d = f e i g h \<Longrightarrow> a = e \<and> b = i \<and> c = g \<and> d = h) \<Longrightarrow>
	distinct [f a b c d. a \<leftarrow> as, b \<leftarrow> bs, c \<leftarrow> cs, d \<leftarrow> ds]"
apply(induction as)
apply(simp;fail)
apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
apply(rule)
apply(rule distinct_3lcomprI; simp_all; fail)
apply fastforce
done


lemma distinct_simple_match_to_of_match: "distinct ifs \<Longrightarrow> distinct (simple_match_to_of_match m ifs)"
apply(unfold simple_match_to_of_match_def Let_def)
apply(rule distinct_4lcomprI)
apply(clarsimp)
apply(induction ifs)
apply(simp;fail)
apply(simp;fail)
apply(cases "proto m")
apply(clarsimp simp add: TCP_def UDP_def SCTP_def split: option.splits; fail)
apply(clarsimp simp add: TCP_def UDP_def SCTP_def split: option.splits; fail)
apply(simp_all)
apply(unfold distinct_map)
apply(simp_all add: distinct_word_upto smtoms_eq_hlp)
done
lemma no_overlaps_42_hlp2: "distinct (map fst amr) \<Longrightarrow> (\<And>r. distinct (fm r)) \<Longrightarrow>
    distinct (concat (map (\<lambda>(a, r, c). map (\<lambda>b. (a, b, fs r c)) (fm r)) amr))"
apply(induction amr)
apply(simp;fail)
apply(simp only: list.map concat.simps distinct_append)
apply(rule)
apply(clarsimp simp add: distinct_map split: prod.splits)
apply(rule inj_inj_on)
apply(rule injI)
apply(simp;fail)
apply(rule)
apply(simp)
apply(force)
done

lemma no_overlaps_42_hlp3: "distinct (map fst amr) \<Longrightarrow>
(aa, ab, ba) \<in> set (fourtytwo_s3 amr ifs) \<Longrightarrow> (ac, ad, bb) \<in> set (fourtytwo_s3 amr ifs) \<Longrightarrow>
ba \<noteq> bb \<Longrightarrow> aa \<noteq> ac"
apply(unfold fourtytwo_s3_def)
apply(clarsimp)
apply(clarsimp split: simple_action.splits)
apply(metis map_of_eq_Some_iff option.inject prod.inject)
apply(metis fst_eqD map_of_eq_Some_iff option.inject simple_action.distinct(1))+
done

lemma no_overlaps_42_hlp4: "distinct (map fst amr) \<Longrightarrow>
 (aa, ab, ac) \<in> set amr \<Longrightarrow> (ba, bb, bc) \<in> set amr \<Longrightarrow>
 ab \<noteq> bb \<Longrightarrow> aa \<noteq> ba"
by (metis map_of_eq_Some_iff old.prod.inject option.inject)

lemma "
	OF_match_fields_unsafe (simple_match_to_of_match_single m a b c d) p \<Longrightarrow>
	OF_match_fields_unsafe (simple_match_to_of_match_single m e f g h) p \<Longrightarrow>
	(a = e \<and> b = f \<and> c = g \<and> d = h)"
apply(cases h, case_tac[!] d)
apply(simp_all add: OF_match_fields_unsafe_def simple_match_to_of_match_single_def option2set_def)
oops

lemma no_overlaps_42_hlp: "distinct (map fst amr) \<Longrightarrow> distinct ifs \<Longrightarrow> 
no_overlaps OF_match_fields_unsafe (map (split3 OFEntry) (fourtytwo_s3 amr ifs))"
apply(rule no_overlapsI, defer_tac)
apply(subst distinct_map, rule)
prefer 2
apply(rule inj_inj_on)
apply(rule injI)
apply(rename_tac x y, case_tac x, case_tac y)
apply(simp add: split3_def;fail)
apply(unfold fourtytwo_s3_def)[1]
apply(rule no_overlaps_42_hlp2; simp_all add: distinct_simple_match_to_of_match)
apply(unfold check_no_overlap_def)
apply(clarify)
apply(unfold set_map)
apply(clarify)
apply(unfold split3_def prod.simps flow_entry_match.simps flow_entry_match.sel de_Morgan_conj)
apply(erule disjE)
apply(clarify;fail)
apply(erule disjE, defer_tac)
apply(simp add: no_overlaps_42_hlp3; fail)
apply(clarsimp simp add: fourtytwo_s3_def)
apply(case_tac "ae \<noteq> ag")
apply(metis no_overlaps_42_hlp4)
apply(clarify | unfold 
	simple_match_to_of_match_def smtoms_eq_hlp Let_def set_concat set_map de_Morgan_conj not_False_eq_True)+
apply(simp add:  comp_def  smtoms_eq_hlp split: if_splits)
apply(auto dest: conjunctSomeProtoAnyD split: protocol.splits option.splits
	simp add: OF_match_fields_unsafe_def simple_match_to_of_match_single_def option2set_def) (* another 160 subgoal split *)
by -
 
lemma assumes "distinct ifs" shows "Inr t = (fourtytwo rt fw ifs) \<Longrightarrow> no_overlaps OF_match_fields_unsafe t"
	apply(unfold fourtytwo_def Let_def)
	apply(simp split: if_splits)
	apply(thin_tac "t = _")
	apply(drule distinct_of_prio_hlp)
	apply(rule no_overlaps_42_hlp[OF _ assms])
	apply(simp)
done

lemma sorted_const: "sorted (map (\<lambda>y. x) k)" (* TODO: move *)
	by(induction k) (simp_all add: sorted_Cons)

lemma sorted_fourtytwo_s3_hlp: "\<forall>x\<in>set f. fst x \<le> a \<Longrightarrow> b \<in> set (fourtytwo_s3 f s) \<Longrightarrow> fst b \<le> a" 
	by(auto simp add: fourtytwo_s3_def)

lemma sorted_fourtytwo_s3: "sorted_descending (map fst f) \<Longrightarrow> sorted_descending (map fst (fourtytwo_s3 f s))"
	apply(induction f)
	apply(simp add: fourtytwo_s3_def)
	apply(clarsimp)
	apply(subst fourtytwo_s3_def)
	apply(clarsimp)
	apply(subst fourtytwo_s3_def[symmetric])
	apply(unfold map_concat map_map comp_def)
	apply(unfold sorted_descending_append)
	apply(simp add: sorted_descending_alt rev_map sorted_const sorted_fourtytwo_s3_hlp)
done

lemma sorted_fourtytwo_hlp: "(ofe_prio \<circ> split3 OFEntry) = fst" by(simp add: fun_eq_iff comp_def split3_def)

lemma "Inr r = fourtytwo rt fw ifs \<Longrightarrow> sorted_descending (map ofe_prio r)"
	apply(unfold fourtytwo_def Let_def)
	apply(simp split: if_splits)
	apply(thin_tac "r = _")
	apply(unfold sorted_fourtytwo_hlp)
	apply(rule sorted_fourtytwo_s3)
	apply(rule sorted_annotated)
	apply simp
done

end