theory 42
imports 
	"../Simple_Firewall/Generic_SimpleFw" 
	"Semantics_OpenFlow"
	"OpenFlowMatches"
	"OpenFlowAction"
	(*"../Routing/AnnotateRouting"*)
	"../Routing/LinuxRouter"
begin

primrec filter_nones where
"filter_nones [] = []" |
"filter_nones (s#ss) = (case s of None \<Rightarrow> [] | Some s \<Rightarrow> [s]) @ filter_nones ss"

lemma set_filter_nones: "k \<in> set (filter_nones ko) = (Some k \<in> set ko)"
	by(induction ko) auto
lemma set_filter_nones_simp: "set (filter_nones ko) = {k. Some k \<in> set ko}"
	using set_filter_nones by fast
lemma filter_nones_filter_map[code_unfold]: "filter_nones x = map the (filter (op \<noteq> None)  x)"
by(induction x) (simp_all split: option.splits)

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

definition "route2match r =
	\<lparr>iiface = ifaceAny, oiface = ifaceAny, 
	src = (0,0), dst=(pfxm_prefix (routing_match r),pfxm_length (routing_match r)), 
	proto=ProtoAny, sports=(0,max_word), ports=(0,max_word)\<rparr>"

definition "simple_rule_and a r \<equiv> option_map (\<lambda>k. SimpleRule k (action_sel r)) (simple_match_and a (match_sel r))"

primrec simple_match_list_and :: "simple_match \<Rightarrow> simple_rule list \<Rightarrow> simple_rule list" where
"simple_match_list_and _ [] = []" |
"simple_match_list_and cr (m#ms) = filter_nones [simple_rule_and cr m] @ simple_match_list_and cr ms"

lemma simple_match_list_and_alt[code_unfold]:
	"simple_match_list_and cr m = filter_nones (map (simple_rule_and cr) m)"
	by(induction m; simp)

lemma r1: "\<not>a \<Longrightarrow> \<not>(a \<and> b)" by simp
lemma prepend_singleton: "[a] @ b = a # b" by simp

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
			apply(clarsimp simp only: set_filter_nones set_map Set.image_iff set_simps option_map_Some_eq2 simple_rule.sel)
			using simple_match_and_SomeD by (smt map_option_eq_Some simple_rule.sel(1) singleton_set) (* this proof and all that use it can be deleted *)
		from simple_fw_prepend_nonmatching[OF this] show ?thesis by(simp add: Let_def False Cons.IH simple_rule_and_def)
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
		ultimately show ?thesis using True by(clarsimp simp:  simple_rule_and_def)
	qed
qed(simp)

(*lemma
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
oops*)

definition toprefixmatch where
"toprefixmatch m \<equiv> (let pm = PrefixMatch (fst m) (snd m) in if pm = PrefixMatch 0 0 then None else Some pm)"
lemma prefix_match_semantics_simple_match: 
  assumes some: "toprefixmatch m = Some pm"
	assumes vld: "valid_prefix pm"
	shows "prefix_match_semantics pm = simple_match_ip m"
using some
	apply(clarsimp simp add: fun_eq_iff)
	apply(subst NumberWangCaesar.prefix_match_if_in_corny_set[OF vld])
	apply(cases m)
	apply(clarsimp simp add: fun_eq_iff toprefixmatch_def ipv4range_set_from_prefix_alt1 maskshift_eq_not_mask pfxm_mask_def split: if_splits)
done

definition "simple_match_to_of_match_single m iif prot sport dport \<equiv>
	   split L4Src ` option2set sport \<union> split L4Dst ` option2set dport
	 \<union> IPv4Proto ` (case prot of ProtoAny \<Rightarrow> {} | Proto p \<Rightarrow> {p}) (* protocol is an 8 word option anyway\<dots> *)
	 \<union> IngressPort ` option2set iif
	 \<union> IPv4Src ` option2set (toprefixmatch (src m)) \<union> IPv4Dst ` option2set (toprefixmatch (dst m))
	 \<union> {EtherType 0x0800}"
(* okay, we need to make sure that no packets are output on the interface they were input on. So for rules that don't have an input interface, we'd need to do a product over all interfaces, if we stay naive.
   The more smart way would be to insert a rule with the same match condition that additionally matches the input interface and drops. However, I'm afraid this is going to be very tricky to verify\<dots> *)
definition simple_match_to_of_match :: "simple_match \<Rightarrow> string list \<Rightarrow> of_match_field set list" where
"simple_match_to_of_match m ifs \<equiv> (let
	npm = (\<lambda>p. fst p = 0 \<and> snd p = max_word);
	sb = (\<lambda>p. (if npm p then [None] else if fst p \<le> snd p then map (Some \<circ> (\<lambda>pfx. (pfxm_prefix pfx, NOT pfxm_mask pfx))) (wordinterval_CIDR_split_internal (WordInterval (fst p) (snd p))) else []))
	in [simple_match_to_of_match_single m iif (proto m) sport dport.
		iif \<leftarrow> (if iiface m = ifaceAny then [None] else [Some i. i \<leftarrow> ifs, match_iface (iiface m) i]),
		sport \<leftarrow> sb (sports m),
		dport \<leftarrow> sb (dports m)]
)"
(* I wonder\<dots> should I check whether list_all (match_iface (iiface m)) ifs instead of iiface m = ifaceAny? It would be pretty stupid if that wasn't the same, but you know\<dots> *)

lemma smtoms_cong: "a = e \<Longrightarrow> b = f \<Longrightarrow> c = g \<Longrightarrow> d = h \<Longrightarrow> simple_match_to_of_match_single r a b c d = simple_match_to_of_match_single r e f g h" by simp
(* this lemma is a bit stronger than what I actually need, but unfolds are convenient *)
lemma smtoms_eq_hlp: "simple_match_to_of_match_single r a b c d = simple_match_to_of_match_single r f g h i \<longleftrightarrow> (a = f \<and> b = g \<and> c = h \<and> d = i)"
apply(rule, simp_all)
apply(simp add: option2set_def simple_match_to_of_match_single_def toprefixmatch_def)
apply(simp add: split: option.splits)
apply(simp add: split: if_splits protocol.splits prod.splits | blast)+
(* give this some time, it creates and solves a ton of subgoals\<dots> Takes 140 seconds for me. *)
done

lemma conjunctSomeProtoAnyD: "Some ProtoAny = simple_proto_conjunct a (Proto b) \<Longrightarrow> False"
by(cases a) (simp_all split: if_splits)
lemma conjunctSomeProtoD: "Some (Proto x) = simple_proto_conjunct a (Proto b) \<Longrightarrow> x = b \<and> (a = ProtoAny \<or> a = Proto b)"
by(cases a) (simp_all split: if_splits)
lemma conjunctProtoD: "Some x = simple_proto_conjunct a (Proto b) \<Longrightarrow> x = Proto b \<and> (a = ProtoAny \<or> a = Proto b)"
by(cases a) (simp_all split: if_splits)

lemma proto_in_srcdst: "IPv4Proto x \<in> IPv4Src ` s \<longleftrightarrow> False" "IPv4Proto x \<in> IPv4Dst ` s \<longleftrightarrow> False" by fastforce+
lemma simple_match_port_UNIVD: "Collect (simple_match_port a) = UNIV \<Longrightarrow> fst a = 0 \<and> snd a = max_word" by (metis antisym_conv fst_conv hrule max_word_max mem_Collect_eq simple_match_port_code snd_conv surj_pair word_le_0_iff)
lemma simple_match_to_of_match_generates_prereqs: "simple_match_valid m \<Longrightarrow> r \<in> set (simple_match_to_of_match m ifs) \<Longrightarrow> all_prerequisites r"
unfolding simple_match_to_of_match_def Let_def
proof(clarsimp, goal_cases)
  case (1 xiface xsrcp xdstp)
  note o = this
  show ?case unfolding simple_match_to_of_match_single_def all_prerequisites_def
    unfolding ball_Un
  proof((intro conjI; ((simp;fail)| - )), goal_cases)
    case 1
    have e: "(fst (sports m) = 0 \<and> snd (sports m) = max_word) \<or> proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto SCTP"
      using o(1)
      unfolding simple_match_valid_alt Let_def
      by(clarsimp split: if_splits)
    show ?case
      using o(3) e
      by(elim disjE; simp add: option2set_def split: if_splits prod.splits;fail)
  next
    case 2
    have e: "(fst (dports m) = 0 \<and> snd (dports m) = max_word) \<or> proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto SCTP"
      using o(1)
      unfolding simple_match_valid_alt Let_def
      by(clarsimp split: if_splits)
    show ?case
      using o(4) e
      by(elim disjE; simp add: option2set_def split: if_splits prod.splits;fail)
  qed
qed

lemma and_assoc: "a \<and> b \<and> c \<longleftrightarrow> (a \<and> b) \<and> c" by simp
lemma ex_bexI: "x \<in> A \<Longrightarrow> (x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<exists>x\<in>A. P x"
proof assume "x \<in> A \<Longrightarrow> P x" and "x \<in> A" thus "P x" .
next  assume "x \<in> A" thus "x \<in> A" . 
qed

lemmas custom_simpset = Let_def set_concat set_map map_map comp_def concat_map_maps set_maps UN_iff fun_app_def Set.image_iff

lemma bex_singleton: "\<exists>x\<in>{s}.P x = P s" by simp

abbreviation "simple_fw_prefix_to_range \<equiv> prefix_to_range \<circ> split PrefixMatch"

lemma simple_match_port_alt: "simple_match_port m p \<longleftrightarrow> p \<in> wordinterval_to_set (split WordInterval m)"
by (metis old.prod.case simple_match_port.elims(2) simple_match_port.elims(3) wordinterval_to_set.simps(1))

(* TODO: move *)
definition "prefix_match_dtor m \<equiv> (case m of PrefixMatch p l \<Rightarrow> (p,l))"

(* TODO: move? *)
lemma simple_match_ip_alt: "valid_prefix (PrefixMatch (fst m) (snd m)) \<Longrightarrow> 
	simple_match_ip m p \<longleftrightarrow> prefix_match_semantics (PrefixMatch (fst m) (snd m)) p"
by(cases m) (simp add: prefix_match_if_in_my_set wordinterval_to_set_ipv4range_set_from_prefix)
lemma simple_match_src_alt: "simple_match_valid r \<Longrightarrow> 
	simple_match_ip (src r) p \<longleftrightarrow> prefix_match_semantics (PrefixMatch (fst (src r)) (snd (src r))) p"
by(cases "(src r)") (simp add: prefix_match_if_in_my_set wordinterval_to_set_ipv4range_set_from_prefix simple_match_valid_def valid_prefix_fw_def)
lemma simple_match_dst_alt: "simple_match_valid r \<Longrightarrow> 
	simple_match_ip (dst r) p \<longleftrightarrow> prefix_match_semantics (PrefixMatch (fst (dst r)) (snd (dst r))) p"
by(cases "(dst r)") (simp add: prefix_match_if_in_my_set wordinterval_to_set_ipv4range_set_from_prefix simple_match_valid_def valid_prefix_fw_def)
thm prefix_match_semantics_simple_match (* mph, I had one like that already. TODO: dedup *)


lemma "x \<in> set (wordinterval_CIDR_split_internal w) \<Longrightarrow> valid_prefix x"
using wordinterval_CIDR_split_internal_all_valid_Ball[THEN bspec] .

lemma simple_match_to_of_matchI: 
	assumes mv: "simple_match_valid r"
	assumes mm: "simple_matches r p"
	assumes ii: "p_iiface p \<in> set ifs"
	assumes ippkt: "p_l2type p = 0x800"
	shows eq: "\<exists>gr \<in> set (simple_match_to_of_match r ifs). OF_match_fields gr p = Some True"
proof -
	let ?npm = "\<lambda>p. fst p = 0 \<and> snd p = max_word"
	let ?sb = "\<lambda>p r. (if ?npm p then None else Some r)"
	obtain si where si: "case si of Some ssi \<Rightarrow> p_sport p \<in> prefix_to_ipset ssi | None \<Rightarrow> True"
		"case si of None \<Rightarrow> True | Some ssi \<Rightarrow> ssi \<in> set (
		wordinterval_CIDR_split_internal (split WordInterval (sports r)))"
		"si = None \<longleftrightarrow> ?npm (sports r)"
	proof(cases "?npm (sports r)")
		case goal1
		hence "(case None of None \<Rightarrow> True | Some ssi \<Rightarrow> p_sport p \<in> prefix_to_ipset ssi) \<and>
            (case None of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_internal (case sports r of (x, xa) \<Rightarrow> WordInterval x xa)))" by simp
        with goal1 show ?thesis by blast
	next
		case goal2
		from mm have "p_sport p \<in> wordinterval_to_set (split WordInterval (sports r))"
			by(simp only: simple_matches.simps simple_match_port_alt)
		then obtain ssi where ssi:
			"ssi \<in> set (wordinterval_CIDR_split_internal (split WordInterval (sports r)))"
			"p_sport p \<in> prefix_to_ipset ssi" 
			using wordinterval_CIDR_split_existential by fast
		hence "(case Some ssi of None \<Rightarrow> True | Some ssi \<Rightarrow> p_sport p \<in> prefix_to_ipset ssi) \<and>
            (case Some ssi of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_internal (case sports r of (x, xa) \<Rightarrow> WordInterval x xa)))" by simp
        with goal2 show ?thesis by blast
    qed				
	obtain di where di: "case di of Some ddi \<Rightarrow> p_dport p \<in> prefix_to_ipset ddi | None \<Rightarrow> True"
		"case di of None \<Rightarrow> True | Some ddi \<Rightarrow> ddi \<in> set (
		wordinterval_CIDR_split_internal (split WordInterval (dports r)))"
		"di = None \<longleftrightarrow> ?npm (dports r)"
	proof(cases "?npm (dports r)")
		case goal1
		hence "(case None of None \<Rightarrow> True | Some ssi \<Rightarrow> p_dport p \<in> prefix_to_ipset ssi) \<and>
            (case None of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_internal (case dports r of (x, xa) \<Rightarrow> WordInterval x xa)))" by simp
        with goal1 show ?thesis by blast
	next
		case goal2
		from mm have "p_dport p \<in> wordinterval_to_set (split WordInterval (dports r))"
			by(simp only: simple_matches.simps simple_match_port_alt)
		then obtain ddi where ddi:
			"ddi \<in> set (wordinterval_CIDR_split_internal (split WordInterval (dports r)))"
			"p_dport p \<in> prefix_to_ipset ddi" 
			using wordinterval_CIDR_split_existential by fast
		hence "(case Some ddi of None \<Rightarrow> True | Some ssi \<Rightarrow> p_dport p \<in> prefix_to_ipset ssi) \<and>
            (case Some ddi of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_internal (case dports r of (x, xa) \<Rightarrow> WordInterval x xa)))" by simp
        with goal2 show ?thesis by blast
    qed
    show ?thesis
	proof
		let ?mf = "map_option (apsnd (wordNOT \<circ> mask \<circ> op - 16) \<circ> prefix_match_dtor)"
		let ?foo = "simple_match_to_of_match_single r
			(if iiface r = ifaceAny then None else Some (p_iiface p)) 
			(if proto r = ProtoAny then ProtoAny else Proto (p_proto p))
			(?mf si) (?mf di)"
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
			proof(rule, rule, rule, rule, rule refl, rule, defer_tac, rule, rule refl, rule refl, goal_cases)
				case 1 thus ?case using ple(2) sdpe(2) di
					apply(simp add: pfxm_mask_def prefix_match_dtor_def split: option.splits prod.splits)
					apply(subst Set.image_iff)
					apply(erule bexI[rotated])
					apply(simp split: prefix_match.splits)
				done
			next
				case 2 thus ?case using ple(1) sdpe(1) si
					apply(simp add: pfxm_mask_def prefix_match_dtor_def split: option.splits prod.splits)
					apply(subst Set.image_iff)
					apply(erule bexI[rotated])
					apply(simp split: prefix_match.splits)
				done
			next
				case 3 thus ?case
					apply(simp only: set_filter_nones list.map set_simps singleton_iff simple_proto_conjunct_asimp  split: if_splits)
					apply(rule)
					 apply(rule)
					  apply(rule)
					  apply(simp;fail)
					 apply(clarsimp;fail)
					apply(rule)
					 apply(rule)
					 apply(clarsimp;fail)
					apply(rule)
					using u ii apply(simp add: set_maps split: if_splits)
				done
			next
				case 4 thus ?case using ii u by simp_all (metis match_proto.elims(2))  
			qed
		have dpm: "\<And>x1 x2. di = Some (PrefixMatch x1 x2)
             \<Longrightarrow> p_dport p && ~~ mask (16 - x2) = x1"
    using di
      apply(clarsimp split: prod.splits)
      apply(subgoal_tac "prefix_match_semantics (the di) (p_dport p)")
      apply(clarsimp simp: prefix_match_semantics_def pfxm_mask_def word_bw_comms;fail)
      apply(clarsimp)
      apply(subst prefix_match_if_in_my_set)
      apply(blast dest: wordinterval_CIDR_split_internal_all_valid_Ball[THEN bspec])
      apply(assumption)
    done
		have spm: "\<And>x1 x2. si = Some (PrefixMatch x1 x2)
             \<Longrightarrow> p_sport p && ~~ mask (16 - x2) = x1"
    using si
      apply(clarsimp split: prod.splits)
      apply(subgoal_tac "prefix_match_semantics (the si) (p_sport p)")
      apply(clarsimp simp: prefix_match_semantics_def pfxm_mask_def word_bw_comms;fail)
      apply(clarsimp)
      apply(subst prefix_match_if_in_my_set)
      apply(blast dest: wordinterval_CIDR_split_internal_all_valid_Ball[THEN bspec])
      apply(assumption)
    done
		show "OF_match_fields ?foo p = Some True"
		unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF mv eg]]
		  apply(cases si; cases di)
			apply(simp_all
					add: simple_match_to_of_match_single_def OF_match_fields_unsafe_def 
					option2set_def prefix_match_semantics_simple_match u ippkt
					comp_def prefix_match_dtor_def toprefixmatch_def 
					simple_match_dst_alt[OF mv, symmetric] simple_match_src_alt[OF mv, symmetric]
					ball_Un split: prefix_match.splits)
			using dpm spm apply presburger+
		done
	qed
qed

lemma prefix_match_00[simp,intro!]: "prefix_match_semantics (PrefixMatch 0 0) p"
  by (simp add: valid_preifx_alt_def zero_prefix_match_all)

lemma simple_match_to_of_matchD:
	assumes eg: "gr \<in> set (simple_match_to_of_match r ifs)"
	assumes mo: "OF_match_fields gr p = Some True"
	assumes me: "match_iface (oiface r) (p_oiface p)"
	assumes mv: "simple_match_valid r"
	shows "simple_matches r p"
proof -
	from mv have validpfx: 
		"valid_prefix (split PrefixMatch (src r))" "valid_prefix (split PrefixMatch (dst r))"
		"\<And>pm. toprefixmatch (src r) = Some pm \<Longrightarrow> valid_prefix pm"
		"\<And>pm. toprefixmatch (dst r) = Some pm \<Longrightarrow> valid_prefix pm"
		unfolding simple_match_valid_def valid_prefix_fw_def toprefixmatch_def by(simp_all split: prod.splits if_splits)
	from mo have mo: "OF_match_fields_unsafe gr p" 
		unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF mv eg]]
		by simp
	note this[unfolded OF_match_fields_unsafe_def]
	note eg[unfolded simple_match_to_of_match_def simple_match_to_of_match_single_def Let_def custom_simpset option2set_def]
	then guess x ..
	moreover from this(2) guess xa ..
	moreover from this(2) guess xb ..
	note xx = calculation(1,3) this
	show ?thesis unfolding simple_matches.simps
	proof(unfold and_assoc, (rule)+)
		case goal1 thus ?case 
			apply(cases "iiface r = ifaceAny") 
			 apply (simp add: match_ifaceAny) 
			using xx(1) mo unfolding xx(4) OF_match_fields_unsafe_def
			apply(simp only: if_False set_maps UN_iff)
			apply(clarify)
			apply(rename_tac a; subgoal_tac "match_iface (iiface r) a") 
			 apply(clarsimp simp add: option2set_def;fail)
			apply(rule ccontr,simp;fail)
		done
	next
		case goal2 thus ?case unfolding simple_packet_unext_def simple_packet.simps using me .
	next
		case goal3 thus ?case
			using mo unfolding xx(4) OF_match_fields_unsafe_def toprefixmatch_def
			by(clarsimp 
			  simp add: simple_packet_unext_def option2set_def validpfx simple_match_src_alt[OF mv] toprefixmatch_def 
			  split: if_splits)
	next
		case goal4 thus ?case
			using mo unfolding xx(4) OF_match_fields_unsafe_def toprefixmatch_def
			apply(clarsimp 
			  simp add: simple_packet_unext_def option2set_def validpfx simple_match_src_alt[OF mv] toprefixmatch_def 
			  split: if_splits) sorry
 	next
		case goal5 thus ?case
			using mo unfolding xx(4) OF_match_fields_unsafe_def
			using xx(1) by(clarsimp 
				simp add: singleton_iff simple_packet_unext_def option2set_def prefix_match_semantics_simple_match ball_Un 
				split: if_splits protocol.splits)
	next
		case goal6 thus ?case
			using mo xx(2) unfolding xx(4) OF_match_fields_unsafe_def
			apply(cases "sports r")
			apply(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
			apply(rename_tac xc)
			apply(subgoal_tac "prefix_match_semantics xc (p_sport p)")
			prefer 2
			apply(simp add: prefix_match_semantics_def word_bw_comms;fail)
			apply(rename_tac a b xc)
			apply(subgoal_tac "p_sport p \<in> wordinterval_to_set (WordInterval a b)")
			apply(simp;fail)
			apply(subgoal_tac "p_sport p \<in> prefix_to_ipset xc")
			apply(subst wordinterval_CIDR_split_internal[symmetric])
			apply blast
			apply(subst(asm)(1) prefix_match_if_in_my_set)
			apply(erule wordinterval_CIDR_split_internal_all_valid_Ball[THEN bspec];fail)
			apply assumption
		done
	next
		case goal7 thus ?case using mo xx(3) unfolding xx(4) OF_match_fields_unsafe_def
			apply(cases "dports r")
			apply(clarsimp simp add: simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
			apply(rename_tac xc)
			apply(subgoal_tac "prefix_match_semantics xc (p_dport p)")
			prefer 2
			apply(simp add: prefix_match_semantics_def word_bw_comms;fail)
			apply(rename_tac a b xc)
			apply(subgoal_tac "p_dport p \<in> wordinterval_to_set (WordInterval a b)")
			apply(simp;fail)
			apply(subgoal_tac "p_dport p \<in> prefix_to_ipset xc")
			apply(subst wordinterval_CIDR_split_internal[symmetric])
			apply blast
			apply(subst(asm)(1) prefix_match_if_in_my_set)
			apply(erule wordinterval_CIDR_split_internal_all_valid_Ball[THEN bspec];fail)
			apply assumption
		done
    qed
qed

primrec annotate_rlen where
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

primrec annotate_rlen_code where
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

lemma map_annotate_rlen[simp]: "annotate_rlen (map f x) = map (apsnd f) (annotate_rlen x)"
by(induction x) simp_all

text{*l3 device to l2 forwarding*}
definition "fourtytwo_s3 ifs ard = (
	[(p, b, case a of simple_action.Accept \<Rightarrow> [Forward c] | simple_action.Drop \<Rightarrow> []).
		(p,r,(c,a)) \<leftarrow> ard, b \<leftarrow> simple_match_to_of_match r ifs])"

definition "oif_ne_iif_p1 ifs \<equiv> [(simple_match_any\<lparr>oiface := Iface oi, iiface := Iface ii\<rparr>, simple_action.Accept). oi \<leftarrow> ifs, ii \<leftarrow> ifs, oi \<noteq> ii]"
definition "oif_ne_iif_p2 ifs = [(simple_match_any\<lparr>oiface := Iface i, iiface := Iface i\<rparr>, simple_action.Drop). i \<leftarrow> ifs]"
definition "oif_ne_iif ifs = oif_ne_iif_p2 ifs @ oif_ne_iif_p1 ifs" (* order irrelephant *)
(*value "oif_ne_iif [''a'', ''b'']"*)
(* I first tried something like "oif_ne_iif ifs \<equiv> [(simple_match_any\<lparr>oiface := Iface oi, iiface := Iface ii\<rparr>, if oi = ii then simple_action.Drop else simple_action.Accept). oi \<leftarrow> ifs, ii \<leftarrow> ifs]", 
   but making the statement I wanted with that was really tricky. Much easier to have the second element constant and do it separately. *)
definition "fourtytwo_s4 ard ifs \<equiv> generalized_fw_join ard (oif_ne_iif ifs)"

definition "fourtytwo_s1 rt = [(route2match r, output_iface (routing_action r)). r \<leftarrow> rt]"
definition "fourtytwo_s2 mrt fw = generalized_fw_join mrt (map simple_rule_dtor fw)"
definition "fourtytwo_nullifyoif = map (apfst (oiface_update (const ifaceAny)))"

definition "fourtytwo_fbs rt fw ifs \<equiv> let
	gfw = map simple_rule_dtor fw; (* generalized simple fw, hopefully for FORWARD *)
	frt = fourtytwo_s1 rt; (* rt as fw *)
	prd = generalized_fw_join frt gfw
	in prd
"

definition "pack_OF_entries ifs ard \<equiv> (map (split3 OFEntry) $ fourtytwo_s3 ifs ard)"

definition "fourtytwo rt fw ifs \<equiv> let
	nrd = fourtytwo_fbs rt fw ifs;
	ard = map (apfst word_of_nat) (annotate_rlen nrd) (* give them a priority *)
	in
	if length nrd < unat (max_word :: 16 word)
	then Inr $ pack_OF_entries ifs ard
	else Inl $ ''Error in creating OpenFlow table: priority number space exhausted''
"

lemma fourtytwo_nullifyoif_alt: "fourtytwo_nullifyoif frd = [(m\<lparr>oiface := ifaceAny\<rparr>,d). (m,d) \<leftarrow> frd]"
proof -
	have h: "(\<lambda>(m, a). [((m\<lparr>oiface := ifaceAny\<rparr>), a)]) = (\<lambda>t. [(case t of (m,a) \<Rightarrow> (m\<lparr>oiface := ifaceAny\<rparr>, a))])"
		unfolding prod.case_distrib by fast
	show ?thesis
		unfolding fourtytwo_nullifyoif_def apfst_def const_def map_prod_def
		unfolding h
		unfolding concat_map_singleton
		by(clarsimp split: simple_rule.splits)
qed

find_theorems List.product (* I wonder if we could also write fourtytwo as rt \<times> fw \<times> ifs. Using the join should be easier though. *)

lemma ipv4cidr_conjunct_any: "ipv4cidr_conjunct (0, 0) (0, 0) \<noteq> None" by(eval)

lemma oif_ne_iif_alt: 
"oif_ne_iif ifs = map (apsnd (\<lambda>(a,b). if a = b then simple_action.Drop else simple_action.Accept)) (generalized_fw_join (map (\<lambda>i. (simple_match_any\<lparr>oiface := Iface i\<rparr>, i)) ifs) (map (\<lambda>i. (simple_match_any\<lparr>iiface := Iface i\<rparr>, i)) ifs))"
unfolding oif_ne_iif_def generalized_fw_join_def option2list_def
oops

(* TODO: move *)
lemma generalized_sfw_filterD: "generalized_sfw (filter f fw) p = Some (r,d) \<Longrightarrow> simple_matches r p \<and> f (r,d)"
by(induction fw) (simp_all add: generalized_sfw_simps split: if_splits)
lemma generalized_sfwD: "generalized_sfw fw p = Some (r,d) \<Longrightarrow> (r,d) \<in> set fw \<and> simple_matches r p"
unfolding generalized_sfw_def using find_SomeD(1) find_SomeD(2) by fastforce

definition "is_iface_name i \<equiv> i \<noteq> [] \<and> \<not>Iface.iface_name_is_wildcard i"
definition "is_iface_list ifs \<equiv> distinct ifs \<and> list_all is_iface_name ifs"

lemma simple_rule_and_iiface_update: "is_iface_name a1 \<Longrightarrow> match_iface (Iface a1) a \<longleftrightarrow> a = a1"
	apply(rule iffI)
	 apply(clarsimp simp: is_iface_name_def match_iface.simps  split: bool.splits option.splits if_splits)
	 apply(induction a1 a rule: internal_iface_name_match.induct)
	    apply(simp_all add: iface_name_is_wildcard.simps split: if_splits)
	 apply(metis iface_name_is_wildcard.simps(3) internal_iface_name_match.elims(2) list.discI)
	apply(simp add: match_iface_refl)
done

(* TODO: move *)
lemma generalized_sfw_NoneD: "generalized_sfw fw p = None \<Longrightarrow> \<forall>(a,b) \<in> set fw. \<not>simple_matches a p"
	by(induction fw) (clarsimp simp add: generalized_sfw_simps split: if_splits)+

lemma max_16_word_max[simp]: "(a :: 16 word) \<le> 0xffff"
proof -
	have ffff: "0xffff = word_of_int (2 ^ 16 - 1)" by fastforce
	show ?thesis using max_word_max[of a] unfolding max_word_def ffff by fastforce
qed

lemma simple_matches_ioiface: "
is_iface_name xa \<Longrightarrow>
is_iface_name xb \<Longrightarrow>
simple_matches (simple_match_any\<lparr>oiface := Iface xb, iiface := Iface xa\<rparr>) p \<longleftrightarrow> (p_oiface p = xb \<and> p_iiface p = xa)"
by(auto simp: simple_matches.simps simple_match_any_def ipv4range_set_from_prefix_UNIV simple_rule_and_iiface_update)

lemma image_iff_forealyo: "(y \<in> f ` S) \<longleftrightarrow> (\<exists>x \<in> S. y = f x)" by blast

lemma oif_ne_iif_alt: "oif_ne_iif ifs =	map (\<lambda>(oi,ii). (simple_match_any\<lparr>oiface := Iface oi, iiface := Iface ii\<rparr>, if oi = ii then simple_action.Drop else simple_action.Accept)) (List.product ifs ifs)"
oops

lemma oif_ne_iif_p1_correct: "is_iface_list ifs \<Longrightarrow> generalized_sfw (oif_ne_iif_p1 ifs) p \<noteq> None \<longleftrightarrow> (p_oiface p \<noteq> p_iiface p \<and> p_oiface p \<in> set ifs \<and> p_iiface p \<in> set ifs)"
proof(rule iffI, defer_tac, rule ccontr, unfold not_not)
	case goal2
	then obtain m d where "generalized_sfw (oif_ne_iif_p1 ifs) p = Some (m,d)" by fast
	note m = generalized_sfwD[OF this]
	then obtain oif iif where ifs[simp]: "oif \<noteq> iif" "oif \<in> set ifs" "iif \<in> set ifs" "m = simple_match_any\<lparr>oiface := Iface oif, iiface := Iface iif\<rparr>" unfolding oif_ne_iif_p1_def by auto
	hence ifn: "is_iface_name iif" "is_iface_name oif" using goal2 by(simp_all add: is_iface_list_def list_all_iff)
	show ?case using m unfolding ifs unfolding simple_matches_ioiface[OF ifn] by simp
next
	case goal1
	hence ifn: "is_iface_name (p_iiface p)" "is_iface_name (p_oiface p)" by(simp_all add: is_iface_list_def list_all_iff)
	note goal1(3)[THEN generalized_sfw_NoneD]
	hence "\<not> simple_matches (simple_match_any\<lparr>oiface := Iface (p_oiface p), iiface := Iface (p_iiface p)\<rparr>) p" 
		unfolding oif_ne_iif_p1_def using goal1(2) by fastforce
	thus False unfolding simple_matches_ioiface[OF ifn] by simp
qed
lemma oif_ne_iif_p2_correct: "is_iface_list ifs \<Longrightarrow> generalized_sfw (oif_ne_iif_p2 ifs) p \<noteq> None \<longleftrightarrow> (p_oiface p = p_iiface p \<and> p_oiface p \<in> set ifs \<and> p_iiface p \<in> set ifs)"
	unfolding oif_ne_iif_p2_def
	apply(induction ifs)
	 apply(clarsimp simp add: generalized_sfw_simps is_iface_list_def)+
using simple_matches_ioiface by auto

lemma  oif_ne_iif_p12_snd:
	"generalized_sfw (oif_ne_iif_p1 ifs) p = Some (r,e) \<Longrightarrow> e \<noteq> simple_action.Drop"
	"generalized_sfw (oif_ne_iif_p2 ifs) p = Some (r,e) \<Longrightarrow> e = simple_action.Drop"
	unfolding oif_ne_iif_p2_def oif_ne_iif_p1_def
	by(drule generalized_sfwD; clarsimp)+

lemma oif_ne_iif_correct: "is_iface_list ifs \<Longrightarrow> (\<exists>r. generalized_sfw (oif_ne_iif ifs) p = Some (r, ad)) \<longleftrightarrow> ((p_oiface p = p_iiface p \<longleftrightarrow> ad = simple_action.Drop) \<and> p_oiface p \<in> set ifs \<and> p_iiface p \<in> set ifs)"
	unfolding oif_ne_iif_def
	unfolding generalized_sfw_append
	apply(rule iffI; split option.splits; clarify)
	  apply(simp_all only: oif_ne_iif_p12_snd)
	  using oif_ne_iif_p1_correct apply blast
	 using oif_ne_iif_p2_correct apply blast
	apply(simp)
	apply(rule conjI;clarsimp)
	 apply(subgoal_tac "p_oiface p \<noteq> p_iiface p")
	  apply(drule oif_ne_iif_p1_correct[of _ p, THEN iffD2])
	   apply blast
	  apply(clarsimp)
	  apply(drule oif_ne_iif_p12_snd)
	  apply(metis simple_action.exhaust)
	 using oif_ne_iif_p2_correct apply blast
	apply(frule oif_ne_iif_p12_snd)
	using oif_ne_iif_p2_correct apply blast
done

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


lemma replicate_FT_hlp: "x \<le> 16 \<and> y \<le> 16 \<Longrightarrow> replicate (16 - x) False @ replicate x True = replicate (16 - y) False @ replicate y True \<Longrightarrow> x = y"
proof -
	let ?ns = "{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}"
	assume "x \<le> 16 \<and> y \<le> 16"
	hence "x \<in> ?ns" "y \<in> ?ns" by(simp; presburger)+
	moreover assume "replicate (16 - x) False @ replicate x True = replicate (16 - y) False @ replicate y True"
	ultimately show "x = y" by simp (elim disjE; simp_all) (* that's only 289 subgoals after the elim *)
qed

lemma mask_inj_hlp1: "inj_on (mask :: nat \<Rightarrow> 16 word) {0..16}"
proof(intro inj_onI)
       case goal1
       from goal1(3)
       have oe: "of_bl (replicate (16 - x) False @ replicate x True) = (of_bl (replicate (16 - y) False @ replicate y True) :: 16 word)"
               unfolding mask_bl of_bl_rep_False .
       have "\<And>z. z \<le> 16 \<Longrightarrow> length (replicate (16 - z) False @ replicate z True) = 16" by auto
       with goal1(1,2)
       have ps: "replicate (16 - x) False @ replicate x True \<in> {bl. length bl = len_of TYPE(16)}" " replicate (16 - y) False @ replicate y True \<in> {bl. length bl = len_of TYPE(16)}" by simp_all
       from inj_onD[OF word_bl.Abs_inj_on, OF oe ps]
       show ?case apply - apply(rule replicate_FT_hlp) using  goal1(1,2) apply simp apply blast done 
qed

lemma distinct_simple_match_to_of_match: "distinct ifs \<Longrightarrow> distinct (simple_match_to_of_match m ifs)"
apply(unfold simple_match_to_of_match_def Let_def)
apply(rule distinct_3lcomprI)
apply(clarsimp)
apply(induction ifs)
apply(simp;fail)
apply(simp;fail)
apply(simp_all add: distinct_word_upto smtoms_eq_hlp)
apply(unfold distinct_map)
apply(clarify)
apply(intro conjI wordinterval_CIDR_split_internal_distinct)
apply(subst comp_inj_on_iff[symmetric])
prefer 2
apply force
apply(intro inj_onI)
apply(case_tac x; case_tac y)
apply(clarsimp simp: pfxm_mask_def)
apply(drule wordinterval_CIDR_split_internal_all_valid_less_Ball[unfolded Ball_def, THEN spec, THEN mp])+
apply(subgoal_tac "16 - x2 = 16 - x2a")
apply(simp;fail)
apply(rule mask_inj_hlp1[THEN inj_onD])
apply(simp;fail)+
apply(clarify)
apply(intro conjI wordinterval_CIDR_split_internal_distinct)
apply(subst comp_inj_on_iff[symmetric])
prefer 2
apply force
apply(intro inj_onI)
apply(case_tac x; case_tac y)
apply(clarsimp simp: pfxm_mask_def)
apply(drule wordinterval_CIDR_split_internal_all_valid_less_Ball[unfolded Ball_def, THEN spec, THEN mp])+
apply(subgoal_tac "16 - x2 = 16 - x2a")
apply(simp;fail)
apply(rule mask_inj_hlp1[THEN inj_onD])
apply(simp;fail)+
done

lemma no_overlaps_42_hlp2: "distinct (map fst amr) \<Longrightarrow> (\<And>r. distinct (fm r)) \<Longrightarrow>
    distinct (concat (map (\<lambda>(p, r, c, a). map (\<lambda>b. (p, b, fs a c)) (fm r)) amr))"
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

(* TODO: move *)
lemma cidrsplitelems: "\<lbrakk>
        x \<in> set (wordinterval_CIDR_split_internal wi);
        xa \<in> set (wordinterval_CIDR_split_internal wi); 
        pt && ~~ pfxm_mask x = pfxm_prefix x;
        pt && ~~ pfxm_mask xa = pfxm_prefix xa
        \<rbrakk>
       \<Longrightarrow> x = xa"
proof(rule ccontr)
	case goal1
	hence "prefix_match_semantics x pt" "prefix_match_semantics xa pt" unfolding prefix_match_semantics_def by (simp_all add: word_bw_comms(1))
	moreover have "valid_prefix x" "valid_prefix xa" using goal1(1-2) wordinterval_CIDR_split_internal_all_valid_Ball by blast+
	ultimately have "pt \<in> prefix_to_ipset x" "pt \<in> prefix_to_ipset xa" using pfx_match_addr_ipset by blast+
	with CIDR_splits_disjunct[OF goal1(1,2) goal1(5)] show False by blast
qed

lemma distinct_42_s3: "\<lbrakk>distinct (map fst amr); distinct ifs\<rbrakk> \<Longrightarrow> distinct (fourtytwo_s3 ifs amr)"
unfolding fourtytwo_s3_def
by(erule no_overlaps_42_hlp2, simp add: distinct_simple_match_to_of_match)

lemma no_overlaps_42_hlp3: "distinct (map fst amr) \<Longrightarrow>
(aa, ab, ac) \<in> set (fourtytwo_s3 ifs amr) \<Longrightarrow> (ba, bb, bc) \<in> set (fourtytwo_s3 ifs amr) \<Longrightarrow>
ac \<noteq> bc \<Longrightarrow> aa \<noteq> ba"
apply(unfold fourtytwo_s3_def)
apply(clarsimp)
apply(clarsimp split: simple_action.splits)
apply(metis map_of_eq_Some_iff old.prod.inject option.inject)
apply(metis map_of_eq_Some_iff old.prod.inject option.inject simple_action.distinct(2))+
done

lemma no_overlaps_42_s3_hlp: "distinct (map fst amr) \<Longrightarrow> distinct ifs \<Longrightarrow> 
no_overlaps OF_match_fields_unsafe (map (split3 OFEntry) (fourtytwo_s3 ifs amr))"
apply(rule no_overlapsI, defer_tac)
apply(subst distinct_map, rule conjI)
prefer 2
apply(rule inj_inj_on)
apply(rule injI)
apply(rename_tac x y, case_tac x, case_tac y)
apply(simp add: split3_def;fail)
apply(erule (1) distinct_42_s3)
apply(unfold check_no_overlap_def)
apply(clarify)
apply(unfold set_map)
apply(clarify)
apply(unfold split3_def prod.simps flow_entry_match.simps flow_entry_match.sel de_Morgan_conj)
apply(erule disjE)
apply(clarify;fail)
apply(erule disjE, defer_tac)
apply(simp add: no_overlaps_42_hlp3;fail)
apply(clarsimp simp add: fourtytwo_s3_def)
apply(rename_tac p ab ac ad a bb bc bd am bm)
apply(case_tac "ab \<noteq> bb")
apply(drule (3) no_overlaps_42_hlp4, (simp;fail)) (* This drule is not applied like you'd expect it to be. But it works. *)
apply(clarify | unfold
	simple_match_to_of_match_def smtoms_eq_hlp Let_def set_concat set_map de_Morgan_conj not_False_eq_True)+
apply(simp add: comp_def smtoms_eq_hlp add: if_splits)
apply(auto dest: conjunctSomeProtoAnyD cidrsplitelems split: protocol.splits option.splits if_splits
	simp add: comp_def  smtoms_eq_hlp OF_match_fields_unsafe_def simple_match_to_of_match_single_def option2set_def) (* another huge split, takes around 332 seconds  *)
by -

lemma if_f_distrib: "(if a then b else c) k = (if a then b k else c k)" by simp

lemma distinct_fst: "distinct (map fst a) \<Longrightarrow> distinct a" by (metis distinct_zipI1 zip_map_fst_snd)
lemma distinct_snd: "distinct (map snd a) \<Longrightarrow> distinct a" by (metis distinct_zipI2 zip_map_fst_snd)

lemma inter_empty_fst2: "(\<lambda>(p, m, a). (p, m)) ` S \<inter> (\<lambda>(p, m, a). (p, m)) ` T = {} \<Longrightarrow> S \<inter> T = {}" by blast

lemma simple_match_to_of_match_iface_any: "\<lbrakk>xa \<in> set (simple_match_to_of_match (match_sel ae) ifs); iiface (match_sel ae) = ifaceAny\<rbrakk> \<Longrightarrow> \<not>(\<exists>p. IngressPort p \<in> xa)"
by(simp add: simple_match_to_of_match_def simple_match_to_of_match_single_def option2set_def) fast

lemma simple_match_to_of_match_iface_some: "\<lbrakk>xa \<in> set (simple_match_to_of_match (match_sel ae) ifs); iiface (match_sel ae) \<noteq> ifaceAny\<rbrakk> \<Longrightarrow> \<exists>p. IngressPort p \<in> xa"
by(simp add: simple_match_to_of_match_def simple_match_to_of_match_single_def option2set_def) fast


lemma not_wildcard_Cons: "\<not> iface_name_is_wildcard (i # is) \<Longrightarrow> i = CHR ''+'' \<Longrightarrow> is \<noteq> []" using iface_name_is_wildcard.simps(2) by blast 

lemma match_iface_name: "is_iface_name (iface_sel n) \<Longrightarrow> match_iface n a \<longleftrightarrow> (iface_sel n) = a"
proof(cases n, simp add: is_iface_name_def, subst match_iface.simps) (* I hereby ignore an explicit warning not to use that function. TODO: FIX! *)
	case (goal1 x)
	show ?case using goal1(1)
	apply(induction x a rule: internal_iface_name_match.induct)
	apply(simp_all add: not_wildcard_Cons)
	apply(rule conjI)
	apply(clarsimp simp add: not_wildcard_Cons iface_name_is_wildcard.simps)
	apply(metis iface_name_is_wildcard.simps(3) internal_iface_name_match.simps(1) internal_iface_name_match.simps(3) splice.elims)
	done
qed

lemma simple_match_to_of_match_iface_specific: "\<lbrakk>xa \<in> set (simple_match_to_of_match (match_sel ae) ifs); iiface (match_sel ae) \<noteq> ifaceAny; is_iface_name (iface_sel (iiface (match_sel ae)))\<rbrakk> 
\<Longrightarrow> IngressPort (iface_sel (iiface (match_sel ae))) \<in> xa"
	apply(clarsimp simp add: simple_match_to_of_match_def simple_match_to_of_match_single_def option2set_def Let_def)
	apply(subst(asm) match_iface_name)
	 apply assumption
	apply fast
done

lemma smtoms_only_one_iport: "\<lbrakk>xa \<in> set (simple_match_to_of_match (match_sel ba) ifs); IngressPort p1 \<in> xa; IngressPort p2 \<in> xa\<rbrakk> \<Longrightarrow> p1 = p2" 
apply(clarsimp simp add: simple_match_to_of_match_def simple_match_to_of_match_single_def option2set_def Let_def)
apply(auto split: option.splits protocol.splits)
done

lemma smtoms_hlp2: "\<lbrakk>xa \<in> set (simple_match_to_of_match (match_sel ba) ifs); xa \<in> set (simple_match_to_of_match (match_sel ae) ifs); iiface (match_sel ae) \<noteq> iiface (match_sel ba);
is_iface_name (iface_sel (iiface (match_sel ae))); is_iface_name (iface_sel (iiface (match_sel ba)))\<rbrakk> \<Longrightarrow> False"
apply(cases "iiface (match_sel ae) = ifaceAny"; cases "iiface (match_sel ba) = ifaceAny")
apply(simp_all)
apply((drule (1) simple_match_to_of_match_iface_any[rotated] | drule (1) simple_match_to_of_match_iface_some[rotated])+; (clarsimp;fail))+
apply(drule (2) simple_match_to_of_match_iface_specific[rotated])
apply(drule (2) simple_match_to_of_match_iface_specific[rotated])
apply(drule (2) smtoms_only_one_iport[rotated])
apply(simp add: iface.expand)
done

 
lemma simple_rule_and_iiface_update: "is_iface_name a1 \<Longrightarrow> simple_rule_and (simple_match_any\<lparr>iiface := Iface a1\<rparr>) a = Some r1 \<Longrightarrow> iface_sel (iiface (match_sel r1)) = a1" 
	apply(cases a)
	apply(rename_tac abm aba)
	apply(case_tac abm)
	apply(rename_tac iiface oiface src dst proto sports dports)
	apply(clarsimp simp add: simple_match_any_def simple_rule_and_def split: option.splits)
	apply(case_tac iiface)
	apply(clarsimp simp: is_iface_name_def split: bool.splits option.splits if_splits)
oops
(* Todo: Move to Iface? I'd rather not\<dots> *)
lemma no_overlaps_42_s4_hlp1: "\<lbrakk>Some r1 = simple_rule_and (simple_match_any\<lparr>iiface := Iface a1\<rparr>) a; Some r2 = simple_rule_and (simple_match_any\<lparr>iiface := Iface a2\<rparr>) a;
	a1 \<noteq> a2; is_iface_name a1; is_iface_name a2\<rbrakk> \<Longrightarrow> iiface (match_sel r1) \<noteq> iiface (match_sel r2)"
using simple_rule_and_iiface_update oops

lemma hlp1: "\<lbrakk>Some r1 = x1; Some r2 = x2; x2 = x1; r1 \<noteq> r2\<rbrakk> \<Longrightarrow> False" by auto

lemma disjointI: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> A \<inter> B = {}" by auto

lemma distinct_restr: "distinct (map (\<lambda>(a,b,c). (a,b)) l) = distinct (map fst (map (\<lambda>(a,b,c). ((a,b),c)) l))"
by(simp add: comp_def prod.case_distrib)
lemma distinct_fst_force_snd: "distinct (map fst l) \<Longrightarrow> (a,b) \<in> set l \<Longrightarrow> (a,c) \<in> set l \<Longrightarrow> b = c" using map_of_is_SomeI by fastforce
lemma distinct_fstsnd_force_trd: "distinct (map (\<lambda>(a,b,c). (a,b)) l) \<Longrightarrow> (a,b,c) \<in> set l \<Longrightarrow> (a,b,d) \<in> set l \<Longrightarrow> c = d"
	apply(rule distinct_fst_force_snd)
	  apply(force elim: distinct_restr[THEN iffD1])+
done

lemma x_comp_fst_comp_apsnd[simp]: "x \<circ> fst \<circ> apsnd f = x \<circ> fst" unfolding comp_def by simp

lemma fourtytwo_no_overlaps: assumes "is_iface_list ifs" shows "Inr t = (fourtytwo rt fw ifs) \<Longrightarrow> no_overlaps OF_match_fields_unsafe t"
	apply(unfold fourtytwo_def Let_def pack_OF_entries_def)
	apply(simp split: if_splits)
	apply(thin_tac "t = _")
	apply(drule distinct_of_prio_hlp)
	apply(rule no_overlaps_42_s3_hlp[rotated])
	apply(simp add: assms[unfolded is_iface_list_def];fail)
	apply(simp add: o_assoc;fail)
done

lemma sorted_const: "sorted (map (\<lambda>y. x) k)" (* TODO: move *)
	by(induction k) (simp_all add: sorted_Cons)

lemma sorted_fourtytwo_s3_hlp: "\<forall>x\<in>set f. fst x \<le> a \<Longrightarrow> b \<in> set (fourtytwo_s3 s f) \<Longrightarrow> fst b \<le> a" 
	by(auto simp add: fourtytwo_s3_def)

lemma sorted_fourtytwo_s3: "sorted_descending (map fst f) \<Longrightarrow> sorted_descending (map fst (fourtytwo_s3 s f))"
	apply(induction f)
	apply(simp add: fourtytwo_s3_def; fail)
	apply(clarsimp)
	apply(subst fourtytwo_s3_def)
	apply(clarsimp)
	apply(subst fourtytwo_s3_def[symmetric])
	apply(unfold map_concat map_map comp_def)
	apply(unfold sorted_descending_append)
	apply(simp add: sorted_descending_alt rev_map sorted_const sorted_fourtytwo_s3_hlp)
done

lemma singleton_sorted: "set x \<subseteq> {a} \<Longrightarrow> sorted x"
by(induction x; simp) (clarsimp simp add: sorted_Cons Ball_def; blast)

lemma sorted_fourtytwo_hlp: "(ofe_prio \<circ> split3 OFEntry) = fst" by(simp add: fun_eq_iff comp_def split3_def)

lemma fourtytwo_sorted_descending: "Inr r = fourtytwo rt fw ifs \<Longrightarrow> sorted_descending (map ofe_prio r)"
	apply(unfold fourtytwo_def Let_def)
	apply(simp split: if_splits)
	apply(thin_tac "r = _")
	apply(unfold sorted_fourtytwo_hlp pack_OF_entries_def split3_def[abs_def] fun_app_def map_map comp_def prod.case_distrib)
	apply(simp add: fst_def[symmetric])
	apply(rule sorted_fourtytwo_s3)
	apply(drule sorted_annotated[OF less_or_eq_imp_le, OF disjI1])
	apply(simp add: o_assoc)
done

lemma find_map: "find g (map f a) = map_option f (find (g \<circ> f) a)"
by(induction a) simp_all

lemma fourtytwo_s1_split: "fourtytwo_s1 (a # rt) = (route2match a, output_iface (routing_action a)) # fourtytwo_s1 rt"
	by(unfold fourtytwo_s1_def list.map, rule)
lemma fourtytwo_s1_append: "fourtytwo_s1 (a @ rt) = fourtytwo_s1 a @ fourtytwo_s1 rt"
	by(induction a) (simp_all add: fourtytwo_s1_split fourtytwo_s1_def)
lemma fourtytwo_s2_split: "fourtytwo_s2 (a # rt) fw = generalized_fw_join [a] (map simple_rule_dtor fw) @ fourtytwo_s2 rt fw"
	unfolding fourtytwo_s2_def generalized_fw_join_def by simp
lemma fourtytwo_s2_split_append: "fourtytwo_s2 (a @ rt) fw = fourtytwo_s2 a fw @ fourtytwo_s2 rt fw"
	apply(induction a)
	 apply(simp add: fourtytwo_s2_def)
	apply(simp add: fourtytwo_s2_split)
done

term "p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>"

lemma route2match_correct: "valid_prefix (routing_match a) \<Longrightarrow> prefix_match_semantics (routing_match a) (p_dst p) \<longleftrightarrow> simple_matches (route2match a) (p)"
by(simp add: route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipv4range_set_from_prefix_UNIV prefix_match_if_in_corny_set2)

lemma route2match_correct_noupd: "valid_prefix (routing_match a) \<Longrightarrow> simple_matches (route2match a) p \<Longrightarrow> prefix_match_semantics (routing_match a) (p_dst p)"
by(simp add: route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipv4range_set_from_prefix_UNIV prefix_match_if_in_corny_set2)

lemma s1_correct: "valid_prefixes rt \<Longrightarrow> has_default_route rt \<Longrightarrow> \<exists>rm ra. generalized_sfw (fourtytwo_s1 rt) p = Some (rm,ra) \<and> ra = output_iface (routing_table_semantics rt (p_dst p))"
	apply(induction rt)
	 apply(simp;fail)
	apply(drule valid_prefixes_split)
	apply(clarsimp)
	apply(erule disjE)
	 apply(rename_tac a rt)
	 apply(case_tac a)
	 apply(rename_tac routing_m metric routing_action)
	 apply(case_tac routing_m)
	 apply(simp add: valid_prefix_def pfxm_mask_def mask_32_max_word prefix_match_semantics_def generalized_sfw_def fourtytwo_s1_def route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipv4range_set_from_prefix_UNIV;fail)
	apply(rule conjI)
	 apply(simp add: generalized_sfw_def fourtytwo_s1_def route2match_correct;fail)
	apply(clarsimp)
	apply(rename_tac rm)
	apply(rule_tac x = rm in exI)
	apply(unfold fourtytwo_s1_split generalized_sfw_simps)
	apply(clarify)
	apply(split if_splits)
	apply(rule conjI[rotated])
	 apply(simp add: fourtytwo_s1_split generalized_sfw_simps;fail)
	apply(simp add: route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipv4range_set_from_prefix_UNIV prefix_match_if_in_corny_set2)
done

lemma find_split: "find f l = Some r \<Longrightarrow> \<exists>a b. l = (a @ r # b) \<and> find f a = None"
apply(induction l)
apply(simp)
apply(clarsimp split: if_splits)
apply(fastforce)
apply(rename_tac a aa b)
apply(rule_tac x = "a # aa" in exI)
apply(simp)
done

lemma simple_fw_undecided: "simple_fw fw p = Undecided \<longleftrightarrow> (\<forall>r \<in> set fw. \<not>simple_matches (match_sel r) p)"
by(induction rule: simple_fw.induct) (simp_all split: if_splits)

lemma "simple_fw fw p = Undecided \<Longrightarrow> generalized_sfw ((fourtytwo_s2 mrt fw)) p = None"
	apply(induction mrt)
	apply(simp add: fourtytwo_s2_def generalized_sfw_def)
	apply(simp add: generalized_sfw_append fourtytwo_s2_split)
	apply(split option.splits; intro conjI)
	apply(simp;fail)
	apply(thin_tac "generalized_sfw _ _ = None")
	apply(induction fw)
	apply(simp add: generalized_sfw_def;fail)
	apply(clarsimp simp: simple_fw_undecided generalized_sfw_def simple_rule_and_def simple_match_and_SomeD  split: option.splits)
	unfolding generalized_fw_join_1_1 oops

(* TODO: Move with simple_match_and_SomeD *)
lemma simple_match_and_NoneD: "simple_match_and m1 m2 = None \<Longrightarrow> \<not>(simple_matches m1 p \<and> simple_matches m2 p)"
	by(simp add: simple_match_and_correct)

lemma s1_none_s2: "generalized_sfw rt p = None \<Longrightarrow> generalized_sfw ((fourtytwo_s2 rt fw)) p = None"
unfolding fourtytwo_s2_def by(rule generalized_sfw_1_join_None)

(* TODO: move? *)
lemma simple_fw_msplit: "simple_fw fw p \<noteq> Undecided \<Longrightarrow> \<exists>a r b. fw = a @ r # b \<and> simple_fw a p = Undecided \<and> simple_matches (match_sel r) p" 
proof(induction fw)
	case (Cons a fw)
	thus ?case proof(cases "simple_matches (match_sel a) p")
		case False
		with Cons.prems have "simple_fw fw p \<noteq> Undecided" by (simp add: simple_fw_alt)
		note Cons.IH[OF this]
		then guess as ..
		then guess r ..
		then guess bs ..
		note mIH = this
		show ?thesis proof(intro exI)
			show "a # fw = (a # as) @ r # bs \<and> simple_fw (a # as) p = Undecided \<and> simple_matches (match_sel r) p" using mIH False by(simp add: simple_fw_alt)
		qed
	qed fastforce (* alternate:
	apply(rule_tac x = Nil in exI)
	apply(rule_tac x = a in exI)
	apply(rule_tac x = fw in exI)
	apply(simp)*)
qed simp

(* TODO: move *)
lemma simple_matches_andD: "simple_matches m1 p \<Longrightarrow> simple_matches m2 p \<Longrightarrow> \<exists>m. simple_match_and m1 m2 = Some m \<and> simple_matches m p"
by (meson option.exhaust_sel simple_match_and_NoneD simple_match_and_SomeD)

lemma findNoneI: "\<forall>x. x \<in> set l \<longrightarrow> \<not>f x \<Longrightarrow> find f l = None"
by (metis findSomeD not_None_eq)
(* TODO: move *)
lemma  generalized_sfw_join_1_single: "generalized_sfw (generalized_fw_join [(mr, ma)] fw) p = (if simple_matches mr p then (case generalized_sfw fw p of Some (mr2,ma2) \<Rightarrow> Some (the (simple_match_and mr mr2), ma, ma2) | None \<Rightarrow> None) else None)"
	apply(clarsimp split: option.splits if_splits)
	apply(intro conjI;clarify)
	apply(clarsimp simp add: generalized_sfw_def list_lib_find)
	apply(drule findNoneD)
	apply(rule findNoneI)
	apply(clarsimp simp: option2set_def generalized_fw_join_cons_1 split: option.splits)
	apply(meson case_prodI simple_match_and_SomeD; fail)
	apply(intro conjI[rotated]; clarify)
	apply (simp add: generalized_fw_join_1_nomatch generalized_fw_join_cons_1;fail)
	apply(induction fw)
	apply(clarsimp simp add: generalized_sfw_simps; fail)
	apply(rename_tac fwa fws x1 x2)
	apply(case_tac "fwa")
	apply(rename_tac fwam fwad)
	apply(case_tac "simple_matches fwam p")
	prefer 2
	apply(clarsimp)
	apply(subst generalized_fw_join_2_nomatch[where as = "[(mr, ma)]"], assumption)
	apply(simp add: generalized_sfw_simps; fail)
	apply(clarsimp simp: generalized_sfw_simps)
	apply(drule (1) simple_matches_andD[of mr p])
	apply(clarsimp simp add: generalized_sfw_append generalized_sfw_simps generalized_fw_join_cons_1 option2list_def)
done

find_theorems "generalized_fw_join _ (_#_)"

(*lemma "simple_fw fw p = x \<longleftrightarrow> generalized_sfw (map simple_rule_dtor fw) p = (case x of Undecided \<Rightarrow> None | Decision x1 \<Rightarrow> (undefined, inv simple_action_to_state x))"*)
(* TODO: write in the Generalized_SFW: We could have generalized away the fact that those are simple_matches, use a locale, assume an option monadic conjunction operator and then have this be an interpretation.
 but *effort *)

lemma s2_correct: "simple_fw fw p \<noteq> Undecided \<Longrightarrow> generalized_sfw rt p = Some (mr,ma) \<Longrightarrow> \<exists>mmr mfd. generalized_sfw ((fourtytwo_s2 rt fw)) p = Some (mmr, (ma, mfd)) \<and> simple_action_to_state mfd = simple_fw fw p"
proof -
	assume ras: "generalized_sfw rt p = Some (mr, ma)"
	note this[THEN generalized_fw_split]
	then guess ra ..
	then guess rb ..
	note rts = this
	note as2 = s1_none_s2[OF rts[THEN conjunct2]]
	from ras have smmr: "simple_matches mr p" unfolding generalized_sfw_def list_lib_find using findSomeD by fast
	assume fas: "simple_fw fw p \<noteq> Undecided"
	note this[THEN simple_fw_msplit]
	then guess fa ..
	then guess fr ..
	then guess fb ..
	note fws = this
	obtain cr where [simp]: "simple_match_and mr (match_sel fr) = Some cr" "simple_matches cr p" unfolding simple_rule_and_def 
		using fws[THEN conjunct2, THEN conjunct2] smmr simple_matches_andD by force
	have l: "generalized_sfw (map simple_rule_dtor fw) p = Some (match_sel fr, action_sel fr)" 
		unfolding fws[THEN conjunct1]
		using fws[THEN conjunct2, THEN conjunct1]
		apply(induction fa)
		using fws apply(clarsimp simp add: generalized_sfw_simps simple_rule_dtor_def split: prod.splits simple_rule.splits)
		apply(unfold append_Cons) (* gotta tread a bit carefully here, to make the first splits those that are actually the ones we need in the induction (thus a # (_)) *)
		apply(unfold list.map generalized_sfw_simps simple_rule_dtor_def)
		apply(split prod.splits)
		apply(split if_splits)
		apply(clarify)
		apply(intro conjI)
		 apply(clarsimp simp: simple_fw_alt split: simple_rule.splits simple_action.splits)+
	done
	show ?thesis proof(rule_tac x = cr in exI, rule_tac x = "action_sel fr" in exI)
		show "generalized_sfw ((fourtytwo_s2 rt fw)) p = Some (cr, ma, (action_sel fr)) \<and> simple_action_to_state (action_sel fr) = simple_fw fw p "
		unfolding rts[THEN conjunct1] fourtytwo_s2_split_append fourtytwo_s2_split  as2 option.simps generalized_sfw_append generalized_sfw_join_1_single
		unfolding \<open>simple_matches mr p\<close>[THEN if_P] l option.simps prod.simps
		using l simple_fw_iff_generalized_fw by force
	qed
qed

(*
"simple_fw fw p \<noteq> Undecided \<Longrightarrow> s1_sema rt p = Some (mr,ma) \<Longrightarrow> \<exists>mmr. s2_sema ((fourtytwo_s2 rt fw)) p = Some (mmr, ma)"
"valid_prefixes rt \<Longrightarrow> has_default_route rt \<Longrightarrow> \<exists>rm ra. s1_sema (fourtytwo_s1 rt) (p\<lparr>p_oiface := ra\<rparr>) = Some (rm,ra) \<and> ra = output_iface (routing_table_semantics rt (p_dst p))"*)
thm s1_correct s2_correct

definition "oiface_exact_match \<equiv> list_all (is_iface_name \<circ> iface_sel)"

(* Okay, here comes the crazy. We have shown so far that for packets with a correct output port, generalized_sfw 1 will make the correct decision on s1, and s2 will uphold that decision.
   However, at some point, we need to make that set go away, and the first possible point is after s1,2,4. Two ways emerge: Either, set the match to something fixed, e.g., '''', and make all packets have that value,
   or set it to ifaceAny. Both will make any packet pass the interface match, so ifaceAny is sane. Here is how we get there: We can show that if s1 has not made a decision with the correct port,
   it will not make a decision with any port. s2 will uphold not making a decision. Thus, the decision has to remain the same even when making a decision. *)
find_theorems route2match
lemma eqFalseI: "\<not>A \<Longrightarrow> A = False" by simp
lemma s1_update_ignorant: "
	valid_prefixes rt \<Longrightarrow> 
	generalized_sfw (fourtytwo_s1 rt) (p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>) = None \<Longrightarrow> generalized_sfw (fourtytwo_s1 rt) p = None"
oops (*
proof(induction rt) (* would be easier by rev_induct, but I lack a little lemma, so this will do. *)
	case (Cons a as)
	have vpfxa: "valid_prefix (routing_match a)" using valid_prefixes_split Cons.prems(1) by blast
	have nps: "\<not>prefix_match_semantics (routing_match a) (p_dst p)"
		using Cons.prems(2) by(simp add: fourtytwo_s1_split generalized_sfw_simps route2match_correct[OF vpfxa] split: if_splits)
	have nsm: "\<not> simple_matches (route2match a) p"
		using nps
		apply -
		apply(erule contrapos_nn)
		apply(erule route2match_correct_noupd[rotated])
		apply(fact vpfxa)
	done
	have "routing_table_semantics (a # as) (p_dst p) = routing_table_semantics as (p_dst p)" by(simp add: nps) (* unusued *)  
	have ihm: "valid_prefixes as" "generalized_sfw (fourtytwo_s1 as) (p\<lparr>p_oiface := output_iface (routing_table_semantics as (p_dst p))\<rparr>) = None"
		using Cons.prems by(simp add: valid_prefixes_split, simp add: generalized_sfw_simps fourtytwo_s1_split nps split: if_splits)
	note Cons.IH[OF this]
	with nsm show ?case by(simp add: generalized_sfw_simps fourtytwo_s1_split) 
qed(simp add: generalized_sfw_def fourtytwo_s1_def;fail)*)

(* TODO: move *)
definition "rtbl_ifs = set \<circ> map (output_iface \<circ> routing_action)"
lemma ra_in_rtbl_ifs: "valid_prefixes rt \<Longrightarrow> has_default_route rt \<Longrightarrow> output_iface (routing_table_semantics rt d) \<in> rtbl_ifs rt"
	apply(induction rt)
	 apply(simp;fail)
	apply(simp add: rtbl_ifs_def comp_def)
using valid_prefixes_split zero_prefix_match_all by blast

(* TODO: move *)
lemma simple_matches_update_any: "simple_matches a p \<Longrightarrow> simple_matches (a\<lparr>oiface := ifaceAny\<rparr>) (p\<lparr>p_oiface := any\<rparr>)"
	by(clarsimp simp: simple_matches.simps match_ifaceAny)

lemma fourtytwo_nullifyoif_Some_keep: "generalized_sfw s p = Some b \<Longrightarrow> \<exists>b'. generalized_sfw (fourtytwo_nullifyoif s) (p\<lparr>p_oiface := any\<rparr>) = Some b'"
	by(induction s) (simp_all add: generalized_sfw_simps fourtytwo_nullifyoif_def const_def simple_matches_update_any split: prod.splits if_splits)

lemma invert_map_append: "map f l = a @ b \<Longrightarrow> \<exists>a' b'. map f (a' @ b') = a @ b \<and> length a' = length a \<and> length b' = length b"
proof(induction a arbitrary: l)
	case (Cons a as)
	from Cons.prems have "map f (tl l) = as @ b" by auto
	with Cons.IH obtain a' b' where ab': "map f (a' @ b') = as @ b" "length a' = length as \<and> length b' = length b" by blast
	show ?case proof(intro exI)
		show "map f (((hd l) # a') @ b') = (a # as) @ b \<and> length ((hd l) # a') = length (a # as) \<and> length b' = length b" using Cons.prems ab' by fastforce
	qed
qed force

lemma s1_correct_noupd: "valid_prefixes (rt::routing_rule list) \<Longrightarrow> has_default_route rt \<Longrightarrow> \<exists>rm ra. generalized_sfw (fourtytwo_s1 rt) p = Some (rm,ra) \<and> ra = output_iface (routing_table_semantics rt (p_dst p))"
oops (*
proof -
	case goal1
	note s1_correct[OF this, of p] then obtain rm ra where rmra: 
	"generalized_sfw (fourtytwo_s1 rt) (p\<lparr>p_oiface := ra\<rparr>) = Some (rm, ra)" "ra = output_iface (routing_table_semantics rt (p_dst p))"
 by blast
	have "generalized_sfw (fourtytwo_s1 rt) (p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>) = Some (rm, ra)" using rmra by fast
	note generalized_fw_split[OF this]
	then obtain a b where ab: "fourtytwo_s1 rt = a @ (rm, ra) # b" "generalized_sfw a (p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>) = None" by blast
	from ab(1) obtain rta where rtab: "fourtytwo_s1 (rta::routing_rule list) = a" 
		apply(simp add: fourtytwo_s1_def)
		apply(drule invert_map_append) 
		apply(clarsimp)
	done
oops*)

definition "to_OF_action a \<equiv> (case a of (p,d) \<Rightarrow> (case d of simple_action.Accept \<Rightarrow> [Forward p] | simple_action.Drop \<Rightarrow> []))"
definition "from_OF_action a = (case a of [] \<Rightarrow> ('''',simple_action.Drop) | [Forward p] \<Rightarrow> (p, simple_action.Accept))"

(* TODO: move *)
lemma OF_match_linear_append: "OF_match_linear \<gamma> (a @ b) p = (case OF_match_linear \<gamma> a p of NoAction \<Rightarrow> OF_match_linear \<gamma> b p | x \<Rightarrow> x)"
by(induction a) simp_all

(* TODO: move? *)
lemma OF_match_linear_match_allsameaction: "\<lbrakk>gr \<in> set oms; OF_match_fields_safe gr p = True\<rbrakk>
       \<Longrightarrow> OF_match_linear OF_match_fields_safe (map (\<lambda>x. split3 OFEntry (pri, x, act)) oms) p = Action act"
by(induction oms) (auto simp add: split3_def)

lemma the_SomeI: "x = Some y \<Longrightarrow> the x = y" by(fact handy_lemma)

lemma OF_match_linear_not_noD: "OF_match_linear \<gamma> oms p \<noteq> NoAction \<Longrightarrow> \<exists>ome. ome \<in> set oms \<and> \<gamma> (ofe_fields ome) p"
	apply(induction oms)
	 apply(simp)
	apply(simp split: if_splits)
	 apply blast+
done

(* TODO: move *)
lemma of_match_fields_safe_eq2: assumes "all_prerequisites m" shows "OF_match_fields_safe m p \<longleftrightarrow> OF_match_fields m p = Some True"
unfolding OF_match_fields_safe_def[abs_def] fun_eq_iff comp_def unfolding of_safe_unsafe_match_eq[OF assms] unfolding option.sel by simp

lemma s3_noaction_hlp: "\<lbrakk>simple_match_valid ac; \<not>simple_matches ac p; match_iface (oiface ac) (p_oiface p)\<rbrakk> \<Longrightarrow> 
OF_match_linear OF_match_fields_safe (map (\<lambda>x. split3 OFEntry (x1, x, case ba of simple_action.Accept \<Rightarrow> [Forward ad] | simple_action.Drop \<Rightarrow> [])) (simple_match_to_of_match ac ifs)) p = NoAction"
  apply(rule ccontr)
  apply(drule OF_match_linear_not_noD)
  apply(clarsimp)
  apply(rename_tac x)
  apply(subgoal_tac "all_prerequisites x")
  apply(drule simple_match_to_of_matchD)
  apply(simp add: split3_def)
  apply(subst(asm) of_match_fields_safe_eq2)
  apply(assumption)
  apply(assumption)
  apply(assumption)
  apply(assumption)
  apply(simp;fail)
using simple_match_to_of_match_generates_prereqs by blast



lemma generalized_sfw_Some_append: "generalized_sfw rs1 p = Some X \<Longrightarrow> generalized_sfw (rs1@rs2) p = Some X"
  apply(simp add: generalized_sfw_def)
  apply(induction rs1)
   apply(simp)
  apply(simp split: split_if_asm)
  done
lemma generalized_sfw_None_append: "generalized_sfw rs1 p = None \<Longrightarrow> generalized_sfw (rs1@rs2) p = generalized_sfw rs2 p"
  apply(simp add: generalized_sfw_def)
  apply(induction rs1)
   apply(simp)
  apply(simp split: split_if_asm)
  done

lemma OF_match_linear_action_append_iff_generalized_sfw:
  assumes ft_tail: "(OF_match_linear OF_match_fields_safe ft_tail p = Action of_action \<longleftrightarrow> generalized_sfw rs p = Some (m, rtfw_action))"
  and ft_hd_action: "(OF_match_linear OF_match_fields_safe ft_hd p = Action of_action \<longleftrightarrow> generalized_sfw [r] p = Some (m, rtfw_action))"
  and ft_hd_noaction: "(OF_match_linear OF_match_fields_safe ft_hd p = NoAction \<longleftrightarrow> generalized_sfw [r] p = None)"
  shows "(OF_match_linear OF_match_fields_safe (ft_hd @ ft_tail) p = Action of_action) \<longleftrightarrow> (generalized_sfw (r # rs) p = Some (m, rtfw_action))"
proof -
  have x1: "(OF_match_linear OF_match_fields_safe ft_tail p = Action of_action \<Longrightarrow> generalized_sfw rs p = Some (m, rtfw_action)) \<Longrightarrow>
      (OF_match_linear OF_match_fields_safe ft_hd p = Action of_action \<Longrightarrow> generalized_sfw [r] p = Some (m, rtfw_action)) \<Longrightarrow>
      (OF_match_linear OF_match_fields_safe ft_hd p = NoAction \<Longrightarrow> generalized_sfw [r] p = None) \<Longrightarrow>
      (OF_match_linear OF_match_fields_safe (ft_hd @ ft_tail) p = Action of_action) \<Longrightarrow> (generalized_sfw (r # rs) p = Some (m, rtfw_action))"
   apply(simp add: OF_match_linear_append)
   apply(case_tac "OF_match_linear OF_match_fields_safe ft_hd p")
     apply(simp)
     apply(subgoal_tac "(generalized_sfw [r] p = Some (m, rtfw_action))")
      prefer 2
      apply blast
     using generalized_sfw_Some_append apply fastforce
    apply(simp)
    apply(drule_tac generalized_sfw_None_append[of _ p rs])
    apply fastforce
   apply(simp; fail)
  done
  have x2: "(generalized_sfw rs p = Some (m, rtfw_action) \<Longrightarrow> OF_match_linear OF_match_fields_safe ft_tail p = Action of_action) \<Longrightarrow>
      (generalized_sfw [r] p = Some (m, rtfw_action) \<Longrightarrow> OF_match_linear OF_match_fields_safe ft_hd p = Action of_action) \<Longrightarrow>
      (generalized_sfw [r] p = None \<Longrightarrow> OF_match_linear OF_match_fields_safe ft_hd p = NoAction) \<Longrightarrow>
      ((generalized_sfw (r # rs) p = Some (m, rtfw_action)) \<Longrightarrow> OF_match_linear OF_match_fields_safe (ft_hd @ ft_tail) p = Action of_action)"
   apply(simp add: generalized_sfw_append[of "[r]" rs p, simplified])
   apply(simp split: option.split_asm)
    apply(simp add: OF_match_linear_append; fail)
   apply(simp add: OF_match_linear_append; fail)
  done

  from assms show ?thesis
   apply-
   apply(rule iffI)
    apply(rule x1, simp_all)
   apply(rule x2, simp_all)
   done
qed


lemma OF_lm_noa_none2: "\<forall>e\<in>set ft. \<not> \<gamma> (ofe_fields e) p \<Longrightarrow> OF_match_linear \<gamma> ft p = NoAction"
	by(induction ft) (simp_all split: if_splits)
(*TODO: sqrl, move!*)
lemma OF_lm_noa_none_iff: "OF_match_linear \<gamma> ft p = NoAction \<longleftrightarrow> (\<forall>e\<in>set ft. \<not> \<gamma> (ofe_fields e) p)"
	by(induction ft) (simp_all split: if_splits)

lemma OF_match_linear_not_noE:"ome \<in> set oms \<and> \<gamma> (ofe_fields ome) p \<Longrightarrow> OF_match_linear \<gamma> oms p \<noteq> NoAction"
apply(induction oms)
	 apply(simp)
	apply(simp split: if_splits)
	 apply blast+
done
lemma OF_match_linear_not_iff: "OF_match_linear \<gamma> oms p \<noteq> NoAction \<longleftrightarrow> (\<exists>ome. ome \<in> set oms \<and> \<gamma> (ofe_fields ome) p)"
  apply(rule)
   using OF_match_linear_not_noD apply metis
  using OF_match_linear_not_noE by metis

lemma OF_match_linear_action1: "ome \<in> set oms \<and> \<gamma> (ofe_fields ome) p \<Longrightarrow>
      \<exists>a. a \<in> set oms \<and> OF_match_linear \<gamma> oms p = Action (ofe_action a)"
apply(induction oms)
	 apply(simp)
	apply(simp)
	apply auto
done
lemma OF_match_linear_action2: "ome \<in> set oms \<and> OF_match_linear \<gamma> oms p = Action (ofe_action ome) \<Longrightarrow> \<gamma> (ofe_fields ome) p"
oops
lemma OF_match_linear_action_find_iff: "OF_match_linear \<gamma> oms p = Action a \<longleftrightarrow> 
       (\<exists>prio flds. List.find (\<lambda>f. \<gamma> (ofe_fields f) p) oms = Some (OFEntry prio flds a))"
apply(induction oms)
	 apply(simp)
	apply(simp)
	apply(safe)
	   apply(simp_all)
	 apply(rename_tac ome oms prio flds)
	 apply(case_tac ome, simp)
	apply(rename_tac ome oms)
	apply(case_tac ome, simp)
	done
lemma 
  defines "only_match_action (ft::(of_match_field, 'a) flow_entry_match list) \<equiv> 
            map (\<lambda>f. case f of OFEntry p flds action \<Rightarrow> (flds, action)) ft"
	assumes ft_eq: "only_match_action ft =
	                   concat (map (\<lambda>(m,a). map (\<lambda>flowmatch. (flowmatch, f a)) (simple_match_to_of_match m ifs)) rs)"
     and action_rslt: "of_action = f rtfw_action"
	shows "OF_match_linear OF_match_fields_safe ft p = Action of_action \<longleftrightarrow> 
	       generalized_sfw rs p = (Some (m, (rtfw_action:: 'fw_action)))" (*TODO: needs \<exists>m*)
  using ft_eq proof(induction rs arbitrary: ft)
  case Nil thus ?case
    apply(simp add: generalized_sfw_def)
    apply(simp add: only_match_action_def; fail)
    done
  next
  case (Cons r rs)
    let ?r_part="(case r of (m, a) \<Rightarrow> map (\<lambda>flowmatch. (flowmatch, f a)) (simple_match_to_of_match m ifs))"
    let ?rs_part="concat (map (\<lambda>(m, a). map (\<lambda>flowmatch. (flowmatch, f a)) (simple_match_to_of_match m ifs)) rs)"
    have ft_only: "only_match_action ft = ?r_part @ ?rs_part" by(simp add: Cons.prems)
    obtain ft_hd ft_tail where ft: "ft = ft_hd@ft_tail"
                           and ft_hd: "ft_hd = take (length ?r_part) ft"
                           and ft_tail: "ft_tail = drop (length ?r_part) ft"
      by(simp)
    from Cons.prems
    have only_match_action_ft_tail: "only_match_action ft_tail = ?rs_part"
      apply(simp add: ft_tail)
      by (metis (no_types, lifting) drop_all_conc drop_map only_match_action_def)
    with Cons.IH have 
      IH: "(OF_match_linear OF_match_fields_safe ft_tail p = Action of_action) \<longleftrightarrow> (generalized_sfw rs p = Some (m, rtfw_action))"
      by blast


    (*unused but useful?*)
    have only_match_action_obtain_prios: 
      "only_match_action ft = rs \<Longrightarrow> \<exists>prios. length prios = length rs \<and> 
                                                map (\<lambda>(prio, (m,a)). OFEntry prio m a) (zip prios rs) = ft" for ft rs
      apply(induction ft arbitrary: rs)
       apply(simp add: only_match_action_def; fail)
      apply(rename_tac e ft rs)
      apply(case_tac rs)
       apply(simp add: only_match_action_def; fail)
      apply(rename_tac r rs)
      apply(simp)
      apply(simp add: only_match_action_def)
      apply(subgoal_tac "\<exists>prios. length prios = length rs \<and> map (\<lambda>(prio, x, y). OFEntry prio x y) (zip prios rs) = ft")
       prefer 2
       apply blast
      apply(elim exE conjE, rename_tac prios)
      apply(case_tac e, rename_tac p x1 x2)
      apply(simp)
      apply(rule_tac x="p#prios" in exI)
      apply(simp)
      by fast
       
    have OF_match_linear_rule: 
      "OF_match_linear OF_match_fields_safe ft p = NoAction \<longleftrightarrow> (\<forall>(m,a)\<in>set rs. \<not> OF_match_fields_safe m p)"
      if prems: "only_match_action ft = rs" for ft rs
       apply -
       apply(subst OF_lm_noa_none_iff)
       apply(subst prems[symmetric])
       apply(simp add: only_match_action_def)
       apply safe
        apply(rename_tac x m a, case_tac x)
        apply(simp)
        apply fastforce
       apply(rename_tac e, case_tac e)
       apply(simp)
       apply fastforce
       done
    have OF_match_linear_ft_hd_noAction: 
      "OF_match_linear OF_match_fields_safe ft_hd p = NoAction \<longleftrightarrow> (\<forall>(m,a)\<in>set ?r_part. \<not> OF_match_fields_safe m p)"
       apply(rule OF_match_linear_rule)
       using only_match_action_ft_tail ft ft_only only_match_action_def by auto
    
    (*
    we don't need \<noteq> NoAction, we need = Action
    have OF_match_linear_rule2: 
      "OF_match_linear OF_match_fields_safe ft p \<noteq> NoAction \<longleftrightarrow> (\<exists>(m,a)\<in>set rs. OF_match_fields_safe m p)"
      if prems: "only_match_action ft = rs" for ft rs
       apply -
       apply(subst OF_match_linear_not_iff)
       apply(subst prems[symmetric])
       apply(simp add: only_match_action_def)
       apply safe
        apply(rename_tac x, case_tac x)
        apply(simp)
        apply force
       apply(rename_tac x xa y, case_tac x)
       apply(simp)
       apply fastforce
       done
    have OF_match_linear_ft_hd_Action: "OF_match_linear OF_match_fields_safe ft_hd p \<noteq> NoAction \<longleftrightarrow> (\<exists>(m,a)\<in>set ?r_part. OF_match_fields_safe m p)"
      apply(rule OF_match_linear_rule2)
      apply(simp add: only_match_action_def)
      using only_match_action_ft_tail ft ft_only only_match_action_def by auto
    *)


    have OF_match_linear_rule2: "(OF_match_linear OF_match_fields_safe ft p = Action of_action) \<longleftrightarrow> 
          (\<exists>m. List.find (\<lambda>(m,a). OF_match_fields_safe m p) rs = Some (m,of_action))"
      if prems: "only_match_action ft = rs" for ft rs
       apply -
       apply(subst OF_match_linear_action_find_iff)
       apply(subst prems[symmetric])
       apply(simp add: only_match_action_def)
       apply safe
        apply(rename_tac prio flds)
        apply(rule_tac x="flds" in exI)
        (*ugly subgoal, cams case splits*)
        apply(induction ft)
         apply(simp; fail)
        apply(simp split: split_if_asm flow_entry_match.split)
        apply force
       apply(rename_tac m)
       apply(induction ft)
        apply(simp; fail)
       apply(simp split: split_if_asm flow_entry_match.split flow_entry_match.split_asm)
       done
    have OF_match_linear_ft_hd_Action: "(OF_match_linear OF_match_fields_safe ft_hd p = Action of_action) \<longleftrightarrow> 
          (\<exists>m. List.find (\<lambda>(m,a). OF_match_fields_safe m p) ?r_part = Some (m,of_action))"
      apply(rule OF_match_linear_rule2)
      apply(simp add: only_match_action_def)
      using only_match_action_ft_tail ft ft_only only_match_action_def by auto


    have step_noaction: "(OF_match_linear OF_match_fields_safe ft_hd p = NoAction) \<longleftrightarrow> (generalized_sfw [r] p = None)"
      apply(subst OF_match_linear_ft_hd_noAction)
      apply(cases r, rename_tac m a)
      apply(simp add: generalized_sfw_def)
      (*TODO: sqrl sagt das sollte trivial sein*)
      sorry
    have "(OF_match_linear OF_match_fields_safe ft_hd p = Action of_action) \<longleftrightarrow> (generalized_sfw [r] p = Some (m, rtfw_action))"
      apply(subst OF_match_linear_ft_hd_Action)
      apply(cases r, rename_tac m' a)
      apply(simp add: generalized_sfw_def)
      (*hmm, wemm man das blau m gegen ein \<exists>m tauscht und action_rslt nutzt, sollte das gelten*)
      sorry
    with step_noaction IH show ?case
      apply(simp add: ft)
      apply(rule OF_match_linear_action_append_iff_generalized_sfw)
      apply(simp_all)
      done
oops


lemma s3_correct:
	assumes vsfwm: "list_all simple_match_valid $ map (fst \<circ> snd) ard"
	assumes ippkt: "p_l2type p = 0x800"
	assumes iiifs: "p_iiface p \<in> set ifs"
	assumes oiifs: "list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) ard"
	shows "OF_match_linear OF_match_fields_safe (pack_OF_entries ifs ard) p = Action ao \<longleftrightarrow> (\<exists>r af. generalized_sfw (map snd ard) p = (Some (r,af)) \<and> (if snd af = simple_action.Drop then ao = [] else ao = [Forward (fst af)]))"
unfolding pack_OF_entries_def fourtytwo_s3_def fun_app_def
using vsfwm oiifs
  apply(induction ard)
   apply(simp add: generalized_sfw_simps)
  apply simp
  apply(clarsimp simp add: generalized_sfw_simps split: prod.splits)
  apply(intro conjI)
   apply(clarsimp simp add: OF_match_linear_append split: prod.splits)
  apply(drule simple_match_to_of_matchI[rotated])
      apply(rule iiifs)
     apply(rule ippkt)
    apply blast
   apply(clarsimp simp add: comp_def)
   apply(rename_tac ard x1 ac ad ba gr)
   apply(drule_tac oms = "simple_match_to_of_match ac ifs" and pri = x1 and act = "case ba of simple_action.Accept \<Rightarrow> [Forward ad] | simple_action.Drop \<Rightarrow> []" in OF_match_linear_match_allsameaction)
    apply(unfold OF_match_fields_safe_def comp_def)
    apply(erule the_SomeI;fail)
   defer
   apply(simp add: OF_match_linear_append)
   apply(rename_tac ard x1 ac ad ba)
   apply(clarify)
   apply(subgoal_tac "OF_match_linear OF_match_fields_safe (map (\<lambda>x. split3 OFEntry (x1, x, case ba of simple_action.Accept \<Rightarrow> [Forward ad] | simple_action.Drop \<Rightarrow> [])) (simple_match_to_of_match ac ifs)) p = NoAction")
    apply(simp;fail)
   apply(erule (1) s3_noaction_hlp)
   apply(simp add: match_ifaceAny;fail)
  apply(clarsimp)
  apply(intro iffI)
   apply(clarsimp split: simple_action.splits)
   apply blast
  apply(clarsimp)
  apply(rename_tac b)
  apply(case_tac b)
   apply(simp_all)
done

lemma has_default_policy_ex_general_result: "has_default_policy fw \<Longrightarrow> \<exists>m a. generalized_sfw (map simple_rule_dtor fw) p = Some (m,a)"
by(induction fw rule: has_default_policy.induct) (simp_all add: generalized_sfw_simps simple_rule_dtor_def simple_match_any)

lemma simple_match_inject: " \<lparr>iiface = iifacea, oiface = oifacea, src = srca, dst = dsta, proto = protoa, sports = sportsa, dports = dportsa\<rparr>
      = \<lparr>iiface = iifaceb, oiface = oifaceb, src = srcb, dst = dstb, proto = protob, sports = sportsb, dports = dportsb\<rparr> \<longleftrightarrow>
      (iifacea = iifaceb \<and> oifacea = oifaceb \<and> srca = srcb \<and> dsta = dstb \<and> protoa = protob \<and> sportsa = sportsb \<and> dportsa = dportsb)"
by simp

(* TODO: move *)
lemma ipv4cidr_conjunct_valid: "\<lbrakk>valid_prefix_fw p1; valid_prefix_fw p2; ipv4cidr_conjunct p1 p2 = Some p\<rbrakk> \<Longrightarrow> valid_prefix_fw p"
unfolding valid_prefix_fw_def
  by(cases p; cases p1; cases p2) (simp add: ipv4cidr_conjunct.simps split: if_splits)
lemma simpl_ports_conjunct_not_UNIV:
"Collect (simple_match_port x) \<noteq> UNIV \<Longrightarrow> x = simpl_ports_conjunct p1 p2 \<Longrightarrow> Collect (simple_match_port p1) \<noteq> UNIV \<or> Collect (simple_match_port p2) \<noteq> UNIV" 
  by (metis Collect_cong mem_Collect_eq simple_ports_conjunct_correct)
lemma simple_match_and_valid: "simple_match_valid m1 \<Longrightarrow> simple_match_valid m2 \<Longrightarrow> simple_match_and m1 m2 = Some m \<Longrightarrow> simple_match_valid m"
unfolding simple_match_valid_def
apply(cases m; cases m1; cases m2)
apply(rename_tac iiface oiface srca dsta protoa sportsa dportsa iifacea oifacea srcaa dstaa protoaa sportsaa dportsaa iifaceb oifaceb srcb dstb protob sportsb dportsb)
apply(intro conjI[rotated])
apply(simp split: option.splits)
apply(erule (2) ipv4cidr_conjunct_valid[rotated,rotated])
apply(simp split: option.splits)
apply(erule (2) ipv4cidr_conjunct_valid[rotated,rotated])
apply(clarify)
apply(unfold simple_match.simps)
apply(erule disjE)
apply(drule simpl_ports_conjunct_not_UNIV)
apply(unfold simple_match_and.simps)
apply(split option.splits, (simp;fail))+
apply(unfold option.inject simple_match_inject)
apply(clarify)
apply(erule sym)
apply(erule disjE)
apply(simp)
apply(elim disjE)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp)
apply(elim disjE)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
apply(drule simpl_ports_conjunct_not_UNIV)
apply(split option.splits, (simp;fail))+
apply(unfold option.inject simple_match_inject)
apply(clarify)
apply(erule sym)
apply(erule disjE)
apply(simp)
apply(elim disjE)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp split: option.splits)
apply(metis conjunctProtoD protocol.simps(3) simple_proto_conjunct.elims)
apply(simp)
apply(elim disjE)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
apply(simp split: option.splits)
apply(metis conjunctProtoD)
done (* okay, shit. *)

(* TODO: move *)
definition "gsfw_valid \<equiv> list_all (simple_match_valid \<circ> fst) :: (simple_match \<times> 'c) list \<Rightarrow> bool"
lemma gsfw_join_valid: "gsfw_valid f1 \<Longrightarrow> gsfw_valid f2 \<Longrightarrow> gsfw_valid (generalized_fw_join f1 f2)"
unfolding gsfw_valid_def
apply(induction f1)
apply(simp;fail)
apply(simp)
apply(rename_tac a f1)
apply(case_tac a)
apply(simp add: generalized_fw_join_cons_1)
apply(clarify)
apply(thin_tac "list_all _ f1")
apply(thin_tac "list_all _ (generalized_fw_join _ _)")
apply(induction f2)
apply(simp;fail)
apply(simp)
apply(clarsimp simp add: option2list_def list_all_iff)
using simple_match_and_valid apply metis
done
lemma gsfw_validI: "simple_fw_valid fw \<Longrightarrow> gsfw_valid (map simple_rule_dtor fw)" unfolding gsfw_valid_def simple_fw_valid_def 
by(clarsimp simp add: simple_rule_dtor_def list_all_iff split: simple_rule.splits) fastforce

lemma valid_prefix_00[simp,intro!]: "valid_prefix (PrefixMatch 0 0)" by (simp add: valid_preifx_alt_def)

lemma oif_ne_iif_valid: "gsfw_valid (oif_ne_iif ifs)"
  unfolding oif_ne_iif_def gsfw_valid_def list_all_iff oif_ne_iif_p1_def oif_ne_iif_p2_def
  apply(clarsimp simp add: Set.image_iff simple_match_valid_def simple_match_any_def valid_prefix_fw_def)
  using simple_match_valid_alt_hlp1 apply force
done

lemma fourtytwo_s1_valid: "valid_prefixes rt \<Longrightarrow> gsfw_valid (fourtytwo_s1 rt)"
  unfolding fourtytwo_s1_def route2match_def gsfw_valid_def list_all_iff
  apply(clarsimp simp: simple_match_valid_def valid_prefix_fw_def)
  apply(intro conjI)
  using simple_match_valid_alt_hlp1 apply force
  using valid_prefixes_alt_def apply blast
done

(* TODO: move with annotate_rlen *)
lemma in_annotate_rlen: "(a,x) \<in> set (annotate_rlen l) \<Longrightarrow> x \<in> set l" 
  by(induction l) (simp_all, blast)

lemma simple_match_valid_fbs_rlen: "\<lbrakk>valid_prefixes rt; simple_fw_valid fw; (a, aa, ab, b) \<in> set (annotate_rlen (fourtytwo_fbs rt fw ifs))\<rbrakk> \<Longrightarrow> simple_match_valid aa"
proof(goal_cases)
  case 1
  note 1[unfolded fourtytwo_fbs_def Let_def]
  have "gsfw_valid (map simple_rule_dtor fw)" using gsfw_validI 1 by blast
  moreover have "gsfw_valid (fourtytwo_s1 rt)" using 1 fourtytwo_s1_valid by blast
  ultimately have "gsfw_valid (generalized_fw_join (fourtytwo_s1 rt) (map simple_rule_dtor fw))" using gsfw_join_valid by blast
  moreover have "(aa, ab, b) \<in> set (fourtytwo_fbs rt fw ifs)" using 1 using in_annotate_rlen by fast
  ultimately show ?thesis unfolding fourtytwo_fbs_def Let_def gsfw_valid_def list_all_iff by fastforce
qed

lemma simple_match_valid_fbs: "\<lbrakk>valid_prefixes rt; simple_fw_valid fw\<rbrakk> \<Longrightarrow> list_all simple_match_valid (map fst (fourtytwo_fbs rt fw ifs))"
proof(goal_cases)
  case 1
  note 1[unfolded fourtytwo_fbs_def Let_def]
  have "gsfw_valid (map simple_rule_dtor fw)" using gsfw_validI 1 by blast
  moreover have "gsfw_valid (fourtytwo_s1 rt)" using 1 fourtytwo_s1_valid by blast
  ultimately have "gsfw_valid (generalized_fw_join (fourtytwo_s1 rt) (map simple_rule_dtor fw))" using gsfw_join_valid by blast
  thus ?thesis unfolding fourtytwo_fbs_def Let_def gsfw_valid_def list_all_iff by fastforce
qed

lemma fourtytwo_prereqs: "valid_prefixes rt \<Longrightarrow> simple_fw_valid fw \<Longrightarrow> fourtytwo rt fw ifs = Inr oft \<Longrightarrow>
list_all (all_prerequisites \<circ> ofe_fields) oft"
unfolding fourtytwo_def pack_OF_entries_def fourtytwo_s3_def Let_def
  apply(simp add: map_concat comp_def prod.case_distrib split3_def split: if_splits)
  apply(simp add: list_all_iff)
  apply(clarsimp)
  apply(drule simple_match_valid_fbs_rlen[rotated])
    apply(simp add: list_all_iff;fail)
   apply(simp add: list_all_iff;fail)
  apply(erule (1) simple_match_to_of_match_generates_prereqs)
done

(* TODO: move. where? *)
lemma OF_unsafe_safe_match3_eq: "
  list_all (all_prerequisites \<circ> ofe_fields) oft \<Longrightarrow>
  OF_same_priority_match3 OF_match_fields_unsafe oft = OF_same_priority_match3 OF_match_fields_safe oft"
unfolding OF_same_priority_match3_def[abs_def]
proof(goal_cases)
  case 1
  from 1 have "\<And>packet. [f\<leftarrow>oft . OF_match_fields_unsafe (ofe_fields f) packet] = [f\<leftarrow>oft . OF_match_fields_safe (ofe_fields f) packet]"
    apply(clarsimp simp add: list_all_iff of_match_fields_safe_eq) 
  using of_match_fields_safe_eq by(metis (mono_tags, lifting) filter_cong)
  thus ?case by metis
qed

lemma OF_unsafe_safe_match_linear_eq: "
  list_all (all_prerequisites \<circ> ofe_fields) oft \<Longrightarrow>
  OF_match_linear OF_match_fields_unsafe oft = OF_match_linear OF_match_fields_safe oft"
unfolding fun_eq_iff
by(induction oft) (clarsimp simp add: list_all_iff of_match_fields_safe_eq)+

lemma simple_action_ne[simp]: 
  "b \<noteq> simple_action.Accept \<longleftrightarrow> b = simple_action.Drop"
  "b \<noteq> simple_action.Drop \<longleftrightarrow> b = simple_action.Accept"
using simple_action.exhaust by blast+

lemma map_snd_annotate_rlen: "map snd (annotate_rlen l) = l"
  by(induction l) simp_all
lemma map_snd_apfst: "map snd (map (apfst x) l) = map snd l"
  unfolding map_map comp_def snd_apfst ..

definition "no_oif_match \<equiv> list_all (\<lambda>m. oiface (match_sel m) = ifaceAny)"
lemma match_ifaceAny_eq: "oiface m = ifaceAny \<Longrightarrow> simple_matches m p = simple_matches m (p\<lparr>p_oiface := any\<rparr>)"
by(cases m) (simp add: simple_matches.simps match_ifaceAny)
lemma no_oif_matchD: "no_oif_match fw \<Longrightarrow> simple_fw fw p = simple_fw fw (p\<lparr>p_oiface := any\<rparr>)"
  apply(induction fw)
   apply(simp add: simple_fw_alt;fail)
  apply(rename_tac a fw)
  apply(subgoal_tac "oiface (match_sel a) = ifaceAny")
   apply(drule match_ifaceAny_eq[of _ p any])
   apply(clarsimp simp add: simple_fw_alt no_oif_match_def)
  apply(simp add: no_oif_match_def)
done

lemma fourtytwo_fbs_acceptD:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw"
  shows "generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Accept) \<Longrightarrow>
  simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>)"
proof(goal_cases)
  case 1
  note 1[unfolded fourtytwo_fbs_def Let_def, THEN generalized_fw_joinD]
  then guess r1 .. then guess r2 .. note r12 = this
  note s1_correct[OF s1, of p]
  then guess rm .. then guess ra .. note rmra = this
  from r12 rmra have oifra: "oif = ra" by simp
  from r12 have sfw: "simple_fw fw p = Decision FinalAllow" using simple_fw_iff_generalized_fw_accept by blast
  note ifupdateirrel = no_oif_matchD[OF s2, where any = " output_iface (routing_table_semantics rt (p_dst p))" and p = p, symmetric]
  show ?case unfolding simple_linux_router_nol12_def by(simp add: Let_def ifupdateirrel sfw oifra rmra split: Option.bind_splits option.splits) 
qed

lemma fourtytwo_fbs_acceptI:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw" "has_default_policy fw"
  shows "simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) \<Longrightarrow>
  \<exists>r. generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Accept)"
proof(goal_cases)
  from s2 have nud: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy state.distinct(1))
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1 have "simple_fw fw p = Decision FinalAllow" by(simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  then obtain r where r: "generalized_sfw (map simple_rule_dtor fw) p = Some (r, simple_action.Accept)" using simple_fw_iff_generalized_fw_accept by blast
  have oif_def: "oif = output_iface (routing_table_semantics rt (p_dst p))" using 1 by(cases p) (simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  note s1_correct[OF s1, of p] then guess rm .. then guess ra .. note rmra = this
  show ?case unfolding fourtytwo_fbs_def Let_def
    apply(rule exI)
    apply(rule generalized_fw_joinI)
    unfolding oif_def using rmra apply simp
    apply(rule r)
  done
qed

lemma fourtytwo_fbs_dropD:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw"
  shows "generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop) \<Longrightarrow>
  simple_linux_router_nol12 rt fw p = None"
proof(goal_cases)
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1[unfolded fourtytwo_fbs_def Let_def, THEN generalized_fw_joinD]
  obtain rr fr where "generalized_sfw (fourtytwo_s1 rt) p = Some (rr, oif) \<and>
          generalized_sfw (map simple_rule_dtor fw) p = Some (fr, simple_action.Drop) \<and> Some r = simple_match_and rr fr" by presburger
  hence fd: "\<And>u. simple_fw fw (p\<lparr>p_oiface := u\<rparr>) = Decision FinalDeny" unfolding ifupdateirrel
  using simple_fw_iff_generalized_fw_drop by blast
  show ?thesis
    by(clarsimp simp: simple_linux_router_nol12_def Let_def fd split: Option.bind_splits)
qed

lemma fourtytwo_fbs_dropI:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw" "has_default_policy fw"
  shows "simple_linux_router_nol12 rt fw p = None \<Longrightarrow>
  \<exists>r oif. generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)"
proof(goal_cases)
  from s2 have nud: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy state.distinct(1))
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1 have "simple_fw fw p = Decision FinalDeny" by(simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  then obtain r where r: "generalized_sfw (map simple_rule_dtor fw) p = Some (r, simple_action.Drop)" using simple_fw_iff_generalized_fw_drop by blast
  note s1_correct[OF s1, of p] then guess rm .. then guess ra .. note rmra = this
  show ?case unfolding fourtytwo_fbs_def Let_def
    apply(rule exI)
    apply(rule exI[where x = ra])
    apply(rule generalized_fw_joinI)
    using rmra apply simp
    apply(rule r)
  done
qed


lemma list_all_map: "list_all f (map g l) = list_all (f \<circ> g) l"
unfolding comp_def by (simp add: list_all_length) (* by(induction l) simp_all *)

(* TODO: move *)
lemma in_fw_join_set: "(a, b1, b2) \<in> set (generalized_fw_join f1 f2) \<Longrightarrow> \<exists>a1 a2. (a1, b1) \<in> set f1 \<and> (a2, b2) \<in> set f2 \<and> simple_match_and a1 a2 = Some a"
unfolding generalized_fw_join_def by(clarsimp simp: option2set_def split: option.splits) blast

lemma no_oif_match_fbs:
 "no_oif_match fw \<Longrightarrow> list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) (map (apfst word_of_nat) (annotate_rlen (fourtytwo_fbs rt fw ifs)))"
proof(goal_cases)
  case 1
  have c: "\<And>mr ar mf af f a. \<lbrakk>(mr, ar) \<in> set (fourtytwo_s1 rt); (mf, af) \<in> simple_rule_dtor ` set fw; simple_match_and mr mf = Some a\<rbrakk> \<Longrightarrow> oiface a = ifaceAny"
  proof(goal_cases)
    case (1 mr ar mf af f a)
    have "oiface mr = ifaceAny" using 1(1) unfolding fourtytwo_s1_def route2match_def by(clarsimp simp add: Set.image_iff)
    moreover have "oiface mf = ifaceAny" using 1(2) \<open>no_oif_match fw\<close> unfolding no_oif_match_def simple_rule_dtor_def[abs_def]
      by(clarsimp simp: list_all_iff split: simple_rule.splits) fastforce 
    ultimately show ?case using 1(3) by(cases a; cases mr; cases mf) (simp add: iface_conjunct_ifaceAny split: option.splits)
  qed
  have la: "list_all (\<lambda>m. oiface (fst m) = ifaceAny) (fourtytwo_fbs rt fw ifs)"
    unfolding fourtytwo_fbs_def Let_def list_all_iff
    apply(clarify)
    apply(drule in_fw_join_set)
    apply(clarsimp)
  using c by blast
  thus ?case
  proof(goal_cases)
    case 1
    have *: "(\<lambda>m. oiface (fst (snd m)) = ifaceAny) = (\<lambda>m. oiface (fst m) = ifaceAny) \<circ> snd" unfolding comp_def ..
    show ?case unfolding * list_all_map[symmetric] map_snd_apfst map_snd_annotate_rlen using la .
  qed
qed

(* TODO: move *)
lemma  OF_match_linear_not_undefined: "OF_match_linear \<gamma> oms p \<noteq> Undefined"
by(induction oms) (simp_all)


lemma fourtytwo_correct:
	fixes p :: "'a simple_packet_ext_scheme"
	assumes s1: "valid_prefixes rt" "has_default_route rt"
	    and s2: "has_default_policy fw" "simple_fw_valid fw" "no_oif_match fw"
	  and nerr: "fourtytwo rt fw ifs = Inr oft"
	 and ippkt: "p_l2type p = 0x800"
	 and   ifl: "is_iface_list ifs"
	 and ifvld: "p_iiface p \<in> set ifs"
	shows "OF_same_priority_match3 OF_match_fields_safe oft p = Action [Forward oif] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = (Some (p\<lparr>p_oiface := oif\<rparr>))"
	      "OF_same_priority_match3 OF_match_fields_safe oft p = Action [] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = None"
	      (* fun stuff: *)
	      "OF_same_priority_match3 OF_match_fields_safe oft p \<noteq> NoAction" "OF_same_priority_match3 OF_match_fields_safe oft p \<noteq> Undefined"
	      "OF_same_priority_match3 OF_match_fields_safe oft p = Action ls \<longrightarrow> length ls \<le> 1"
	      "\<exists>ls. length ls \<le> 1 \<and> OF_same_priority_match3 OF_match_fields_safe oft p = Action ls"
proof -
  have unsafe_safe_eq: 
    "OF_same_priority_match3 OF_match_fields_unsafe oft = OF_same_priority_match3 OF_match_fields_safe oft"
    "OF_match_linear OF_match_fields_unsafe oft = OF_match_linear OF_match_fields_safe oft"
    apply(subst OF_unsafe_safe_match3_eq; (rule fourtytwo_prereqs s1 s2 nerr refl)+)
    apply(subst OF_unsafe_safe_match_linear_eq; (rule fourtytwo_prereqs s1 s2 nerr refl)+)
  done
  have lin: "OF_same_priority_match3 OF_match_fields_safe oft = OF_match_linear OF_match_fields_safe oft"
    using OF_eq[OF fourtytwo_no_overlaps fourtytwo_sorted_descending, OF ifl nerr[symmetric] nerr[symmetric]] unfolding fun_eq_iff unsafe_safe_eq by metis
  let ?ard = "map (apfst word_of_nat) (annotate_rlen (fourtytwo_fbs rt fw ifs))"
  have oft_def: "oft = pack_OF_entries ifs ?ard" using nerr unfolding fourtytwo_def Let_def by(simp split: if_splits)
  have vld: "list_all simple_match_valid $ map (fst \<circ> snd) ?ard" 
    unfolding fun_app_def map_map[symmetric] snd_apfst map_snd_apfst map_snd_annotate_rlen using simple_match_valid_fbs[OF s1(1) s2(2)] .
  have *: "list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) ?ard" using no_oif_match_fbs[OF s2(3)] .
  have not_undec: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy s2(1) state.simps(3))
  have w1_1: "\<And>oif. OF_match_linear OF_match_fields_safe oft p = Action [Forward oif] \<Longrightarrow> simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) 
    \<and> oif = output_iface (routing_table_semantics rt (p_dst p))"
  proof(intro conjI, goal_cases)
    case (1 oif)
    note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD1, unfolded oft_def[symmetric], OF 1]
    hence "\<exists>r. generalized_sfw (map snd (map (apfst word_of_nat) (annotate_rlen (fourtytwo_fbs rt fw ifs)))) p = Some (r, (oif, simple_action.Accept))"
      by(clarsimp split: if_splits)
    then obtain r where "generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, (oif, simple_action.Accept))" 
      unfolding map_map comp_def snd_apfst map_snd_annotate_rlen by blast
    thus ?case using fourtytwo_fbs_acceptD[OF s1 s2(3)] by metis
    thus "oif = output_iface (routing_table_semantics rt (p_dst p))"
      by(cases p) (clarsimp simp: simple_linux_router_nol12_def Let_def not_undec split: Option.bind_splits state.splits final_decision.splits) 
  qed
  have w1_2: "\<And>oif. simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) \<Longrightarrow> OF_match_linear OF_match_fields_safe oft p = Action [Forward oif]"
  proof(goal_cases)
    case (1 oif)
    note fourtytwo_fbs_acceptI[OF s1 s2(3) s2(1) this, of ifs] then guess r .. note r = this
    hence "generalized_sfw (map snd (map (apfst word_of_nat) (annotate_rlen (fourtytwo_fbs rt fw ifs)))) p = Some (r, (oif, simple_action.Accept))" 
    unfolding map_snd_apfst map_snd_annotate_rlen .
    moreover note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD2, unfolded oft_def[symmetric], of "[Forward oif]"]
    ultimately show ?case by simp
  qed
  show w1: "\<And>oif. (OF_same_priority_match3 OF_match_fields_safe oft p = Action [Forward oif]) = (simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>))"
    unfolding lin using w1_1 w1_2 by blast
  show w2: "(OF_same_priority_match3 OF_match_fields_safe oft p = Action []) = (simple_linux_router_nol12 rt fw p = None)"
  unfolding lin
  proof(rule iffI, goal_cases)
    case 1
    note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD1, unfolded oft_def[symmetric], OF 1]
    then obtain r oif where roif: "generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)"
      unfolding map_snd_apfst map_snd_annotate_rlen by(clarsimp split: if_splits)
    note fourtytwo_fbs_dropD[OF s1 s2(3) this]
    thus ?case .
  next
    case 2 
    note fourtytwo_fbs_dropI[OF s1 s2(3) s2(1) this, of ifs] then 
    obtain r oif where "generalized_sfw (fourtytwo_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)" by blast
    hence "generalized_sfw (map snd (map (apfst word_of_nat) (annotate_rlen (fourtytwo_fbs rt fw ifs)))) p = Some (r, oif, simple_action.Drop)" 
      unfolding map_snd_apfst map_snd_annotate_rlen .
    moreover note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD2, unfolded oft_def[symmetric], of "[]"]
    ultimately show ?case by force
  qed
  have lr_determ: "\<And>a. simple_linux_router_nol12 rt fw p = Some a \<Longrightarrow> a = p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>"
    by(clarsimp simp: simple_linux_router_nol12_def Let_def not_undec split: Option.bind_splits state.splits final_decision.splits)
  show notno: "OF_same_priority_match3 OF_match_fields_safe oft p \<noteq> NoAction"
    apply(cases "simple_linux_router_nol12 rt fw p")
    using w2 apply(simp)
    using w1[of "output_iface (routing_table_semantics rt (p_dst p))"] apply(simp)
    apply(drule lr_determ)
    apply(simp)
  done
  show notub: "OF_same_priority_match3 OF_match_fields_safe oft p \<noteq> Undefined" unfolding lin using OF_match_linear_not_undefined .
    (*by (metis fourtytwo_no_overlaps ifl lin nerr no_overlaps_not_unefined unsafe_safe_eq(1))*)
  show notmult: "\<And>ls. OF_same_priority_match3 OF_match_fields_safe oft p = Action ls \<longrightarrow> length ls \<le> 1"
  apply(cases "simple_linux_router_nol12 rt fw p")
    using w2 apply(simp)
    using w1[of "output_iface (routing_table_semantics rt (p_dst p))"] apply(simp)
    apply(drule lr_determ)
    apply(clarsimp)
  done
  show "\<exists>ls. length ls \<le> 1 \<and> OF_same_priority_match3 OF_match_fields_safe oft p = Action ls"
    apply(cases "OF_same_priority_match3 OF_match_fields_safe oft p")
    using notmult apply blast
    using notno   apply blast
    using notub   apply blast
  done
qed

end
