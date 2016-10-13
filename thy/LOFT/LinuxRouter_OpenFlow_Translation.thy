theory LinuxRouter_OpenFlow_Translation
imports "../IP_Addresses/CIDR_Split"
  "../Automatic_Refinement/Lib/Misc" (*TODO@Peter: rename and make available at better place :)*)
	"../Simple_Firewall/Generic_SimpleFw" 
	"Semantics_OpenFlow"
	"OpenFlow_Matches"
	"OpenFlow_Action"
	"../Routing/Linux_Router"
begin

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
p_payload :: string
*)

definition "route2match r =
	\<lparr>iiface = ifaceAny, oiface = ifaceAny, 
	src = (0,0), dst=(pfxm_prefix (routing_match r),pfxm_length (routing_match r)), 
	proto=ProtoAny, sports=(0,max_word), ports=(0,max_word)\<rparr>"

definition toprefixmatch where
"toprefixmatch m \<equiv> (let pm = PrefixMatch (fst m) (snd m) in if pm = PrefixMatch 0 0 then None else Some pm)"
lemma prefix_match_semantics_simple_match: 
  assumes some: "toprefixmatch m = Some pm"
	assumes vld: "valid_prefix pm"
	shows "prefix_match_semantics pm = simple_match_ip m"
using some
  by(cases m)
	  (clarsimp 
	   simp add: toprefixmatch_def ipset_from_cidr_def pfxm_mask_def fun_eq_iff
	            prefix_match_semantics_ipset_from_netmask[OF vld] NOT_mask_shifted_lenword[symmetric]
	   split: if_splits)

definition simple_match_to_of_match_single ::
    "(32, 'a) simple_match_scheme
     \<Rightarrow> char list option \<Rightarrow> protocol \<Rightarrow> (16 word \<times> 16 word) option \<Rightarrow> (16 word \<times> 16 word) option \<Rightarrow> of_match_field set" 
    where
"simple_match_to_of_match_single m iif prot sport dport \<equiv>
	   uncurry L4Src ` option2set sport \<union> uncurry L4Dst ` option2set dport
	 \<union> IPv4Proto ` (case prot of ProtoAny \<Rightarrow> {} | Proto p \<Rightarrow> {p}) (* protocol is an 8 word option anyway\<dots> *)
	 \<union> IngressPort ` option2set iif
	 \<union> IPv4Src ` option2set (toprefixmatch (src m)) \<union> IPv4Dst ` option2set (toprefixmatch (dst m))
	 \<union> {EtherType 0x0800}"
(* okay, we need to make sure that no packets are output on the interface they were input on. So for rules that don't have an input interface, we'd need to do a product over all interfaces, if we stay naive.
   The more smart way would be to insert a rule with the same match condition that additionally matches the input interface and drops. However, I'm afraid this is going to be very tricky to verify\<dots> *)
definition simple_match_to_of_match :: "32 simple_match \<Rightarrow> string list \<Rightarrow> of_match_field set list" where
"simple_match_to_of_match m ifs \<equiv> (let
	npm = (\<lambda>p. fst p = 0 \<and> snd p = max_word);
	sb = (\<lambda>p. (if npm p then [None] else if fst p \<le> snd p then map (Some \<circ> (\<lambda>pfx. (pfxm_prefix pfx, NOT pfxm_mask pfx))) (wordinterval_CIDR_split_prefixmatch (WordInterval (fst p) (snd p))) else []))
	in [simple_match_to_of_match_single m iif (proto m) sport dport.
		iif \<leftarrow> (if iiface m = ifaceAny then [None] else [Some i. i \<leftarrow> ifs, match_iface (iiface m) i]),
		sport \<leftarrow> sb (sports m),
		dport \<leftarrow> sb (dports m)]
)"
(* I wonder\<dots> should I check whether list_all (match_iface (iiface m)) ifs instead of iiface m = ifaceAny? It would be pretty stupid if that wasn't the same, but you know\<dots> *)

lemma smtoms_eq_hlp: "simple_match_to_of_match_single r a b c d = simple_match_to_of_match_single r f g h i \<longleftrightarrow> (a = f \<and> b = g \<and> c = h \<and> d = i)"
(* In case this proof breaks: there are two alternate proofs in the repo. They are of similar quality, though. Good luck. *)
proof(rule iffI,goal_cases)
  case 1
  thus ?case proof(intro conjI)
    have *: "\<And>P z x. \<lbrakk>\<forall>x :: of_match_field. P x; z = Some x\<rbrakk> \<Longrightarrow> P (IngressPort x)" by simp
    show "a = f" using 1 by(cases a; cases f)
        (simp add: option2set_None simple_match_to_of_match_single_def toprefixmatch_def option2set_def;
        subst(asm) set_eq_iff; drule (1) *; simp split: option.splits uncurry_splits protocol.splits)+
  next
    have *: "\<And>P z x. \<lbrakk>\<forall>x :: of_match_field. P x; z = Proto x\<rbrakk> \<Longrightarrow> P (IPv4Proto x)" by simp
    show "b = g" using 1 by(cases b; cases g) 
        (simp add: option2set_None simple_match_to_of_match_single_def toprefixmatch_def option2set_def;
        subst(asm) set_eq_iff; drule (1) *; simp split: option.splits uncurry_splits protocol.splits)+
  next
    have *: "\<And>P z x. \<lbrakk>\<forall>x :: of_match_field. P x; z = Some x\<rbrakk> \<Longrightarrow> P (uncurry L4Src x)" by simp
    show "c = h" using 1 by(cases c; cases h)
        (simp add: option2set_None simple_match_to_of_match_single_def toprefixmatch_def option2set_def;
        subst(asm) set_eq_iff; drule (1) *; simp split: option.splits uncurry_splits protocol.splits)+
  next
    have *: "\<And>P z x. \<lbrakk>\<forall>x :: of_match_field. P x; z = Some x\<rbrakk> \<Longrightarrow> P (uncurry L4Dst x)" by simp
    show "d = i" using 1 by(cases d; cases i)
        (simp add: option2set_None simple_match_to_of_match_single_def toprefixmatch_def option2set_def;
        subst(asm) set_eq_iff; drule (1) *; simp split: option.splits uncurry_splits protocol.splits)+
  qed
qed simp

lemma simple_match_to_of_match_generates_prereqs: "simple_match_valid m \<Longrightarrow> r \<in> set (simple_match_to_of_match m ifs) \<Longrightarrow> all_prerequisites r"
unfolding simple_match_to_of_match_def Let_def
proof(clarsimp, goal_cases)
  case (1 xiface xsrcp xdstp)
  note o = this
  show ?case unfolding simple_match_to_of_match_single_def all_prerequisites_def
    unfolding ball_Un
  proof((intro conjI; ((simp;fail)| - )), goal_cases)
    case 1
    have e: "(fst (sports m) = 0 \<and> snd (sports m) = max_word) \<or> proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto L4_Protocol.SCTP"
      using o(1)
      unfolding simple_match_valid_alt Let_def
      by(clarsimp split: if_splits)
    show ?case
      using o(3) e
      by(elim disjE; simp add: option2set_def split: if_splits prod.splits uncurry_splits)
  next
    case 2
    have e: "(fst (dports m) = 0 \<and> snd (dports m) = max_word) \<or> proto m = Proto TCP \<or> proto m = Proto UDP \<or> proto m = Proto L4_Protocol.SCTP"
      using o(1)
      unfolding simple_match_valid_alt Let_def
      by(clarsimp split: if_splits)
    show ?case
      using o(4) e
      by(elim disjE; simp add: option2set_def split: if_splits prod.splits uncurry_splits)
  qed
qed

lemma and_assoc: "a \<and> b \<and> c \<longleftrightarrow> (a \<and> b) \<and> c" by simp

lemmas custom_simpset = Let_def set_concat set_map map_map comp_def concat_map_maps set_maps UN_iff fun_app_def Set.image_iff

abbreviation "simple_fw_prefix_to_wordinterval \<equiv> prefix_to_wordinterval \<circ> uncurry PrefixMatch"

lemma simple_match_port_alt: "simple_match_port m p \<longleftrightarrow> p \<in> wordinterval_to_set (uncurry WordInterval m)" by(simp split: uncurry_splits)

lemma simple_match_src_alt: "simple_match_valid r \<Longrightarrow> 
	simple_match_ip (src r) p \<longleftrightarrow> prefix_match_semantics (PrefixMatch (fst (src r)) (snd (src r))) p"
by(cases "(src r)") (simp add: prefix_match_semantics_ipset_from_netmask2 prefix_to_wordset_ipset_from_cidr simple_match_valid_def valid_prefix_fw_def)
lemma simple_match_dst_alt: "simple_match_valid r \<Longrightarrow> 
	simple_match_ip (dst r) p \<longleftrightarrow> prefix_match_semantics (PrefixMatch (fst (dst r)) (snd (dst r))) p"
by(cases "(dst r)") (simp add: prefix_match_semantics_ipset_from_netmask2 prefix_to_wordset_ipset_from_cidr simple_match_valid_def valid_prefix_fw_def)

lemma "x \<in> set (wordinterval_CIDR_split_prefixmatch w) \<Longrightarrow> valid_prefix x"
using wordinterval_CIDR_split_prefixmatch_all_valid_Ball[THEN bspec, THEN conjunct1] .

lemma simple_match_to_of_matchI: 
	assumes mv: "simple_match_valid r"
	assumes mm: "simple_matches r p"
	assumes ii: "p_iiface p \<in> set ifs"
	assumes ippkt: "p_l2type p = 0x800"
	shows eq: "\<exists>gr \<in> set (simple_match_to_of_match r ifs). OF_match_fields gr p = Some True"
proof -
	let ?npm = "\<lambda>p. fst p = 0 \<and> snd p = max_word"
	let ?sb = "\<lambda>p r. (if ?npm p then None else Some r)"
	obtain si where si: "case si of Some ssi \<Rightarrow> p_sport p \<in> prefix_to_wordset ssi | None \<Rightarrow> True"
		"case si of None \<Rightarrow> True | Some ssi \<Rightarrow> ssi \<in> set (
		wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (sports r)))"
		"si = None \<longleftrightarrow> ?npm (sports r)"
	proof(cases "?npm (sports r)", goal_cases)
		case 1 (* True *)
		hence "(case None of None \<Rightarrow> True | Some ssi \<Rightarrow> p_sport p \<in> prefix_to_wordset ssi) \<and>
            (case None of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (sports r))))" by simp
        with 1 show ?thesis by blast
	next
		case 2 (* False *)
		from mm have "p_sport p \<in> wordinterval_to_set (uncurry WordInterval (sports r))"
			by(simp only: simple_matches.simps simple_match_port_alt)
		then obtain ssi where ssi:
			"ssi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (sports r)))"
			"p_sport p \<in> prefix_to_wordset ssi" 
			using wordinterval_CIDR_split_existential by fast
		hence "(case Some ssi of None \<Rightarrow> True | Some ssi \<Rightarrow> p_sport p \<in> prefix_to_wordset ssi) \<and>
            (case Some ssi of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (sports r))))" by simp
        with 2 show ?thesis by blast
    qed				
	obtain di where di: "case di of Some ddi \<Rightarrow> p_dport p \<in> prefix_to_wordset ddi | None \<Rightarrow> True"
		"case di of None \<Rightarrow> True | Some ddi \<Rightarrow> ddi \<in> set (
		wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (dports r)))"
		"di = None \<longleftrightarrow> ?npm (dports r)"
	proof(cases "?npm (dports r)", goal_cases)
		case 1
		hence "(case None of None \<Rightarrow> True | Some ssi \<Rightarrow> p_dport p \<in> prefix_to_wordset ssi) \<and>
            (case None of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (dports r))))" by simp
        with 1 show ?thesis by blast
	next
		case 2
		from mm have "p_dport p \<in> wordinterval_to_set (uncurry WordInterval (dports r))"
			by(simp only: simple_matches.simps simple_match_port_alt)
		then obtain ddi where ddi:
			"ddi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (dports r)))"
			"p_dport p \<in> prefix_to_wordset ddi" 
			using wordinterval_CIDR_split_existential by fast
		hence "(case Some ddi of None \<Rightarrow> True | Some ssi \<Rightarrow> p_dport p \<in> prefix_to_wordset ssi) \<and>
            (case Some ddi of None \<Rightarrow> True
            | Some ssi \<Rightarrow> ssi \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (dports r))))" by simp
        with 2 show ?thesis by blast
    qed
    show ?thesis
	proof
		let ?mf = "map_option (apsnd (wordNOT \<circ> mask \<circ> op - 16) \<circ> prefix_match_dtor)"
		let ?gr = "simple_match_to_of_match_single r
			(if iiface r = ifaceAny then None else Some (p_iiface p)) 
			(if proto r = ProtoAny then ProtoAny else Proto (p_proto p))
			(?mf si) (?mf di)"
		note mfu = simple_match_port.simps[of "fst (sports r)" "snd (sports r)", unfolded surjective_pairing[of "sports r",symmetric]]
				   simple_match_port.simps[of "fst (dports r)" "snd (dports r)", unfolded surjective_pairing[of "dports r",symmetric]]
		note u = mm[unfolded simple_matches.simps mfu ord_class.atLeastAtMost_iff simple_packet_unext_def simple_packet.simps]
		note of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs]
		from u have ple: "fst (sports r) \<le> snd (sports r)" "fst (dports r) \<le> snd (dports r)" by force+
		show eg: "?gr \<in> set (simple_match_to_of_match r ifs)"
			unfolding simple_match_to_of_match_def
			unfolding custom_simpset
			unfolding smtoms_eq_hlp
			proof(intro bexI, (intro conjI; ((rule refl)?)), goal_cases)
				case 2 thus ?case using ple(2) di
					apply(simp add: pfxm_mask_def prefix_match_dtor_def Set.image_iff 
					           split: option.splits prod.splits uncurry_splits)
					apply(erule bexI[rotated])
					apply(simp split: prefix_match.splits)
				done
			next
				case 3 thus ?case using ple(1) si
					apply(simp add: pfxm_mask_def prefix_match_dtor_def Set.image_iff 
					           split: option.splits prod.splits uncurry_splits)
					apply(erule bexI[rotated])
					apply(simp split: prefix_match.splits)
				done
			next
				case 4 thus ?case
				  using u ii by(clarsimp simp: set_maps split: if_splits)
			next
				case 1 thus ?case using ii u by simp_all (metis match_proto.elims(2))  
			qed
		have dpm: "di = Some (PrefixMatch x1 x2) \<Longrightarrow> p_dport p && ~~ mask (16 - x2) = x1" for x1 x2
    proof -
      have *: "di = Some (PrefixMatch x1 x2) \<Longrightarrow> prefix_match_semantics (the di) (p_dport p) \<Longrightarrow> p_dport p && ~~ mask (16 - x2) = x1"
        by(clarsimp simp: prefix_match_semantics_def pfxm_mask_def word_bw_comms;fail)
      have **: "pfx \<in> set (wordinterval_CIDR_split_prefixmatch ra) \<Longrightarrow> prefix_match_semantics pfx a = (a \<in> prefix_to_wordset pfx)" for pfx ra and a :: "16 word"
        by (fact prefix_match_semantics_wordset[OF wordinterval_CIDR_split_prefixmatch_all_valid_Ball[THEN bspec, THEN conjunct1]])
      have "\<lbrakk>di = Some (PrefixMatch x1 x2); p_dport p \<in> prefix_to_wordset (PrefixMatch x1 x2); PrefixMatch x1 x2 \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (dports r)))\<rbrakk>
             \<Longrightarrow> p_dport p && ~~ mask (16 - x2) = x1"
      using di(1,2)
        using * ** by auto
      thus "di = Some (PrefixMatch x1 x2) \<Longrightarrow> p_dport p && ~~ mask (16 - x2) = x1"  using di(1,2) by auto
    qed
		have spm: "si = Some (PrefixMatch x1 x2) \<Longrightarrow> p_sport p && ~~ mask (16 - x2) = x1" for x1 x2
    using si
    proof -
      have *: "si = Some (PrefixMatch x1 x2) \<Longrightarrow> prefix_match_semantics (the si) (p_sport p) \<Longrightarrow> p_sport p && ~~ mask (16 - x2) = x1"
        by(clarsimp simp: prefix_match_semantics_def pfxm_mask_def word_bw_comms;fail)
      have **: "pfx \<in> set (wordinterval_CIDR_split_prefixmatch ra) \<Longrightarrow> prefix_match_semantics pfx a = (a \<in> prefix_to_wordset pfx)" for pfx ra and a :: "16 word"
        by (fact prefix_match_semantics_wordset[OF wordinterval_CIDR_split_prefixmatch_all_valid_Ball[THEN bspec, THEN conjunct1]])
      have "\<lbrakk>si = Some (PrefixMatch x1 x2); p_sport p \<in> prefix_to_wordset (PrefixMatch x1 x2); PrefixMatch x1 x2 \<in> set (wordinterval_CIDR_split_prefixmatch (uncurry WordInterval (sports r)))\<rbrakk>
             \<Longrightarrow> p_sport p && ~~ mask (16 - x2) = x1"
      using si(1,2)
        using * ** by auto
      thus "si = Some (PrefixMatch x1 x2) \<Longrightarrow> p_sport p && ~~ mask (16 - x2) = x1"  using si(1,2) by auto
    qed
		show "OF_match_fields ?gr p = Some True"
		unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF mv eg]]
		  by(cases si; cases di)
        (simp_all
					add: simple_match_to_of_match_single_def OF_match_fields_unsafe_def spm
					     option2set_def u ippkt prefix_match_dtor_def toprefixmatch_def dpm
					     simple_match_dst_alt[OF mv, symmetric] simple_match_src_alt[OF mv, symmetric]
					split: prefix_match.splits)
	qed
qed

lemma prefix_match_00[simp,intro!]: "prefix_match_semantics (PrefixMatch 0 0) p"
  by (simp add: valid_prefix_def zero_prefix_match_all)

lemma simple_match_to_of_matchD:
	assumes eg: "gr \<in> set (simple_match_to_of_match r ifs)"
	assumes mo: "OF_match_fields gr p = Some True"
	assumes me: "match_iface (oiface r) (p_oiface p)"
	assumes mv: "simple_match_valid r"
	shows "simple_matches r p"
proof -
	from mv have validpfx: 
		"valid_prefix (uncurry PrefixMatch (src r))" "valid_prefix (uncurry PrefixMatch (dst r))"
		"\<And>pm. toprefixmatch (src r) = Some pm \<Longrightarrow> valid_prefix pm"
		"\<And>pm. toprefixmatch (dst r) = Some pm \<Longrightarrow> valid_prefix pm"
		unfolding simple_match_valid_def valid_prefix_fw_def toprefixmatch_def 
		  by(simp_all split: uncurry_splits if_splits)
	from mo have mo: "OF_match_fields_unsafe gr p" 
		unfolding of_safe_unsafe_match_eq[OF simple_match_to_of_match_generates_prereqs[OF mv eg]]
		by simp
	note this[unfolded OF_match_fields_unsafe_def]
	note eg[unfolded simple_match_to_of_match_def simple_match_to_of_match_single_def  custom_simpset option2set_def]
	then guess x ..	moreover from this(2) guess xa ..	moreover from this(2) guess xb ..
	note xx = calculation(1,3) this

  { fix a b xc xa
      fix pp :: "16 word"
	  have "\<lbrakk>pp && ~~ pfxm_mask xc = pfxm_prefix xc\<rbrakk>
              \<Longrightarrow> prefix_match_semantics xc (pp)" for xc
      by(simp add: prefix_match_semantics_def word_bw_comms;fail)
    moreover have "pp \<in> wordinterval_to_set (WordInterval a b) \<Longrightarrow> a \<le> pp \<and> pp \<le> b" by simp
    moreover have "xc \<in> set (wordinterval_CIDR_split_prefixmatch (WordInterval a b)) \<Longrightarrow> pp \<in> prefix_to_wordset xc  \<Longrightarrow> pp \<in> wordinterval_to_set (WordInterval a b)"
			by(subst wordinterval_CIDR_split_prefixmatch) blast
	  moreover have "\<lbrakk>xc \<in> set (wordinterval_CIDR_split_prefixmatch (WordInterval a b)); xa = Some (pfxm_prefix xc, ~~ pfxm_mask xc); prefix_match_semantics xc (pp)\<rbrakk> \<Longrightarrow> pp \<in> prefix_to_wordset xc"
			apply(subst(asm)(1) prefix_match_semantics_wordset)
			apply(erule wordinterval_CIDR_split_prefixmatch_all_valid_Ball[THEN bspec, THEN conjunct1];fail)
			apply assumption
	  done
	  ultimately have "\<lbrakk>xc \<in> set (wordinterval_CIDR_split_prefixmatch (WordInterval a b)); xa = Some (pfxm_prefix xc, ~~ pfxm_mask xc);
               pp && ~~ pfxm_mask xc = pfxm_prefix xc\<rbrakk>
              \<Longrightarrow> a \<le> pp \<and> pp \<le> b"
     by metis
	} note l4port_logic = this

	show ?thesis unfolding simple_matches.simps
	proof(unfold and_assoc, (rule)+)
		show "match_iface (iiface r) (p_iiface p)"
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
		show "match_iface (oiface r) (p_oiface p)" using me .
	next
		show "simple_match_ip (src r) (p_src p)"
			using mo unfolding xx(4) OF_match_fields_unsafe_def toprefixmatch_def
			by(clarsimp
			  simp add: simple_packet_unext_def option2set_def validpfx simple_match_src_alt[OF mv] toprefixmatch_def 
			  split: if_splits)
	next
		show "simple_match_ip (dst r) (p_dst p)"
			using mo unfolding xx(4) OF_match_fields_unsafe_def toprefixmatch_def
			by(clarsimp
			  simp add: simple_packet_unext_def option2set_def validpfx simple_match_dst_alt[OF mv] toprefixmatch_def 
			  split: if_splits)
 	next
		show "match_proto (proto r) (p_proto p)"
			using mo unfolding xx(4) OF_match_fields_unsafe_def
			using xx(1) by(clarsimp 
				simp add: singleton_iff simple_packet_unext_def option2set_def prefix_match_semantics_simple_match ball_Un 
				split: if_splits protocol.splits)
	next
		show "simple_match_port (sports r) (p_sport p)"
			using mo xx(2) unfolding xx(4) OF_match_fields_unsafe_def
			by(cases "sports r") (clarsimp simp add: l4port_logic simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
	next
		show "simple_match_port (dports r) (p_dport p)" 
		  using mo xx(3) unfolding xx(4) OF_match_fields_unsafe_def
			by(cases "dports r") (clarsimp simp add: l4port_logic simple_packet_unext_def option2set_def prefix_match_semantics_simple_match split: if_splits)
    qed
qed

primrec annotate_rlen where
"annotate_rlen [] = []" |
"annotate_rlen (a#as) = (length as, a) # annotate_rlen as"
lemma "annotate_rlen ''asdf'' = [(3, CHR ''a''), (2, CHR ''s''), (1, CHR ''d''), (0, CHR ''f'')]" by simp

lemma fst_annotate_rlen_le: "(k, a) \<in> set (annotate_rlen l) \<Longrightarrow> k < length l"
	by(induction l arbitrary: k; simp; force)

lemma distinct_fst_annotate_rlen: "distinct (map fst (annotate_rlen l))"
	using fst_annotate_rlen_le by(induction l) (simp, fastforce)
lemma distinct_annotate_rlen: "distinct (annotate_rlen l)"
	using distinct_fst_annotate_rlen unfolding distinct_map by blast
lemma in_annotate_rlen: "(a,x) \<in> set (annotate_rlen l) \<Longrightarrow> x \<in> set l" 
  by(induction l) (simp_all, blast)
lemma map_snd_annotate_rlen: "map snd (annotate_rlen l) = l"
  by(induction l) simp_all
lemma "sorted_descending (map fst (annotate_rlen l))"
  by(induction l; clarsimp) (force dest: fst_annotate_rlen_le)
lemma "annotate_rlen l = zip (rev [0..<length l]) l"
  by(induction l; simp) (* It would probably have been better to just use the zip, but oh well\<dots> *)

primrec annotate_rlen_code where
"annotate_rlen_code [] = (0,[])" |
"annotate_rlen_code (a#as) = (case annotate_rlen_code as of (r,aas) \<Rightarrow> (Suc r, (r, a) # aas))"
lemma annotate_rlen_len: "fst (annotate_rlen_code r) = length r"
by(induction r) (clarsimp split: prod.splits)+
lemma annotate_rlen_code[code]: "annotate_rlen s = snd (annotate_rlen_code s)"
proof(induction s)
  case (Cons s ss) thus ?case using annotate_rlen_len[of ss] by(clarsimp split: prod.split)
qed simp

lemma suc2plus_inj_on: "inj_on (of_nat :: nat \<Rightarrow> ('l :: len) word) {0..unat (max_word :: 'l word)}"
proof(rule inj_onI)
   let ?mmw = "(max_word :: 'l word)"
   let ?mstp = "(of_nat :: nat \<Rightarrow> 'l word)"
   fix x y :: nat
   assume "x \<in> {0..unat ?mmw}" "y \<in> {0..unat ?mmw}"
   hence se: "x \<le> unat ?mmw" "y \<le> unat ?mmw" by simp_all
   assume eq: "?mstp x = ?mstp y"
   note f = le_unat_uoi[OF se(1)] le_unat_uoi[OF se(2)]
   show "x = y" using eq le_unat_uoi se by metis
qed

lemma distinct_of_nat_list: (* TODO: Move to CaesarWordLemmaBucket *)
	"distinct l \<Longrightarrow> \<forall>e \<in> set l. e \<le> unat (max_word :: ('l::len) word) \<Longrightarrow> distinct (map (of_nat :: nat \<Rightarrow> 'l word) l)"
proof(induction l)
	let ?mmw = "(max_word :: 'l word)"
	let ?mstp = "(of_nat :: nat \<Rightarrow> 'l word)"
	case (Cons a as)
	have "distinct as" "\<forall>e\<in>set as. e \<le> unat ?mmw" using Cons.prems by simp_all 
	note mIH = Cons.IH[OF this]
	moreover have "?mstp a \<notin> ?mstp ` set as"
	proof 
		have representable_set: "set as \<subseteq> {0..unat ?mmw}" using \<open>\<forall>e\<in>set (a # as). e \<le> unat max_word\<close> by fastforce
		have a_reprbl: "a \<in> {0..unat ?mmw}" using \<open>\<forall>e\<in>set (a # as). e \<le> unat max_word\<close> by simp
		assume "?mstp a \<in> ?mstp ` set as"
		with inj_on_image_mem_iff[OF suc2plus_inj_on a_reprbl representable_set]
		have "a \<in> set as" by simp
		with \<open>distinct (a # as)\<close> show False by simp
	qed
	ultimately show ?case by simp
qed simp

lemma annotate_first_le_hlp:
	"length l < unat (max_word :: ('l :: len) word) \<Longrightarrow> \<forall>e\<in>set (map fst (annotate_rlen l)). e \<le> unat (max_word :: 'l word)"
	by(clarsimp) (meson fst_annotate_rlen_le less_trans nat_less_le)
lemmas distinct_of_prio_hlp = distinct_of_nat_list[OF distinct_fst_annotate_rlen annotate_first_le_hlp]
(* don't need these right now, but maybe later? *)
                                                  
lemma fst_annotate_rlen: "map fst (annotate_rlen l) = rev [0..<length l]"
by(induction l) (simp_all)

lemma sorted_word_upt:
  defines[simp]: "won \<equiv> (of_nat :: nat \<Rightarrow> ('l :: len) word)"
  assumes "length l \<le> unat (max_word :: 'l word)"
  shows "sorted_descending (map won (rev [0..<Suc (length l)]))" 
using assms
  by(induction l rule: rev_induct;clarsimp)
    (metis (mono_tags, hide_lams) le_SucI le_unat_uoi of_nat_Suc order_refl word_le_nat_alt)
    (* This proof is kind of ugly. In case it breaks unfixably, go back to rev a9c4927 and get word_upto.
       The lemmas on word_upto can be used to shows this trivially. *)

lemma sorted_annotated:
	assumes "length l \<le> unat (max_word :: ('l :: len) word)"
	shows "sorted_descending (map fst (map (apfst (of_nat :: nat \<Rightarrow> 'l word)) (annotate_rlen l)))"
proof -
	let ?won = "(of_nat :: nat \<Rightarrow> 'l word)"
	have "sorted_descending (map ?won (rev [0..<Suc (length l)]))" 
		using sorted_word_upt[OF assms] .
	hence "sorted_descending (map ?won (map fst (annotate_rlen l)))" by(simp add: fst_annotate_rlen)
	thus "sorted_descending (map fst (map (apfst ?won) (annotate_rlen l)))" by simp
qed

text\<open>l3 device to l2 forwarding\<close>
definition "lr_of_tran_s3 ifs ard = (
	[(p, b, case a of simple_action.Accept \<Rightarrow> [Forward c] | simple_action.Drop \<Rightarrow> []).
		(p,r,(c,a)) \<leftarrow> ard, b \<leftarrow> simple_match_to_of_match r ifs])"

definition "oif_ne_iif_p1 ifs \<equiv> [(simple_match_any\<lparr>oiface := Iface oi, iiface := Iface ii\<rparr>, simple_action.Accept). oi \<leftarrow> ifs, ii \<leftarrow> ifs, oi \<noteq> ii]"
definition "oif_ne_iif_p2 ifs = [(simple_match_any\<lparr>oiface := Iface i, iiface := Iface i\<rparr>, simple_action.Drop). i \<leftarrow> ifs]"
definition "oif_ne_iif ifs = oif_ne_iif_p2 ifs @ oif_ne_iif_p1 ifs" (* order irrelephant *)
(*value "oif_ne_iif [''a'', ''b'']"*)
(* I first tried something like "oif_ne_iif ifs \<equiv> [(simple_match_any\<lparr>oiface := Iface oi, iiface := Iface ii\<rparr>, if oi = ii then simple_action.Drop else simple_action.Accept). oi \<leftarrow> ifs, ii \<leftarrow> ifs]", 
   but making the statement I wanted with that was really tricky. Much easier to have the second element constant and do it separately. *)
definition "lr_of_tran_s4 ard ifs \<equiv> generalized_fw_join ard (oif_ne_iif ifs)"

definition "lr_of_tran_s1 rt = [(route2match r, output_iface (routing_action r)). r \<leftarrow> rt]"

definition "lr_of_tran_fbs rt fw ifs \<equiv> let
	gfw = map simple_rule_dtor fw; (* generalized simple fw, hopefully for FORWARD *)
	frt = lr_of_tran_s1 rt; (* rt as fw *)
	prd = generalized_fw_join frt gfw
	in prd
"

definition "pack_OF_entries ifs ard \<equiv> (map (split3 OFEntry) (lr_of_tran_s3 ifs ard))"
definition "no_oif_match \<equiv> list_all (\<lambda>m. oiface (match_sel m) = ifaceAny)"

definition "lr_of_tran rt fw ifs \<equiv> 
  if \<not> (no_oif_match fw \<and> has_default_policy fw \<and> simple_fw_valid fw	\<and> valid_prefixes rt \<and> has_default_route rt \<and> distinct ifs)
    then Inl ''Error in creating OpenFlow table: prerequisites not satisifed''
    else (
  let	nrd = lr_of_tran_fbs rt fw ifs;
	ard = map (apfst of_nat) (annotate_rlen nrd) (* give them a priority *)
	in
	if length nrd < unat (max_word :: 16 word)
	then Inr (pack_OF_entries ifs ard)
	else Inl ''Error in creating OpenFlow table: priority number space exhausted'')
"

definition "is_iface_name i \<equiv> i \<noteq> [] \<and> \<not>Iface.iface_name_is_wildcard i"
definition "is_iface_list ifs \<equiv> distinct ifs \<and> list_all is_iface_name ifs"

lemma max_16_word_max[simp]: "(a :: 16 word) \<le> 0xffff"
proof -
	have ffff: "0xffff = word_of_int (2 ^ 16 - 1)" by fastforce
	show ?thesis using max_word_max[of a] unfolding max_word_def ffff by fastforce
qed

lemma replicate_FT_hlp: "x \<le> 16 \<and> y \<le> 16 \<Longrightarrow> replicate (16 - x) False @ replicate x True = replicate (16 - y) False @ replicate y True \<Longrightarrow> x = y"
proof -
	let ?ns = "{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}"
	assume "x \<le> 16 \<and> y \<le> 16"
	hence "x \<in> ?ns" "y \<in> ?ns" by(simp; presburger)+
	moreover assume "replicate (16 - x) False @ replicate x True = replicate (16 - y) False @ replicate y True"
	ultimately show "x = y" by simp (elim disjE; simp_all) (* that's only 289 subgoals after the elim *)
qed

lemma mask_inj_hlp1: "inj_on (mask :: nat \<Rightarrow> 16 word) {0..16}"
proof(intro inj_onI, goal_cases)
  case (1 x y)
  from 1(3)
  have oe: "of_bl (replicate (16 - x) False @ replicate x True) = (of_bl (replicate (16 - y) False @ replicate y True) :: 16 word)"
         unfolding mask_bl of_bl_rep_False .
  have "\<And>z. z \<le> 16 \<Longrightarrow> length (replicate (16 - z) False @ replicate z True) = 16" by auto
  with 1(1,2)
  have ps: "replicate (16 - x) False @ replicate x True \<in> {bl. length bl = len_of TYPE(16)}" " replicate (16 - y) False @ replicate y True \<in> {bl. length bl = len_of TYPE(16)}" by simp_all
  from inj_onD[OF word_bl.Abs_inj_on, OF oe ps]
  show ?case using 1(1,2) by(fastforce intro: replicate_FT_hlp)
qed

lemma distinct_simple_match_to_of_match_portlist_hlp: 
  fixes ps :: "(16 word \<times> 16 word)"
  shows "distinct ifs \<Longrightarrow>
    distinct
     (if fst ps = 0 \<and> snd ps = max_word then [None]
      else if fst ps \<le> snd ps
           then map (Some \<circ> (\<lambda>pfx. (pfxm_prefix pfx, ~~ pfxm_mask pfx)))
                 (wordinterval_CIDR_split_prefixmatch (WordInterval (fst ps) (snd ps)))
           else [])"
proof -
  assume di: "distinct ifs"
  { def wis \<equiv> "set (wordinterval_CIDR_split_prefixmatch (WordInterval (fst ps) (snd ps)))"
    fix x y :: "16 prefix_match"
    obtain xm xn ym yn where xyd[simp]: "x = PrefixMatch xm xn" "y = PrefixMatch ym yn" by(cases x; cases y)
    assume iw: "x \<in> wis" "y \<in> wis" and et: "(pfxm_prefix x, ~~ pfxm_mask x) = (pfxm_prefix y, ~~ pfxm_mask y)"
    hence le16: "xn \<le> 16" "yn \<le> 16" unfolding wis_def using wordinterval_CIDR_split_prefixmatch_all_valid_Ball[unfolded Ball_def, THEN spec, THEN mp] by force+
    with et have "16 - xn = 16 - yn" unfolding pfxm_mask_def by(auto intro: mask_inj_hlp1[THEN inj_onD])
    hence "x = y" using et le16 using diff_diff_cancel by simp
  } note * = this
  show ?thesis 
    apply(clarsimp simp add: smtoms_eq_hlp distinct_map wordinterval_CIDR_split_distinct)
    apply(subst comp_inj_on_iff[symmetric]; intro inj_onI)
  using * by simp_all
qed

lemma distinct_simple_match_to_of_match: "distinct ifs \<Longrightarrow> distinct (simple_match_to_of_match m ifs)"
  apply(unfold simple_match_to_of_match_def Let_def)
  apply(rule distinct_3lcomprI)
  subgoal by(induction ifs; clarsimp)
  subgoal by(fact distinct_simple_match_to_of_match_portlist_hlp)
  subgoal by(fact distinct_simple_match_to_of_match_portlist_hlp)
  subgoal by(simp_all add: smtoms_eq_hlp)
done

lemma inj_inj_on: "inj F \<Longrightarrow> inj_on F A" using subset_inj_on by auto (* TODO: include Word_Lib *)

lemma no_overlaps_lroft_hlp2: "distinct (map fst amr) \<Longrightarrow> (\<And>r. distinct (fm r)) \<Longrightarrow>
    distinct (concat (map (\<lambda>(p, r, c, a). map (\<lambda>b. (p, b, fs a c)) (fm r)) amr))"
  by(induction amr; force intro: injI inj_onI simp add: distinct_map split: prod.splits)

lemma distinct_lroft_s3: "\<lbrakk>distinct (map fst amr); distinct ifs\<rbrakk> \<Longrightarrow> distinct (lr_of_tran_s3 ifs amr)"
  unfolding lr_of_tran_s3_def
  by(erule no_overlaps_lroft_hlp2, simp add: distinct_simple_match_to_of_match)

lemma no_overlaps_lroft_hlp3: "distinct (map fst amr) \<Longrightarrow>
(aa, ab, ac) \<in> set (lr_of_tran_s3 ifs amr) \<Longrightarrow> (ba, bb, bc) \<in> set (lr_of_tran_s3 ifs amr) \<Longrightarrow>
ac \<noteq> bc \<Longrightarrow> aa \<noteq> ba"
  apply(unfold lr_of_tran_s3_def)
  apply(clarsimp)
  apply(clarsimp split: simple_action.splits)
    apply(metis map_of_eq_Some_iff old.prod.inject option.inject)
   apply(metis map_of_eq_Some_iff old.prod.inject option.inject simple_action.distinct(2))+
done

lemma no_overlaps_lroft_s3_hlp_hlp: (* I hlps *)
  "\<lbrakk>distinct (map fst amr); OF_match_fields_unsafe ab p; ab \<noteq> ad \<or> ba \<noteq> bb; OF_match_fields_unsafe ad p;
        (ac, ab, ba) \<in> set (lr_of_tran_s3 ifs amr); (ac, ad, bb) \<in> set (lr_of_tran_s3 ifs amr)\<rbrakk>
       \<Longrightarrow> False"
proof(elim disjE, goal_cases)
  case 1
  have 4: "\<lbrakk>distinct (map fst amr);  (ac, ab, x1, x2) \<in> set amr; (ac, bb, x4, x5) \<in> set amr; ab \<noteq> bb\<rbrakk>
       \<Longrightarrow> False" for ab x1 x2 bb x4 x5
       by (meson distinct_map_fstD old.prod.inject)
  have conjunctSomeProtoAnyD: "Some ProtoAny = simple_proto_conjunct a (Proto b) \<Longrightarrow> False" for a b
    using conjunctProtoD by force
  have 5:
       "\<lbrakk>OF_match_fields_unsafe am p; OF_match_fields_unsafe bm p; am \<noteq> bm; 
        am \<in> set (simple_match_to_of_match ab ifs); bm \<in> set (simple_match_to_of_match bb ifs); \<not> ab \<noteq> bb\<rbrakk>
       \<Longrightarrow> False" for ab bb am bm
      by(clarify | unfold
         simple_match_to_of_match_def smtoms_eq_hlp Let_def set_concat set_map de_Morgan_conj not_False_eq_True)+
        (auto dest: conjunctSomeProtoAnyD cidrsplit_no_overlaps
	            simp add: OF_match_fields_unsafe_def simple_match_to_of_match_single_def option2set_def comp_def
	            split: if_splits
	            cong: smtoms_eq_hlp) (*1min*)
  from 1 show ?case
  using 4 5 by(clarsimp simp add: lr_of_tran_s3_def) blast
qed(metis no_overlaps_lroft_hlp3)


lemma no_overlaps_lroft_s3_hlp: "distinct (map fst amr) \<Longrightarrow> distinct ifs \<Longrightarrow> 
no_overlaps OF_match_fields_unsafe (map (split3 OFEntry) (lr_of_tran_s3 ifs amr))"
  apply(rule no_overlapsI[rotated])
  apply(subst distinct_map, rule conjI)
  subgoal by(erule (1) distinct_lroft_s3)
  subgoal
    apply(rule inj_inj_on)
    apply(rule injI)
    apply(rename_tac x y, case_tac x, case_tac y)
    apply(simp add: split3_def;fail)
  done
  subgoal
    apply(unfold check_no_overlap_def)
    apply(clarify)
    apply(unfold set_map)
    apply(clarify)
    apply(unfold split3_def prod.simps flow_entry_match.simps flow_entry_match.sel de_Morgan_conj)
    apply(clarsimp simp only:)
    apply(erule (1) no_overlaps_lroft_s3_hlp_hlp)
       apply simp
      apply assumption
     apply assumption
    apply simp
  done
done

lemma lr_of_tran_no_overlaps: assumes "distinct ifs" shows "Inr t = (lr_of_tran rt fw ifs) \<Longrightarrow> no_overlaps OF_match_fields_unsafe t"
	apply(unfold lr_of_tran_def Let_def pack_OF_entries_def)
	apply(simp split: if_splits)
	apply(thin_tac "t = _")
	apply(drule distinct_of_prio_hlp)
	apply(rule no_overlaps_lroft_s3_hlp[rotated])
	subgoal by(simp add: assms)
	subgoal by(simp add: o_assoc)
done

lemma sorted_lr_of_tran_s3_hlp: "\<forall>x\<in>set f. fst x \<le> a \<Longrightarrow> b \<in> set (lr_of_tran_s3 s f) \<Longrightarrow> fst b \<le> a" 
	by(auto simp add: lr_of_tran_s3_def)

lemma lr_of_tran_s3_Cons: "lr_of_tran_s3 ifs (a#ard) = (
	[(p, b, case a of simple_action.Accept \<Rightarrow> [Forward c] | simple_action.Drop \<Rightarrow> []).
		(p,r,(c,a)) \<leftarrow> [a], b \<leftarrow> simple_match_to_of_match r ifs]) @ lr_of_tran_s3 ifs ard"
	by(clarsimp simp: lr_of_tran_s3_def)

lemma sorted_lr_of_tran_s3: "sorted_descending (map fst f) \<Longrightarrow> sorted_descending (map fst (lr_of_tran_s3 s f))"
	apply(induction f)
	 subgoal by(simp add: lr_of_tran_s3_def)
	apply(clarsimp simp: lr_of_tran_s3_Cons map_concat comp_def)
	apply(unfold sorted_descending_append)
	apply(simp add: sorted_descending_alt rev_map sorted_lr_of_tran_s3_hlp sorted_const)
done

lemma sorted_lr_of_tran_hlp: "(ofe_prio \<circ> split3 OFEntry) = fst" by(simp add: fun_eq_iff comp_def split3_def)

lemma lr_of_tran_sorted_descending: "Inr r = lr_of_tran rt fw ifs \<Longrightarrow> sorted_descending (map ofe_prio r)"
	apply(unfold lr_of_tran_def Let_def)
	apply(simp split: if_splits)
	apply(thin_tac "r = _")
	apply(unfold sorted_lr_of_tran_hlp pack_OF_entries_def split3_def[abs_def] fun_app_def map_map comp_def prod.case_distrib)
	apply(simp add: fst_def[symmetric])
	apply(rule sorted_lr_of_tran_s3)
	apply(drule sorted_annotated[OF less_or_eq_imp_le, OF disjI1])
	apply(simp add: o_assoc)
done

lemma lr_of_tran_s1_split: "lr_of_tran_s1 (a # rt) = (route2match a, output_iface (routing_action a)) # lr_of_tran_s1 rt"
	by(unfold lr_of_tran_s1_def list.map, rule)

lemma route2match_correct: "valid_prefix (routing_match a) \<Longrightarrow> prefix_match_semantics (routing_match a) (p_dst p) \<longleftrightarrow> simple_matches (route2match a) (p)"
by(simp add: route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipset_from_cidr_0 prefix_match_semantics_ipset_from_netmask2)

lemma s1_correct: "valid_prefixes rt \<Longrightarrow> has_default_route (rt::('i::len) prefix_routing) \<Longrightarrow> 
  \<exists>rm ra. generalized_sfw (lr_of_tran_s1 rt) p = Some (rm,ra) \<and> ra = output_iface (routing_table_semantics rt (p_dst p))"
	apply(induction rt)
	 apply(simp;fail)
	apply(drule valid_prefixes_split)
	apply(clarsimp)
	apply(erule disjE)
	subgoal for a rt
	 apply(case_tac a)
	 apply(rename_tac routing_m metric routing_action)
	 apply(case_tac routing_m)
	 apply(simp add: valid_prefix_def pfxm_mask_def prefix_match_semantics_def generalized_sfw_def 
	       lr_of_tran_s1_def route2match_def simple_matches.simps match_ifaceAny match_iface_refl ipset_from_cidr_0
	       max_word_mask[where 'a = 'i, symmetric, simplified])
	done
	subgoal
    apply(rule conjI)
     apply(simp add: generalized_sfw_def lr_of_tran_s1_def route2match_correct;fail)
    apply(simp add: route2match_def simple_matches.simps prefix_match_semantics_ipset_from_netmask2 
                    lr_of_tran_s1_split generalized_sfw_simps)
  done
done

definition "to_OF_action a \<equiv> (case a of (p,d) \<Rightarrow> (case d of simple_action.Accept \<Rightarrow> [Forward p] | simple_action.Drop \<Rightarrow> []))"
definition "from_OF_action a = (case a of [] \<Rightarrow> ('''',simple_action.Drop) | [Forward p] \<Rightarrow> (p, simple_action.Accept))"

lemma OF_match_linear_not_noD: "OF_match_linear \<gamma> oms p \<noteq> NoAction \<Longrightarrow> \<exists>ome. ome \<in> set oms \<and> \<gamma> (ofe_fields ome) p"
	apply(induction oms)
	 apply(simp)
	apply(simp split: if_splits)
	 apply blast+
done

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
      apply(simp;fail)+
  using simple_match_to_of_match_generates_prereqs by blast

lemma s3_correct:
	assumes vsfwm: "list_all simple_match_valid (map (fst \<circ> snd) ard)"
	assumes ippkt: "p_l2type p = 0x800"
	assumes iiifs: "p_iiface p \<in> set ifs"
	assumes oiifs: "list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) ard"
	shows "OF_match_linear OF_match_fields_safe (pack_OF_entries ifs ard) p = Action ao \<longleftrightarrow> (\<exists>r af. generalized_sfw (map snd ard) p = (Some (r,af)) \<and> (if snd af = simple_action.Drop then ao = [] else ao = [Forward (fst af)]))"
unfolding pack_OF_entries_def lr_of_tran_s3_def fun_app_def
using vsfwm oiifs
  apply(induction ard)
   subgoal by(simp add: generalized_sfw_simps)
  apply simp
  apply(clarsimp simp add: generalized_sfw_simps split: prod.splits)
  apply(intro conjI) (* make two subgoals from one *)
   subgoal for ard x1 ac ad ba
    apply(clarsimp simp add: OF_match_linear_append split: prod.splits)
    apply(drule simple_match_to_of_matchI[rotated])
       apply(rule iiifs)
      apply(rule ippkt)
     apply blast
    apply(clarsimp simp add: comp_def)
    apply(drule 
       OF_match_linear_match_allsameaction[where
         \<gamma>=OF_match_fields_safe and pri = x1 and
         oms = "simple_match_to_of_match ac ifs" and 
         act = "case ba of simple_action.Accept \<Rightarrow> [Forward ad] | simple_action.Drop \<Rightarrow> []"])
     apply(unfold OF_match_fields_safe_def comp_def)
     apply(erule Some_to_the[symmetric];fail)
    apply(clarsimp)
    apply(intro iffI)
    subgoal
     apply(rule exI[where x = ac])
     apply(rule exI[where x = ad])
     apply(rule exI[where x = ba])
     apply(clarsimp simp: split3_def split: simple_action.splits flowtable_behavior.splits if_splits)
    done
    subgoal
     apply(clarsimp)
     apply(rename_tac b)
     apply(case_tac b)
     apply(simp_all)
   done
  done
  subgoal for ard x1 ac ad ba
   apply(simp add: OF_match_linear_append OF_match_fields_safe_def comp_def)
   apply(clarify)
   apply(subgoal_tac "OF_match_linear OF_match_fields_safe (map (\<lambda>x. split3 OFEntry (x1, x, case ba of simple_action.Accept \<Rightarrow> [Forward ad] | simple_action.Drop \<Rightarrow> [])) (simple_match_to_of_match ac ifs)) p = NoAction")
    apply(simp;fail)
   apply(erule (1) s3_noaction_hlp)
   apply(simp add: match_ifaceAny;fail)
  done
done

context
  notes valid_prefix_00[simp, intro!]
begin
  lemma lr_of_tran_s1_valid: "valid_prefixes rt \<Longrightarrow> gsfw_valid (lr_of_tran_s1 rt)"
    unfolding lr_of_tran_s1_def route2match_def gsfw_valid_def list_all_iff
    apply(clarsimp simp: simple_match_valid_def valid_prefix_fw_def)
    apply(intro conjI)
     apply force
    apply(simp add: valid_prefixes_alt_def)
  done
end

lemma simple_match_valid_fbs_rlen: "\<lbrakk>valid_prefixes rt; simple_fw_valid fw; (a, aa, ab, b) \<in> set (annotate_rlen (lr_of_tran_fbs rt fw ifs))\<rbrakk> \<Longrightarrow> simple_match_valid aa"
proof(goal_cases)
  case 1
  note 1[unfolded lr_of_tran_fbs_def Let_def]
  have "gsfw_valid (map simple_rule_dtor fw)" using gsfw_validI 1 by blast
  moreover have "gsfw_valid (lr_of_tran_s1 rt)" using 1 lr_of_tran_s1_valid by blast
  ultimately have "gsfw_valid (generalized_fw_join (lr_of_tran_s1 rt) (map simple_rule_dtor fw))" using gsfw_join_valid by blast
  moreover have "(aa, ab, b) \<in> set (lr_of_tran_fbs rt fw ifs)" using 1 using in_annotate_rlen by fast
  ultimately show ?thesis unfolding lr_of_tran_fbs_def Let_def gsfw_valid_def list_all_iff by fastforce
qed

lemma simple_match_valid_fbs: "\<lbrakk>valid_prefixes rt; simple_fw_valid fw\<rbrakk> \<Longrightarrow> list_all simple_match_valid (map fst (lr_of_tran_fbs rt fw ifs))"
proof(goal_cases)
  case 1
  note 1[unfolded lr_of_tran_fbs_def Let_def]
  have "gsfw_valid (map simple_rule_dtor fw)" using gsfw_validI 1 by blast
  moreover have "gsfw_valid (lr_of_tran_s1 rt)" using 1 lr_of_tran_s1_valid by blast
  ultimately have "gsfw_valid (generalized_fw_join (lr_of_tran_s1 rt) (map simple_rule_dtor fw))" using gsfw_join_valid by blast
  thus ?thesis unfolding lr_of_tran_fbs_def Let_def gsfw_valid_def list_all_iff by fastforce
qed

lemma lr_of_tran_prereqs: "valid_prefixes rt \<Longrightarrow> simple_fw_valid fw \<Longrightarrow> lr_of_tran rt fw ifs = Inr oft \<Longrightarrow>
list_all (all_prerequisites \<circ> ofe_fields) oft"
unfolding lr_of_tran_def pack_OF_entries_def lr_of_tran_s3_def Let_def
  apply(simp add: map_concat comp_def prod.case_distrib split3_def split: if_splits)
  apply(simp add: list_all_iff)
  apply(clarsimp)
  apply(drule simple_match_valid_fbs_rlen[rotated])
    apply(simp add: list_all_iff;fail)
   apply(simp add: list_all_iff;fail)
  apply(rule simple_match_to_of_match_generates_prereqs; assumption)
done

(* TODO: move. where? *)
lemma OF_unsafe_safe_match3_eq: "
  list_all (all_prerequisites \<circ> ofe_fields) oft \<Longrightarrow>
  OF_priority_match OF_match_fields_unsafe oft = OF_priority_match OF_match_fields_safe oft"
unfolding OF_priority_match_def[abs_def]
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

lemma map_snd_apfst: "map snd (map (apfst x) l) = map snd l"
  unfolding map_map comp_def snd_apfst ..

lemma match_ifaceAny_eq: "oiface m = ifaceAny \<Longrightarrow> simple_matches m p = simple_matches m (p\<lparr>p_oiface := any\<rparr>)"
by(cases m) (simp add: simple_matches.simps match_ifaceAny)
lemma no_oif_matchD: "no_oif_match fw \<Longrightarrow> simple_fw fw p = simple_fw fw (p\<lparr>p_oiface := any\<rparr>)"
  by(induction fw)
    (auto simp add: no_oif_match_def simple_fw_alt dest: match_ifaceAny_eq)

lemma lr_of_tran_fbs_acceptD:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw"
  shows "generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Accept) \<Longrightarrow>
  simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>)"
proof(goal_cases)
  case 1
  note 1[unfolded lr_of_tran_fbs_def Let_def, THEN generalized_fw_joinD]
  then guess r1 .. then guess r2 .. note r12 = this
  note s1_correct[OF s1, of p]
  then guess rm .. then guess ra .. note rmra = this
  from r12 rmra have oifra: "oif = ra" by simp
  from r12 have sfw: "simple_fw fw p = Decision FinalAllow" using simple_fw_iff_generalized_fw_accept by blast
  note ifupdateirrel = no_oif_matchD[OF s2, where any = " output_iface (routing_table_semantics rt (p_dst p))" and p = p, symmetric]
  show ?case unfolding simple_linux_router_nol12_def by(simp add: Let_def ifupdateirrel sfw oifra rmra split: Option.bind_splits option.splits) 
qed

lemma lr_of_tran_fbs_acceptI:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw" "has_default_policy fw"
  shows "simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) \<Longrightarrow>
  \<exists>r. generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Accept)"
proof(goal_cases)
  from s2 have nud: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy state.distinct(1))
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1 have "simple_fw fw p = Decision FinalAllow" by(simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  then obtain r where r: "generalized_sfw (map simple_rule_dtor fw) p = Some (r, simple_action.Accept)" using simple_fw_iff_generalized_fw_accept by blast
  have oif_def: "oif = output_iface (routing_table_semantics rt (p_dst p))" using 1 by(cases p) (simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  note s1_correct[OF s1, of p] then guess rm .. then guess ra .. note rmra = this
  show ?case unfolding lr_of_tran_fbs_def Let_def
    apply(rule exI)
    apply(rule generalized_fw_joinI)
    unfolding oif_def using rmra apply simp
    apply(rule r)
  done
qed

lemma lr_of_tran_fbs_dropD:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw"
  shows "generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop) \<Longrightarrow>
  simple_linux_router_nol12 rt fw p = None"
proof(goal_cases)
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1[unfolded lr_of_tran_fbs_def Let_def, THEN generalized_fw_joinD]
  obtain rr fr where "generalized_sfw (lr_of_tran_s1 rt) p = Some (rr, oif) \<and>
          generalized_sfw (map simple_rule_dtor fw) p = Some (fr, simple_action.Drop) \<and> Some r = simple_match_and rr fr" by presburger
  hence fd: "\<And>u. simple_fw fw (p\<lparr>p_oiface := u\<rparr>) = Decision FinalDeny" unfolding ifupdateirrel
  using simple_fw_iff_generalized_fw_drop by blast
  show ?thesis
    by(clarsimp simp: simple_linux_router_nol12_def Let_def fd split: Option.bind_splits)
qed

lemma lr_of_tran_fbs_dropI:
  assumes s1: "valid_prefixes rt" "has_default_route rt"
  assumes s2: "no_oif_match fw" "has_default_policy fw"
  shows "simple_linux_router_nol12 rt fw p = None \<Longrightarrow>
  \<exists>r oif. generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)"
proof(goal_cases)
  from s2 have nud: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy state.distinct(1))
  note ifupdateirrel = no_oif_matchD[OF s2(1), symmetric]
  case 1
  from 1 have "simple_fw fw p = Decision FinalDeny" by(simp add: simple_linux_router_nol12_def Let_def nud ifupdateirrel split: Option.bind_splits state.splits final_decision.splits)
  then obtain r where r: "generalized_sfw (map simple_rule_dtor fw) p = Some (r, simple_action.Drop)" using simple_fw_iff_generalized_fw_drop by blast
  note s1_correct[OF s1, of p] then guess rm .. then guess ra .. note rmra = this
  show ?case unfolding lr_of_tran_fbs_def Let_def
    apply(rule exI)
    apply(rule exI[where x = ra])
    apply(rule generalized_fw_joinI)
    using rmra apply simp
    apply(rule r)
  done
qed


lemma no_oif_match_fbs:
 "no_oif_match fw \<Longrightarrow> list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) (map (apfst of_nat) (annotate_rlen (lr_of_tran_fbs rt fw ifs)))"
proof(goal_cases)
  case 1
  have c: "\<And>mr ar mf af f a. \<lbrakk>(mr, ar) \<in> set (lr_of_tran_s1 rt); (mf, af) \<in> simple_rule_dtor ` set fw; simple_match_and mr mf = Some a\<rbrakk> \<Longrightarrow> oiface a = ifaceAny"
  proof(goal_cases)
    case (1 mr ar mf af f a)
    have "oiface mr = ifaceAny" using 1(1) unfolding lr_of_tran_s1_def route2match_def by(clarsimp simp add: Set.image_iff)
    moreover have "oiface mf = ifaceAny" using 1(2) \<open>no_oif_match fw\<close> unfolding no_oif_match_def simple_rule_dtor_def[abs_def]
      by(clarsimp simp: list_all_iff split: simple_rule.splits) fastforce 
    ultimately show ?case using 1(3) by(cases a; cases mr; cases mf) (simp add: iface_conjunct_ifaceAny split: option.splits)
  qed
  have la: "list_all (\<lambda>m. oiface (fst m) = ifaceAny) (lr_of_tran_fbs rt fw ifs)"
    unfolding lr_of_tran_fbs_def Let_def list_all_iff
    apply(clarify)
    apply(subst(asm) generalized_sfw_join_set)
    apply(clarsimp)
  using c by blast
  thus ?case
  proof(goal_cases)
    case 1
    have *: "(\<lambda>m. oiface (fst (snd m)) = ifaceAny) = (\<lambda>m. oiface (fst m) = ifaceAny) \<circ> snd" unfolding comp_def ..
    show ?case unfolding * list_all_map[symmetric] map_snd_apfst map_snd_annotate_rlen using la .
  qed
qed


lemma lr_of_tran_correct:
	fixes p :: "(32, 'a) simple_packet_ext_scheme"
assumes nerr: "lr_of_tran rt fw ifs = Inr oft"
	 and ippkt: "p_l2type p = 0x800"
	 and ifvld: "p_iiface p \<in> set ifs"
	shows "OF_priority_match OF_match_fields_safe oft p = Action [Forward oif] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = (Some (p\<lparr>p_oiface := oif\<rparr>))"
	      "OF_priority_match OF_match_fields_safe oft p = Action [] \<longleftrightarrow> simple_linux_router_nol12 rt fw p = None"
	      (* fun stuff: *)
	      "OF_priority_match OF_match_fields_safe oft p \<noteq> NoAction" "OF_priority_match OF_match_fields_safe oft p \<noteq> Undefined"
	      "OF_priority_match OF_match_fields_safe oft p = Action ls \<longrightarrow> length ls \<le> 1"
	      "\<exists>ls. length ls \<le> 1 \<and> OF_priority_match OF_match_fields_safe oft p = Action ls"
proof -
	have s1: "valid_prefixes rt" "has_default_route rt" 
   and s2: "has_default_policy fw" "simple_fw_valid fw" "no_oif_match fw"
   and difs: "distinct ifs"
	  using nerr unfolding lr_of_tran_def by(simp_all split: if_splits)
  have "no_oif_match fw" using nerr unfolding lr_of_tran_def by(simp split: if_splits)
  note s2 = s2 this
  have unsafe_safe_eq: 
    "OF_priority_match OF_match_fields_unsafe oft = OF_priority_match OF_match_fields_safe oft"
    "OF_match_linear OF_match_fields_unsafe oft = OF_match_linear OF_match_fields_safe oft"
    apply(subst OF_unsafe_safe_match3_eq; (rule lr_of_tran_prereqs s1 s2 nerr refl)+)
    apply(subst OF_unsafe_safe_match_linear_eq; (rule lr_of_tran_prereqs s1 s2 nerr refl)+)
  done
  have lin: "OF_priority_match OF_match_fields_safe oft = OF_match_linear OF_match_fields_safe oft"
    using OF_eq[OF lr_of_tran_no_overlaps lr_of_tran_sorted_descending, OF difs nerr[symmetric] nerr[symmetric]] unfolding fun_eq_iff unsafe_safe_eq by metis
  let ?ard = "map (apfst of_nat) (annotate_rlen (lr_of_tran_fbs rt fw ifs))"
  have oft_def: "oft = pack_OF_entries ifs ?ard" using nerr unfolding lr_of_tran_def Let_def by(simp split: if_splits)
  have vld: "list_all simple_match_valid (map (fst \<circ> snd) ?ard)"
    unfolding fun_app_def map_map[symmetric] snd_apfst map_snd_apfst map_snd_annotate_rlen using simple_match_valid_fbs[OF s1(1) s2(2)] .
  have *: "list_all (\<lambda>m. oiface (fst (snd m)) = ifaceAny) ?ard" using no_oif_match_fbs[OF s2(3)] .
  have not_undec: "\<And>p. simple_fw fw p \<noteq> Undecided" by (metis has_default_policy s2(1) state.simps(3))
  have w1_1: "\<And>oif. OF_match_linear OF_match_fields_safe oft p = Action [Forward oif] \<Longrightarrow> simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) 
    \<and> oif = output_iface (routing_table_semantics rt (p_dst p))"
  proof(intro conjI, goal_cases)
    case (1 oif)
    note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD1, unfolded oft_def[symmetric], OF 1]
    hence "\<exists>r. generalized_sfw (map snd (map (apfst of_nat) (annotate_rlen (lr_of_tran_fbs rt fw ifs)))) p = Some (r, (oif, simple_action.Accept))"
      by(clarsimp split: if_splits)
    then obtain r where "generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, (oif, simple_action.Accept))" 
      unfolding map_map comp_def snd_apfst map_snd_annotate_rlen by blast
    thus ?case using lr_of_tran_fbs_acceptD[OF s1 s2(3)] by metis
    thus "oif = output_iface (routing_table_semantics rt (p_dst p))"
      by(cases p) (clarsimp simp: simple_linux_router_nol12_def Let_def not_undec split: Option.bind_splits state.splits final_decision.splits) 
  qed
  have w1_2: "\<And>oif. simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>) \<Longrightarrow> OF_match_linear OF_match_fields_safe oft p = Action [Forward oif]"
  proof(goal_cases)
    case (1 oif)
    note lr_of_tran_fbs_acceptI[OF s1 s2(3) s2(1) this, of ifs] then guess r .. note r = this
    hence "generalized_sfw (map snd (map (apfst of_nat) (annotate_rlen (lr_of_tran_fbs rt fw ifs)))) p = Some (r, (oif, simple_action.Accept))" 
    unfolding map_snd_apfst map_snd_annotate_rlen .
    moreover note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD2, unfolded oft_def[symmetric], of "[Forward oif]"]
    ultimately show ?case by simp
  qed
  show w1: "\<And>oif. (OF_priority_match OF_match_fields_safe oft p = Action [Forward oif]) = (simple_linux_router_nol12 rt fw p = Some (p\<lparr>p_oiface := oif\<rparr>))"
    unfolding lin using w1_1 w1_2 by blast
  show w2: "(OF_priority_match OF_match_fields_safe oft p = Action []) = (simple_linux_router_nol12 rt fw p = None)"
  unfolding lin
  proof(rule iffI, goal_cases)
    case 1
    note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD1, unfolded oft_def[symmetric], OF 1]
    then obtain r oif where roif: "generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)"
      unfolding map_snd_apfst map_snd_annotate_rlen by(clarsimp split: if_splits)
    note lr_of_tran_fbs_dropD[OF s1 s2(3) this]
    thus ?case .
  next
    case 2 
    note lr_of_tran_fbs_dropI[OF s1 s2(3) s2(1) this, of ifs] then 
    obtain r oif where "generalized_sfw (lr_of_tran_fbs rt fw ifs) p = Some (r, oif, simple_action.Drop)" by blast
    hence "generalized_sfw (map snd (map (apfst of_nat) (annotate_rlen (lr_of_tran_fbs rt fw ifs)))) p = Some (r, oif, simple_action.Drop)" 
      unfolding map_snd_apfst map_snd_annotate_rlen .
    moreover note s3_correct[OF vld ippkt ifvld(1) *, THEN iffD2, unfolded oft_def[symmetric], of "[]"]
    ultimately show ?case by force
  qed
  have lr_determ: "\<And>a. simple_linux_router_nol12 rt fw p = Some a \<Longrightarrow> a = p\<lparr>p_oiface := output_iface (routing_table_semantics rt (p_dst p))\<rparr>"
    by(clarsimp simp: simple_linux_router_nol12_def Let_def not_undec split: Option.bind_splits state.splits final_decision.splits)
  show notno: "OF_priority_match OF_match_fields_safe oft p \<noteq> NoAction"
    apply(cases "simple_linux_router_nol12 rt fw p")
    using w2 apply(simp)
    using w1[of "output_iface (routing_table_semantics rt (p_dst p))"] apply(simp)
    apply(drule lr_determ)
    apply(simp)
  done
  show notub: "OF_priority_match OF_match_fields_safe oft p \<noteq> Undefined" unfolding lin using OF_match_linear_ne_Undefined .
  show notmult: "\<And>ls. OF_priority_match OF_match_fields_safe oft p = Action ls \<longrightarrow> length ls \<le> 1"
  apply(cases "simple_linux_router_nol12 rt fw p")
    using w2 apply(simp)
    using w1[of "output_iface (routing_table_semantics rt (p_dst p))"] apply(simp)
    apply(drule lr_determ)
    apply(clarsimp)
  done
  show "\<exists>ls. length ls \<le> 1 \<and> OF_priority_match OF_match_fields_safe oft p = Action ls"
    apply(cases "OF_priority_match OF_match_fields_safe oft p")
    using notmult apply blast
    using notno   apply blast
    using notub   apply blast
  done
qed

end
