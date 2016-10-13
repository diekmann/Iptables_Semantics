theory Semantics_OpenFlow
imports List_Group Sort_Descending
  "../IP_Addresses/IPv4"
  "OpenFlow_Helpers"
begin

datatype 'a flowtable_behavior = Action 'a | NoAction | Undefined

definition "option_to_ftb b \<equiv> case b of Some a \<Rightarrow> Action a | None \<Rightarrow> NoAction"
definition "ftb_to_option b \<equiv> case b of Action a \<Rightarrow> Some a | NoAction \<Rightarrow> None"

(*section\<open>OpenFlow\<close>*)

(*https://www.opennetworking.org/images/stories/downloads/sdn-resources/onf-specifications/openflow/openflow-switch-v1.5.0.pdf*)

(*"OpenFlow packets are received on an ingress port [...]. The packet ingress port is a property of the packet
throughout the OpenFlow pipeline and represents the OpenFlow port on which the packet was received
into the OpenFlow switch."
*)

(* "Packet forwarded to non-existent ports are just dropped"*)

(*we do not support egress tables (those are optional in the standard).
  we only support flow table 0 (ingress table).
  Essentially, this means, we only support one flow table and no pipelining.
  This corresponds to OpenFlow 1.0.0
*)

(*priority \<times> Match Fields \<times> instructions
 not modeled: counters, timeouts, cookie ("Not used when processing packets"), flags,
     instructions (only an output list of egress ports will be modeled)
*)

datatype ('m, 'a) flow_entry_match = OFEntry (ofe_prio: "16 word") (ofe_fields: "'m set") (ofe_action: 'a)

(* why is there curry *)
find_consts "(('a \<times> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
(* but no "uncurry" *)
find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'c"
(* Anyway, we want this to easily construct OFEntrys from tuples *)
definition "split3 f p \<equiv> case p of (a,b,c) \<Rightarrow> f a b c"
find_consts "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<times> 'b \<times> 'c) \<Rightarrow> 'd"

(*
"If there are multiple matching flow entries with the same highest priority, the selected flow entry is explicitly undefined."
OFP 1.0.0 also stated that non-wildcarded matches implicitly have the highest priority (which is gone in 1.5).
*)
(*Defined None \<longleftrightarrow> No match
  Defined (Some a) \<longleftrightarrow> Match and instruction is a
  Undefined \<longleftrightarrow> Undefined*)

type_synonym ('m, 'a) flowtable = "(('m, 'a) flow_entry_match) list"
type_synonym ('m, 'p) field_matcher = "('m set \<Rightarrow> 'p \<Rightarrow> bool)"

definition OF_same_priority_match2 :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> 'a flowtable_behavior" where
  "OF_same_priority_match2 \<gamma> flow_entries packet \<equiv> let s = 
  	{ofe_action f|f. f \<in> set flow_entries \<and> \<gamma> (ofe_fields f) packet \<and> 
  	  (\<forall>fo \<in> set flow_entries. ofe_prio fo > ofe_prio f \<longrightarrow> \<not>\<gamma> (ofe_fields fo) packet)} in
  	case card s of 0       \<Rightarrow> NoAction
                 | (Suc 0) \<Rightarrow> Action (the_elem s) 
                 | _       \<Rightarrow> Undefined"

(* are there any overlaping rules? *)
definition "check_no_overlap \<gamma> ft = (\<forall>a \<in> set ft. \<forall>b \<in> set ft. \<forall>p \<in> UNIV. (ofe_prio a = ofe_prio b \<and> \<gamma> (ofe_fields a) p \<and> a \<noteq> b) \<longrightarrow> \<not>\<gamma> (ofe_fields b) p)"
definition "check_no_overlap2 \<gamma> ft = (\<forall>a \<in> set ft. \<forall>b \<in> set ft. (a \<noteq> b \<and> ofe_prio a = ofe_prio b) \<longrightarrow> \<not>(\<exists>p \<in> UNIV. \<gamma> (ofe_fields a) p \<and> \<gamma> (ofe_fields b) p))"
lemma check_no_overlap_alt: "check_no_overlap \<gamma> ft = check_no_overlap2 \<gamma> ft"
	unfolding check_no_overlap2_def check_no_overlap_def
	by blast

(* If there are no overlapping rules, our match should check out. *)
lemma no_overlap_not_unefined: "check_no_overlap \<gamma> ft \<Longrightarrow> OF_same_priority_match2 \<gamma> ft p \<noteq> Undefined"
proof
  assume goal1: "check_no_overlap \<gamma> ft" "OF_same_priority_match2 \<gamma> ft p = Undefined"
	let ?as = "{f. f \<in> set ft \<and> \<gamma> (ofe_fields f) p \<and> (\<forall>fo \<in> set ft. ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}"
	have fin: "finite ?as" by simp
	note goal1(2)[unfolded OF_same_priority_match2_def]
	then have "2 \<le> card (ofe_action ` ?as)" unfolding f_Img_ex_set
		unfolding Let_def
		by(cases "card (ofe_action ` ?as)", simp) (rename_tac nat1, case_tac nat1, simp add: image_Collect, presburger)
	then have "2 \<le> card ?as" using card_image_le[OF fin, of ofe_action] by linarith
	then obtain a b where ab: "a \<noteq> b" "a \<in> ?as" "b \<in> ?as" using card2_eI by blast
	then have ab2: "a \<in> set ft" "\<gamma> (ofe_fields a) p" "(\<forall>fo\<in>set ft. ofe_prio a < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" 
	               "b \<in> set ft" "\<gamma> (ofe_fields b) p" "(\<forall>fo\<in>set ft. ofe_prio b < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" by simp_all
	then have "ofe_prio a = ofe_prio b"
		by fastforce
	note goal1(1)[unfolded check_no_overlap_def] ab2(1) ab2(4) this ab2(2) ab(1) ab2(5)
	then show False by blast
qed

fun OF_match_linear :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> 'a flowtable_behavior" where
"OF_match_linear _ [] _ = NoAction" |
"OF_match_linear \<gamma> (a#as) p = (if \<gamma> (ofe_fields a) p then Action (ofe_action a) else OF_match_linear \<gamma> as p)"

lemma OF_match_linear_ne_Undefined: "OF_match_linear \<gamma> ft p \<noteq> Undefined"
	by(induction ft) auto

lemma OF_match_linear_append: "OF_match_linear \<gamma> (a @ b) p = (case OF_match_linear \<gamma> a p of NoAction \<Rightarrow> OF_match_linear \<gamma> b p | x \<Rightarrow> x)"
by(induction a) simp_all
lemma OF_match_linear_match_allsameaction: "\<lbrakk>gr \<in> set oms; \<gamma> gr p = True\<rbrakk>
       \<Longrightarrow> OF_match_linear \<gamma> (map (\<lambda>x. split3 OFEntry (pri, x, act)) oms) p = Action act"
by(induction oms) (auto simp add: split3_def)
lemma OF_lm_noa_none_iff: "OF_match_linear \<gamma> ft p = NoAction \<longleftrightarrow> (\<forall>e\<in>set ft. \<not> \<gamma> (ofe_fields e) p)"
	by(induction ft) (simp_all split: if_splits)

lemma set_eq_rule: "(\<And>x. x \<in> a \<Longrightarrow> x \<in> b) \<Longrightarrow> (\<And>x. x \<in> b \<Longrightarrow> x \<in> a) \<Longrightarrow> a = b" by(rule antisym[OF subsetI subsetI])

lemma unmatching_insert_agnostic: "\<not> \<gamma> (ofe_fields a) p \<Longrightarrow> OF_same_priority_match2 \<gamma> (a # ft) p = OF_same_priority_match2 \<gamma> ft p"
proof -
	let ?as = "{f. f \<in> set ft \<and> \<gamma> (ofe_fields f) p \<and> (\<forall>fo \<in> set ft. ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}"
	let ?aas = "{f |f. f \<in> set (a # ft) \<and> \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}"
	assume nm: "\<not> \<gamma> (ofe_fields a) p" 
	have aa: "?aas = ?as"
	proof(rule set_eq_rule)
	  fix x
		assume "x \<in> {f |f. f \<in> set (a # ft) \<and> \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}"
		hence as: "x \<in> set (a # ft) \<and> \<gamma> (ofe_fields x) p \<and> (\<forall>fo\<in>set (a # ft). ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" by simp
		with nm have "x \<in> set ft" by fastforce
		moreover from as have "(\<forall>fo\<in>set ft. ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" by simp
		ultimately show "x \<in> {f \<in> set ft. \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set ft. ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}" using as by force
	next
	  fix x
		assume "x \<in> {f \<in> set ft. \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set ft. ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}"
		hence as: "x \<in> set ft" "\<gamma> (ofe_fields x) p" "(\<forall>fo\<in>set ft. ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" by simp_all
		from as(1) have "x \<in> set (a # ft)" by simp
		moreover from as(3) have "(\<forall>fo\<in>set (a # ft). ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)" using nm by simp
		ultimately show "x \<in> {f |f. f \<in> set (a # ft) \<and> \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)}" using as(2) by blast
	qed
	note uf = arg_cong[OF aa, of "op ` ofe_action", unfolded image_Collect]
	show ?thesis unfolding OF_same_priority_match2_def using uf by presburger
qed

lemma OF_match_eq: "sorted_descending (map ofe_prio ft) \<Longrightarrow> check_no_overlap \<gamma> ft \<Longrightarrow> 
	OF_same_priority_match2 \<gamma> ft p = OF_match_linear \<gamma> ft p"
proof(induction "ft")
	case (Cons a ft)
	have 1: "sorted_descending (map ofe_prio ft)" using Cons(2) by simp
	have 2: "check_no_overlap \<gamma> ft" using Cons(3) unfolding check_no_overlap_def using set_subset_Cons by fast
	note mIH = Cons(1)[OF 1 2]
	show ?case (is ?kees)
	proof(cases "\<gamma> (ofe_fields a) p")
		case False thus ?kees
			by(simp only: OF_match_linear.simps if_False mIH[symmetric] unmatching_insert_agnostic[of \<gamma>, OF False])
	next
		note sorted_descending_split[OF Cons(2)]
		then obtain m n where mn: "a # ft = m @ n" "\<forall>e\<in>set m. ofe_prio a = ofe_prio e" "\<forall>e\<in>set n. ofe_prio e < ofe_prio a"
			unfolding list.sel by blast 
		hence aem: "a \<in> set m"
			by (metis UnE less_imp_neq list.set_intros(1) set_append)
		have mover: "check_no_overlap \<gamma> m" using Cons(3) unfolding check_no_overlap_def
			by (metis Un_iff mn(1) set_append)
		let ?fc = "(\<lambda>s. 
			{f. f \<in> set s \<and> \<gamma> (ofe_fields f) p \<and> 
			(\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)})"
		case True
		have "?fc (m @ n) = ?fc m \<union> ?fc n" by auto
		moreover have "?fc n = {}"
		proof(rule set_eq_rule, rule ccontr, goal_cases)
			case (1 x)
			hence g1: "x \<in> set n" "\<gamma> (ofe_fields x) p" 
				"(\<forall>fo\<in>set m. ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)"
				"(\<forall>fo\<in>set n. ofe_prio x < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)"
				unfolding mn(1) by(simp_all)
			from g1(1) mn(3) have le: "ofe_prio x < ofe_prio a" by simp
			note le g1(3) aem True
			then show False by blast
		qed simp
		ultimately have cc: "?fc (m @ n) = ?fc m" by blast
		have cm: "?fc m = {a}" (* using Cons(3) *)
		proof -
			have "\<forall>f \<in> set m. (\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)"
				by (metis UnE less_asym mn set_append)
			hence 1: "?fc m = {f \<in> set m. \<gamma> (ofe_fields f) p}" by blast
			show "{f \<in> set m. \<gamma> (ofe_fields f) p \<and> (\<forall>fo\<in>set (a # ft). ofe_prio f < ofe_prio fo \<longrightarrow> \<not> \<gamma> (ofe_fields fo) p)} = {a} " unfolding 1
			proof(rule set_eq_rule, goal_cases fwd bwd)
				case (bwd x)
				have "a \<in> {f \<in> set m. \<gamma> (ofe_fields f) p}" using True aem by simp
				thus ?case using bwd by simp
			next
				case (fwd x) show ?case proof(rule ccontr)
					assume "x \<notin> {a}" hence ne: "x \<noteq> a" by simp
					from fwd have 1: "x \<in> set m" "\<gamma> (ofe_fields x) p" by simp_all
					have 2: "ofe_prio x = ofe_prio a" using 1(1) mn(2) by simp
					show False using 1 ne mover aem True 2 unfolding check_no_overlap_def by blast 
				qed
			qed
		qed
		show ?kees
			unfolding mn(1)
			unfolding OF_same_priority_match2_def
			unfolding f_Img_ex_set
			unfolding cc[unfolded mn(1)]
			unfolding cm[unfolded mn(1)]
			unfolding Let_def
			by(simp only: mn(1)[symmetric] OF_match_linear.simps True if_True, simp)
		qed
qed (simp add: OF_same_priority_match2_def)

lemma overlap_sort_invar[simp]: "check_no_overlap \<gamma> (sort_descending_key k ft) = check_no_overlap \<gamma> ft"
	unfolding check_no_overlap_def
	unfolding sort_descending_set_inv
	..

lemma OF_match_eq2: 
  assumes "check_no_overlap \<gamma> ft"
  shows "OF_same_priority_match2 \<gamma> ft p = OF_match_linear \<gamma> (sort_descending_key ofe_prio ft) p"
proof -
	have "sorted_descending (map ofe_prio (sort_descending_key ofe_prio ft))" by (simp add: sorted_descending_sort_descending_key)
	note ceq = OF_match_eq[OF this, unfolded overlap_sort_invar, OF \<open>check_no_overlap \<gamma> ft\<close>, symmetric]
	show ?thesis 
		unfolding ceq
		unfolding OF_same_priority_match2_def
		unfolding sort_descending_set_inv
		..
qed

(* Just me, thinking about some alternate ways of writing this down. *)
lemma prio_match_matcher_alt: "{f. f \<in> set flow_entries \<and> \<gamma> (ofe_fields f) packet \<and> 
  	  (\<forall>fo \<in> set flow_entries. ofe_prio fo > ofe_prio f \<longrightarrow> \<not>\<gamma> (ofe_fields fo) packet)}
  	  = (
  	  let matching = {f. f \<in> set flow_entries \<and> \<gamma> (ofe_fields f) packet} 
  	  in {f. f \<in> matching \<and> (\<forall>fo \<in> matching. ofe_prio fo \<le> ofe_prio f)}
  	  )"
by(auto simp add: Let_def)
lemma prio_match_matcher_alt2: "(
  	  let matching = {f. f \<in> set flow_entries \<and> \<gamma> (ofe_fields f) packet} 
  	  in {f. f \<in> matching \<and> (\<forall>fo \<in> matching. ofe_prio fo \<le> ofe_prio f)}
  	  ) = set (
  	  let matching = filter (\<lambda>f. \<gamma> (ofe_fields f) packet) flow_entries
  	  in filter (\<lambda>f. \<forall>fo \<in> set matching. ofe_prio fo \<le> ofe_prio f) matching
  	  )"
by(auto simp add: Let_def)

definition OF_priority_match where
  "OF_priority_match \<gamma> flow_entries packet \<equiv> 
  let m  = filter (\<lambda>f. \<gamma> (ofe_fields f) packet) flow_entries;
  	  m' = filter (\<lambda>f. \<forall>fo \<in> set m. ofe_prio fo \<le> ofe_prio f) m in
  	case m' of []  \<Rightarrow> NoAction
             | [s] \<Rightarrow> Action (ofe_action s)
             |  _  \<Rightarrow> Undefined"

definition OF_priority_match_ana where
  "OF_priority_match_ana \<gamma> flow_entries packet \<equiv> 
  let m  = filter (\<lambda>f. \<gamma> (ofe_fields f) packet) flow_entries;
  	  m' = filter (\<lambda>f. \<forall>fo \<in> set m. ofe_prio fo \<le> ofe_prio f) m in
  	case m' of []  \<Rightarrow> NoAction
             | [s] \<Rightarrow> Action s
             |  _  \<Rightarrow> Undefined"

lemma filter_singleton: "[x\<leftarrow>s. f x] = [y] \<Longrightarrow> f y \<and> y \<in> set s" by (metis filter_eq_Cons_iff in_set_conv_decomp) 

lemma OF_spm3_get_fe: "OF_priority_match \<gamma> ft p = Action a \<Longrightarrow> \<exists>fe. ofe_action fe = a \<and> fe \<in> set ft \<and> OF_priority_match_ana \<gamma> ft p = Action fe"
	unfolding OF_priority_match_def OF_priority_match_ana_def
	by(clarsimp split: flowtable_behavior.splits list.splits) (drule filter_singleton; simp)

fun no_overlaps where
"no_overlaps _ [] = True" |
"no_overlaps \<gamma> (a#as) = (no_overlaps \<gamma> as \<and> (
	\<forall>b \<in> set as. ofe_prio a = ofe_prio b \<longrightarrow> \<not>(\<exists>p \<in> UNIV. \<gamma> (ofe_fields a) p \<and> \<gamma> (ofe_fields b) p)))"

lemma no_overlap_ConsI: "check_no_overlap2 \<gamma> (x#xs) \<Longrightarrow> check_no_overlap2 \<gamma> xs"
	unfolding check_no_overlap2_def by simp

lemma no_overlapsI: "check_no_overlap \<gamma> t \<Longrightarrow> distinct t \<Longrightarrow> no_overlaps \<gamma> t"
unfolding check_no_overlap_alt
proof(induction t)
	case (Cons a t)
	from no_overlap_ConsI[OF Cons(2)] Cons(3,1)
	have "no_overlaps \<gamma> t" by simp
	thus ?case using Cons(2,3) unfolding check_no_overlap2_def by auto
qed (simp add: check_no_overlap2_def)

lemma check_no_overlapI: "no_overlaps \<gamma> t \<Longrightarrow> check_no_overlap \<gamma> t"
unfolding check_no_overlap_alt
proof(induction t)
	case (Cons a t)
	from Cons(1)[OF conjunct1[OF Cons(2)[unfolded no_overlaps.simps]]]
	show ?case
		using conjunct2[OF Cons(2)[unfolded no_overlaps.simps]]
		unfolding check_no_overlap2_def
		by auto
qed (simp add: check_no_overlap2_def)

lemma "(\<And>e p. e \<in> set t \<Longrightarrow> \<not>\<gamma> (ofe_fields e) p) \<Longrightarrow> no_overlaps \<gamma> t"
	by(induction t) simp_all
lemma no_overlaps_append: "no_overlaps \<gamma> (x @ y) \<Longrightarrow> no_overlaps \<gamma> y"
	by(induction x) simp_all
lemma no_overlaps_ne1: "no_overlaps \<gamma> (x @ a # y @ b # z) \<Longrightarrow> ((\<exists>p. \<gamma> (ofe_fields a) p) \<or> (\<exists>p. \<gamma> (ofe_fields b) p)) \<Longrightarrow> a \<noteq> b"
proof (rule notI, goal_cases contr)
	case contr
	from contr(1) no_overlaps_append have "no_overlaps \<gamma> (a # y @ b # z)" by blast
	note this[unfolded no_overlaps.simps]
	with contr(3) have "\<not> (\<exists>p\<in>UNIV. \<gamma> (ofe_fields a) p \<and> \<gamma> (ofe_fields b) p)" by simp
	with contr(2) show False unfolding contr(3) by simp
qed

lemma no_overlaps_defeq: "no_overlaps \<gamma> fe \<Longrightarrow> OF_same_priority_match2 \<gamma> fe p = OF_priority_match \<gamma> fe p"
	unfolding OF_same_priority_match2_def OF_priority_match_def 
	unfolding f_Img_ex_set
	unfolding prio_match_matcher_alt
	unfolding prio_match_matcher_alt2
proof (goal_cases uf)
	case uf
	let ?m' = "let m = [f\<leftarrow>fe . \<gamma> (ofe_fields f) p] in [f\<leftarrow>m . \<forall>fo\<in>set m. ofe_prio fo \<le> ofe_prio f]"
	let ?s = "ofe_action ` set ?m'"
	from uf show ?case 
	proof(cases ?m')
		case Nil
		moreover then have "card ?s = 0" by force
		ultimately show ?thesis by(simp add: Let_def)
	next
		case (Cons a as)
		have "as = []"
		proof(rule ccontr)
			assume "as \<noteq> []"
			then obtain b bs where bbs: "as = b # bs" by (meson neq_Nil_conv)
			 note no = Cons[unfolded Let_def filter_filter]
			have f1: "a \<in> set ?m'" "b \<in> set ?m'" unfolding bbs local.Cons by simp_all
			hence "ofe_prio a = ofe_prio b" by (simp add: antisym) 
			moreover have ms: "\<gamma> (ofe_fields a) p" "\<gamma> (ofe_fields b) p" using no[symmetric] unfolding bbs by(blast dest: Cons_eq_filterD)+
			moreover have abis: "a \<in> set fe" "b \<in> set fe" using f1 by auto
			moreover have "a \<noteq> b" proof(cases "\<exists>x y z. fe = x @ a # y @ b # z")
				case True
				then obtain x y z where xyz: "fe = x @ a # y @ b # z" by blast
				from no_overlaps_ne1 ms(1) uf[unfolded xyz]
				show ?thesis by blast
			next
				case False
				then obtain x y z where xyz: "fe = x @ b # y @ a # z"
					using no unfolding bbs
					by (metis (no_types, lifting) Cons_eq_filterD)
				from no_overlaps_ne1 ms(1) uf[unfolded xyz]
				show ?thesis by blast
			qed
			ultimately show False using check_no_overlapI[OF uf, unfolded check_no_overlap_def] by blast
		qed
		then have oe: "a # as = [a]" by simp
		show ?thesis using Cons[unfolded oe] by force
	qed
qed
(* the above lemma used to be this, but it's slightly weaker than I wanted. *)
lemma "distinct fe \<Longrightarrow> check_no_overlap \<gamma> fe \<Longrightarrow> OF_same_priority_match2 \<gamma> fe p = OF_priority_match \<gamma> fe p"
	by(rule no_overlaps_defeq) (drule (2) no_overlapsI)

theorem OF_eq:
	assumes no: "no_overlaps \<gamma> f"
	    and so: "sorted_descending (map ofe_prio f)"
	shows "OF_match_linear \<gamma> f p = OF_priority_match \<gamma> f p"
	unfolding no_overlaps_defeq[symmetric,OF no] OF_match_eq[OF so check_no_overlapI[OF no]]
	..

corollary OF_eq_sort:
	assumes no: "no_overlaps \<gamma> f"
	shows "OF_priority_match \<gamma> f p = OF_match_linear \<gamma> (sort_descending_key ofe_prio f) p"
	using OF_match_eq2 check_no_overlapI no no_overlaps_defeq by fastforce

lemma OF_lm_noa_none: "OF_match_linear \<gamma> ft p = NoAction \<Longrightarrow> \<forall>e\<in>set ft. \<not> \<gamma> (ofe_fields e) p"
	by(induction ft) (simp_all split: if_splits)
	
(* this should be provable without the overlaps assumption, but that's quite a bit harder. *)
lemma OF_spm3_noa_none:
	assumes no: "no_overlaps \<gamma> ft"
	shows "OF_priority_match \<gamma> ft p = NoAction \<Longrightarrow> \<forall>e \<in> set ft. \<not>\<gamma> (ofe_fields e) p"
unfolding OF_eq_sort[OF no] by(drule OF_lm_noa_none) simp

(* repetition of the lemma for definition 2 for definition 3 *)
lemma no_overlaps_not_unefined: "no_overlaps \<gamma> ft \<Longrightarrow> OF_priority_match \<gamma> ft p \<noteq> Undefined"
	using check_no_overlapI no_overlap_not_unefined no_overlaps_defeq by fastforce

end
