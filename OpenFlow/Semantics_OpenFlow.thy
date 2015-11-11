theory Semantics_OpenFlow
imports List_Group Sort_Descending
  "../Bitmagic/IPv4Addr"
begin

datatype 'a undefined_behavior = Defined 'a | Undefined

section{*OpenFlow*}

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

datatype 'm match_fields = MatchFields (match_fields_sel: "'m set")

(*TODO: probably don't have an 'm set but just a record?*)

(*priority \<times> Match Fields \<times> instructions
 not modeled: counters, timeouts, cookie ("Not used when processing packets"), flags,
     instructions (only an output list of egress ports will be modeled)
*)
type_synonym ('m, 'a) flow_entry_match="nat \<times> 'm match_fields \<times> 'a"


(*the packet also contains the ingress port*)
definition OF_match :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> 'm match_fields \<Rightarrow> 'p \<Rightarrow> bool" where
  "OF_match \<gamma> match_fields packet \<equiv> \<forall> field \<in> match_fields_sel match_fields. \<gamma> field packet"


(*
"If there are multiple matching flow entries with the same highest priority, the selected flow entry is explicitly undefined."
OFP 1.0.0 also stated that non-wildcarded matches implicitly have the highest priority (which is gone in 1.5).
*)
(*Defined None \<longleftrightarrow> No match
  Defined (Some a) \<longleftrightarrow> Match and instruction is a
  Undefined \<longleftrightarrow> Undefined*)
definition OF_same_priority_match :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m match_fields \<times> 'a) list \<Rightarrow> 'p \<Rightarrow> ('a option) undefined_behavior" where
  "OF_same_priority_match \<gamma> flow_entries packet \<equiv> case [(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m packet] of [] \<Rightarrow> Defined None
                            | [(_, action)] \<Rightarrow> Defined (Some action)
                            | _ \<Rightarrow> Undefined "

definition "snd3 \<equiv> fst \<circ> snd"
definition "trd \<equiv> snd \<circ> snd"
lemmas[simp] = snd3_def trd_def

type_synonym ('m, 'a) flowtable = "(('m, 'a) flow_entry_match) list"
type_synonym ('m, 'p) field_matcher = "('m \<Rightarrow> 'p \<Rightarrow> bool)"

definition OF_same_priority_match2 :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> ('a option) undefined_behavior" where
  "OF_same_priority_match2 \<gamma> flow_entries packet \<equiv> let s = {trd f|f. f \<in> set flow_entries \<and> OF_match \<gamma> (snd3 f) packet \<and> (\<forall>fo \<in> set flow_entries. fst fo > fst f \<longrightarrow> \<not>OF_match \<gamma> (snd3 fo) packet)} in
  	case card s of 0       \<Rightarrow> Defined None
                 | (Suc 0) \<Rightarrow> Defined (Some (the_elem s)) 
                 | _       \<Rightarrow> Undefined "

(* are there any overlaping rules? *)
definition "check_no_overlap \<gamma> ft = (\<forall>a \<in> set ft. \<forall>b \<in> set ft. \<forall>p \<in> UNIV. (fst a = fst b \<and> OF_match \<gamma> (snd3 a) p \<and> a \<noteq> b) \<longrightarrow> \<not>OF_match \<gamma> (snd3 b) p)"
lemma card1_eI: "1 \<le> card S \<Longrightarrow> \<exists>y S'. S = {y} \<union> S' \<and> y \<notin> S'"
	by (metis One_nat_def card_infinite card_le_Suc_iff insert_is_Un leD zero_less_Suc)
lemma card2_eI: "2 \<le> card S \<Longrightarrow> \<exists>x y. x \<noteq> y \<and> x \<in> S \<and> y \<in> S"
proof -
	case goal1
	then have "1 \<le> card S" by simp
	note card1_eI[OF this]
	then obtain x S' where xs: "S = {x} \<union> S' \<and> x \<notin> S'" by presburger
	then have "1 \<le> card S'" 
		by (metis goal1 Suc_1 card_infinite card_insert_if finite_Un insert_is_Un le0 not_less_eq_eq) 
	then obtain y where "y \<in> S'" by fastforce
	then show ?case using xs by force
qed

(* If there are no overlapping rules, our match should check out. *)
lemma no_overlap_not_unefined: "check_no_overlap \<gamma> ft \<Longrightarrow> OF_same_priority_match2 \<gamma> ft p \<noteq> Undefined"
proof
	case goal1
	let ?as = "{f. f \<in> set ft \<and> OF_match \<gamma> (snd3 f) p \<and> (\<forall>fo \<in> set ft. fst f < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)}"
	have fin: "finite ?as" by simp
	note goal1(2)[unfolded OF_same_priority_match2_def]
	then have "2 \<le> card (trd ` ?as)"
		unfolding Let_def
		apply(cases "card (trd ` ?as)", simp add: image_Collect)
		apply(rename_tac nat1, case_tac nat1, simp add: image_Collect)
		apply(presburger)
		done
	then have "2 \<le> card ?as" using card_image_le[OF fin, of trd] by linarith
	then obtain a b where ab: "a \<noteq> b" "a \<in> ?as" "b \<in> ?as" using card2_eI by blast
	then have ab2: "a \<in> set ft" "OF_match \<gamma> (snd3 a) p" "(\<forall>fo\<in>set ft. fst a < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" 
	               "b \<in> set ft" "OF_match \<gamma> (snd3 b) p" "(\<forall>fo\<in>set ft. fst b < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" by simp_all
	then have "fst a = fst b"
		by fastforce
	note goal1(1)[unfolded check_no_overlap_def] ab2(1) ab2(4) this ab2(2) ab(1) ab2(5)
	then show False by blast
qed

fun OF_match_linear :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> 'a option" where
"OF_match_linear _ [] _ = None" |
"OF_match_linear \<gamma> (a#as) p = (if OF_match \<gamma> (snd3 a) p then Some (trd a) else OF_match_linear \<gamma> as p)"

lemma set_eq_rule: "(\<And>x. x \<in> a \<Longrightarrow> x \<in> b) \<Longrightarrow> (\<And>x. x \<in> b \<Longrightarrow> x \<in> a) \<Longrightarrow> a = b" by blast

lemma unmatching_insert_agnostic: "\<not> OF_match \<gamma> (snd3 a) p \<Longrightarrow> OF_same_priority_match2 \<gamma> (a # ft) p = OF_same_priority_match2 \<gamma> ft p"
proof -
	let ?as = "{f. f \<in> set ft \<and> OF_match \<gamma> (snd3 f) p \<and> (\<forall>fo \<in> set ft. fst f < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)}"
	let ?aas = "{f |f. f \<in> set (a # ft) \<and> OF_match \<gamma> (snd3 f) p \<and> (\<forall>fo\<in>set (a # ft). fst f < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)}"
	case goal1 note nm = this 
	have aa: "?aas = ?as"
	proof(rule set_eq_rule)
		case goal1
		hence as: "x \<in> set (a # ft) \<and> OF_match \<gamma> (snd3 x) p \<and> (\<forall>fo\<in>set (a # ft). fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" by simp
		with nm have "x \<in> set ft" by fastforce
		moreover from as have "(\<forall>fo\<in>set ft. fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" by simp
		ultimately show ?case using as by force
	next
		case goal2
		hence as: "x \<in> set ft" "OF_match \<gamma> (snd3 x) p" "(\<forall>fo\<in>set ft. fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" by simp_all
		from as(1) have "x \<in> set (a # ft)" by simp
		moreover from as(3) have "(\<forall>fo\<in>set (a # ft). fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)" using nm by simp
		ultimately show ?case using as(2) by blast
	qed
	note uf = arg_cong[OF aa, of "op ` trd", unfolded image_Collect]
	show ?case unfolding OF_same_priority_match2_def using uf by presburger
qed

lemma forall_append: "(\<forall>k \<in> set (m @ n). P k) \<longleftrightarrow> (\<forall>k \<in> set m. P k) \<and> (\<forall>k \<in> set n. P k)" by auto

lemma f_Img_ex_set: "{f x|x. P x} = f ` {x. P x}" by auto

lemma "sorted_descending (map fst ft) \<Longrightarrow> check_no_overlap \<gamma> ft \<Longrightarrow> 
	OF_same_priority_match2 \<gamma> ft p = Defined (OF_match_linear \<gamma> ft p)"
proof(induction "ft")
	case goal2
	have 1: "sorted_descending (map fst ft)" using goal2(2) by simp
	have 2: "check_no_overlap \<gamma> ft" using goal2(3) unfolding check_no_overlap_def using set_subset_Cons by fast
	note mIH = goal2(1)[OF 1 2]
	show ?case (is ?kees)
	proof(cases "OF_match \<gamma> (snd3 a) p")
		case False thus ?kees 
			by(simp only: OF_match_linear.simps if_False mIH[symmetric] unmatching_insert_agnostic[OF False])
	next
		note sorted_descending_split[OF goal2(2)]
		then obtain m n where mn: "a # ft = m @ n" "\<forall>e\<in>set m. fst a = fst e" "\<forall>e\<in>set n. fst e < fst a"
			unfolding list.sel by blast 
		hence aem: "a \<in> set m"
			by (metis UnE less_imp_neq list.set_intros(1) set_append)
		have mover: "check_no_overlap \<gamma> m" using goal2(3) unfolding check_no_overlap_def
			by (metis Un_iff mn(1) set_append)
		let ?fc = "(\<lambda>s. 
			{f. f \<in> set s \<and> OF_match \<gamma> (snd3 f) p \<and> 
			(\<forall>fo\<in>set (a # ft). fst f < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)})"
		case True
		have "?fc (m @ n) = ?fc m \<union> ?fc n" by auto
		moreover have "?fc n = {}"
		proof(rule set_eq_rule, rule ccontr)
			case goal1
			hence g1: "x \<in> set n" "OF_match \<gamma> (snd3 x) p" 
				"(\<forall>fo\<in>set m. fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)"
				"(\<forall>fo\<in>set n. fst x < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)"
				unfolding mn(1) by(simp_all)
			from g1(1) mn(3) have le: "fst x < fst a" by simp
			note le g1(3) aem True
			then show False by blast
		qed simp
		ultimately have cc: "?fc (m @ n) = ?fc m" by blast
		have cm: "?fc m = {a}" (* using goal2(3) *)
		proof - case goal1
			have "\<forall>f \<in> set m. (\<forall>fo\<in>set (a # ft). fst f < fst fo \<longrightarrow> \<not> OF_match \<gamma> (snd3 fo) p)"
				by (metis UnE less_asym mn set_append) (* sorry *)
			hence 1: "?fc m = {f \<in> set m. OF_match \<gamma> (snd3 f) p}" by blast
			show ?case unfolding 1
			proof(rule set_eq_rule)
				case goal2
				have "a \<in> {f \<in> set m. OF_match \<gamma> (snd3 f) p}" using True aem by simp
				thus ?case using goal2 by simp
			next
				case goal1 show ?case proof(rule ccontr)
					assume "x \<notin> {a}" hence ne: "x \<noteq> a" by simp
					from goal1 have 1: "x \<in> set m" "OF_match \<gamma> (snd3 x) p" by simp_all
					have 2: "fst x = fst a" using 1(1) mn(2) by simp
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
	
text{*The flow entries should always be distinct -- yes, but that's not the only thing we want. *}
lemma "\<not> distinct flow_entries \<Longrightarrow> flow_entries \<noteq> [] \<Longrightarrow> \<exists>\<gamma> p. OF_same_priority_match \<gamma> flow_entries p = Undefined"
  apply(simp add: OF_same_priority_match_def)
  apply(rule_tac x="\<lambda>_ _. True" in exI)
  apply(simp add: OF_match_def)
  apply(case_tac flow_entries)
   apply(simp_all)
  apply(rename_tac l list)
  apply(case_tac list)
   apply(simp_all)
  done

lemma OF_same_priority_match_defined:
  "(\<forall>p. OF_same_priority_match \<gamma> flow_entries p \<noteq> Undefined) \<longleftrightarrow> (\<forall>p. length [(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m p] \<le> 1)"
  apply(simp add: OF_same_priority_match_def)
  apply(rule iffI)
   apply(intro allI)
   apply(erule_tac x=p in allE)
   defer
   apply(intro allI)
   apply(erule_tac x=p in allE)
   apply(case_tac [!] "[(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m p]")
      apply(simp_all)
   apply(rename_tac [!] l list)
   apply(case_tac [!] list)
      apply(simp_all split: split_split)
  done


lemma distinct_set_collect_singleton: "distinct xs \<Longrightarrow>
       {x. x \<in> set xs \<and> P x} = {x} \<Longrightarrow>
       [x\<leftarrow>xs . P x] = [x]"
apply(induction xs)
 apply(simp)
apply(simp)
apply(case_tac "x=a")
 apply simp_all
 apply (smt DiffD2 Diff_insert_absorb filter_False insert_compr mem_Collect_eq)
by (smt Collect_cong ball_empty insert_iff mem_Collect_eq)

lemma set_collect_ge_singleton: "\<forall>x. {x \<in> set xs. P x} \<noteq> {x} \<Longrightarrow>
       P x \<Longrightarrow> x \<in> set xs \<Longrightarrow> length [x\<leftarrow>xs . P x] > 1"
apply(induction xs)
 apply(simp)
apply(simp)
apply(case_tac "x=a")
 apply simp_all
 apply (smt Collect_cong Collect_conv_if2 filter_empty_conv)
by (smt Collect_cong filter_empty_conv)

text{*set representation*}
lemma OF_same_priority_match_set: "distinct flow_entries \<Longrightarrow> OF_same_priority_match \<gamma> flow_entries packet = (
  let matching_entries = {(m,action) \<in> set flow_entries. OF_match \<gamma> m packet} in 
    if matching_entries = {} then Defined None else
    if \<exists>! x. matching_entries = {x} then Defined (Some (snd (the_elem matching_entries))) else
       Undefined)"
apply(simp add: OF_same_priority_match_def  Let_def)
apply(safe)
       apply(simp_all)
   apply blast
  apply(rename_tac a b aa bb)
  apply(drule_tac P="\<lambda>(m,action). OF_match \<gamma> m packet" and x="(a,b)" in distinct_set_collect_singleton)
   apply blast
  apply simp
 apply (metis (no_types, lifting) case_prodE filter_False list.simps(4))
apply(subgoal_tac "length [(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m packet] > 1")
 apply(case_tac "[(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m packet]")
  apply(simp)
 apply(rename_tac l list)
 apply(case_tac list)
  apply(simp)
 apply(simp)
apply(rule set_collect_ge_singleton)
  apply(simp_all)
by blast


lemma list_filter_singleton_element_eq: "[x\<leftarrow>xs. P x] = [x] \<Longrightarrow>
       y \<in> set xs \<Longrightarrow> P y \<Longrightarrow> x = y"
apply(induction xs)
 apply(simp)
apply(simp)
by (metis filter_empty_conv list.inject)

lemma helper_foo: "\<not> (\<forall>x2. l \<noteq> (fst l, x2))"
by (meson eq_fst_iff)

lemma helper_foo2: "\<not> (\<forall>x2. ba \<noteq> x2)" by simp

lemma helper_foo3: "(\<forall>x\<in>set list. \<forall>x1. (\<forall>x2. x \<noteq> (x1, x2)) \<or> P x1) \<longleftrightarrow> 
       (\<forall>(x,y)\<in>set list. P x)"
by blast


lemma helper_foo4: "
       \<forall>x\<in>set list. \<forall>x1. (\<forall>x2. x \<noteq> (x1, x2)) \<or> a = x1 \<or> \<not> OF_match \<gamma> x1 p \<Longrightarrow>
       (a, b) \<notin> set list \<Longrightarrow>
       (\<forall>(x,y)\<in>set list. \<not> OF_match \<gamma> x p) \<or> (\<exists>b'. (a, b') \<in> set list)"
apply(subst(asm) helper_foo3)
apply(induction list)
 apply(simp)
apply(auto)
done

lemma helper_foo5: "\<forall>(x, y)\<in>set list. \<not> OF_match \<gamma> x p \<Longrightarrow> [(m, action)\<leftarrow>list . OF_match \<gamma> m p] = []"
 by(induction list) auto


definition "overlapping_entries \<gamma> flow_entries_matches \<equiv> (\<exists>p. \<exists>entry1 \<in> set flow_entries_matches. \<exists>entry2 \<in> set flow_entries_matches. 
          (entry1 \<noteq> entry2) \<and> OF_match \<gamma> entry1 p \<and> OF_match \<gamma> entry2 p)"

lemma not_overlapping_entries_fst: "\<not> overlapping_entries \<gamma> (x#xs) \<Longrightarrow> \<not> overlapping_entries \<gamma> xs"
   by(simp add: overlapping_entries_def)

lemma leq_1_match_iff_not_overlapping_entries: "distinct (map (\<lambda>(m,a). m) flow_entries) \<Longrightarrow> 
      (\<forall>p. length [(m, action) \<leftarrow> flow_entries . OF_match \<gamma> m p] \<le> 1) \<longleftrightarrow> 
      \<not> overlapping_entries \<gamma> (map (\<lambda>(m,a). m) flow_entries)"
  apply(simp)
  apply(rule iffI)
   apply(simp add: overlapping_entries_def)
   apply(intro allI)
   apply(erule_tac x=p in allE)
   apply(case_tac "[(m, action)\<leftarrow>flow_entries . OF_match \<gamma> m p]")
    apply(simp_all)
    apply(clarify)
    apply (metis case_prodI filter_empty_conv)
   apply(clarify)
   apply(rename_tac p m1 a1 unused m2 a2 m3 a3)
   apply(frule_tac y="(m2, a2)" in list_filter_singleton_element_eq)
     apply(simp_all)
   apply(frule_tac y="(m3, a3)" in list_filter_singleton_element_eq)
     apply(simp_all)
  apply(intro allI)
  (*apply(erule_tac x=p in allE)*)
  (*apply(simp split: split_split_asm)*)
  apply(induction flow_entries)
   apply(simp)
  apply(rename_tac l list p)
  apply(simp add: not_overlapping_entries_fst)
  apply(safe)
  apply(simp add: overlapping_entries_def)
  apply(erule_tac x=p in allE)
  apply(simp)
  apply(safe)
  by (smt case_prodE filter_False image_iff split_conv)
  

(*"The packet is matched against the table and only the highest priority flow entry that matches the
packet must be selected" *)
definition group_descending_priority :: "('m, 'a) flow_entry_match list \<Rightarrow> ('m, 'a) flow_entry_match list list" where
  "group_descending_priority flow_table \<equiv> list_group_eq_key (\<lambda>(priority,_,_). priority) (sort_descending_key (\<lambda>(priority,_,_). priority) flow_table)"


(*assumes: sorted_descending flow_table and partitioned by same priority*)
fun internal_OF_match_table :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> (('m match_fields \<times> 'a) list) list \<Rightarrow> 'p \<Rightarrow> 'a undefined_behavior" where
  "internal_OF_match_table \<gamma> [] packet = Undefined" |
  "internal_OF_match_table \<gamma> (same_priority_flow_table#ts) packet =
      (case OF_same_priority_match \<gamma> same_priority_flow_table packet
          of Undefined \<Rightarrow> Undefined
           | Defined None \<Rightarrow> internal_OF_match_table \<gamma> ts packet
           | Defined (Some a) \<Rightarrow> Defined a)"


definition OF_match_table :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m, 'a) flow_entry_match list \<Rightarrow> 'p \<Rightarrow> 'a undefined_behavior" where
  "OF_match_table \<gamma> flow_table packet = internal_OF_match_table \<gamma>
      (map (map (\<lambda>(_, match, action). (match,action))) (group_descending_priority flow_table))
      packet"


(*
"For add requests (OFPFC_ADD) with the OFPFF_CHECK_OVERLAP flag set, the switch must first check for
any overlapping flow entries in the requested table. Two flow entries overlap if a single packet may
match both, and both entries have the same priority. If an overlap conflict exists between an existing
flow entry and the add request, the switch must refuse the addition and respond with an Overlap error
message (see 7.5.4.6)."*)
(*this definition is slightly stricter, OpenVSwitch does not throw an error for two identical entries.*)
definition OFPFF_CHECK_OVERLAP_same_priority :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m match_fields) list \<Rightarrow> 'm match_fields \<Rightarrow> bool" where
  "OFPFF_CHECK_OVERLAP_same_priority \<gamma> flow_entries_match new_entry_match \<equiv>
      \<exists>packet. \<exists>entrie \<in> set flow_entries_match. OF_match \<gamma> new_entry_match packet \<and> OF_match \<gamma> entrie packet"



text{*If @{const OFPFF_CHECK_OVERLAP_same_priority} is @{const True}, there may be a packet which triggers the undefined behavior.*}
lemma "OFPFF_CHECK_OVERLAP_same_priority \<gamma> [entry1] entry2 \<Longrightarrow> \<exists>packet. OF_match_table \<gamma> [(priority, entry2, a2), (priority, entry1, a1)] packet = Undefined"
  apply(simp add: OFPFF_CHECK_OVERLAP_same_priority_def OF_match_table_def
                  group_descending_priority_def sort_descending_key_def
             split: option.split)
  apply(simp add: OF_same_priority_match_def)
  apply(erule exE)
  apply(rule_tac x=packet in exI)
  apply(clarify)
  apply(simp)
  done


lemma no_OFPFF_CHECK_OVERLAP_same_priority: 
      "distinct flow_entries_match \<Longrightarrow>
      (\<forall>entry \<in> set flow_entries_match. \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry flow_entries_match) entry)
      \<longleftrightarrow>
      \<not> overlapping_entries \<gamma> flow_entries_match"
  unfolding overlapping_entries_def
  apply(simp add: OF_same_priority_match_def)
  apply(simp add: OFPFF_CHECK_OVERLAP_same_priority_def OF_match_table_def
                  group_descending_priority_def sort_descending_key_def
             split: option.split)
  by blast

lemma no_overlapping_entries_same_priority_defined: "distinct (map (\<lambda>(m, _). m) same_priority_match) \<Longrightarrow>
        \<not> overlapping_entries \<gamma> (map (\<lambda>(m, _). m) same_priority_match)
      \<longleftrightarrow>
        (\<forall>packet. OF_same_priority_match \<gamma> same_priority_match packet \<noteq> Undefined)"
  by(simp add: leq_1_match_iff_not_overlapping_entries[symmetric] OF_same_priority_match_defined)


corollary OFPFF_CHECK_OVERLAP_same_priority_defined: "distinct (map (\<lambda>(m, _). m) same_priority_match) \<Longrightarrow>
      (\<forall>entry \<in> set (map (\<lambda>(m, _). m) same_priority_match).
        \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry (map (\<lambda>(m, _). m) same_priority_match)) entry)
      \<longleftrightarrow>
      (\<forall>packet. OF_same_priority_match \<gamma> same_priority_match packet \<noteq> Undefined)"
  apply(subst no_OFPFF_CHECK_OVERLAP_same_priority)
   apply(simp)
  apply(simp add: no_overlapping_entries_same_priority_defined)
  done



(*Every flow table must support a table-miss flow entry to process table misses.
The table-miss flow entry is identified by its match and its priority (see 5.2), it wildcards all match
fields (all fields omitted) and has the lowest priority (0).*)

definition has_table_miss_entry :: " ('m, 'a) flow_entry_match list \<Rightarrow> bool" where
  "has_table_miss_entry flow_table \<equiv> \<exists> table_miss_action. (0, MatchFields {}, table_miss_action) \<in> set flow_table"

lemma has_table_miss_entry_fst: 
  "has_table_miss_entry ((priority, matches, action) # flow_table) \<Longrightarrow> priority = 0 \<and> matches = MatchFields {} \<or> has_table_miss_entry flow_table"
  apply(simp add: has_table_miss_entry_def)
  by blast

lemma "distinct (sort (x#xs)) \<Longrightarrow> distinct (sort xs)"
by (meson distinct.simps(2) distinct_sort)


lemma "distinct (map (map (\<lambda>(_, match, _). match)) (group_descending_priority (f#fs))) \<Longrightarrow>
       distinct (map (map (\<lambda>(_, match, _). match)) (group_descending_priority fs))"
apply(simp add: group_descending_priority_def sort_descending_key_def)
apply(simp add: distinct_sort)
oops

definition "all_not_OFPFF_CHECK_OVERLAP \<gamma> grouped_matches \<equiv> \<forall> same_priority_matches \<in> grouped_matches.
       (\<forall> entry \<in> set same_priority_matches. \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry same_priority_matches) entry)"

lemma "has_table_miss_entry flow_table \<Longrightarrow> distinct ((map (map (\<lambda>(_, match, _). match))) (group_descending_priority flow_table)) \<Longrightarrow>
 all_not_OFPFF_CHECK_OVERLAP \<gamma> (set ((map (map (\<lambda>(_, match, _). match))) (group_descending_priority flow_table)))
  \<Longrightarrow>
  OF_match_table \<gamma> flow_table packet \<noteq> Undefined"
  apply(rule iffI)
   unfolding OF_match_table_def
   apply(induction flow_table)
    apply(simp add: has_table_miss_entry_def)
   apply(clarify)
   apply(drule has_table_miss_entry_fst)
   apply(safe)
    defer
    apply(simp)
   thm OFPFF_CHECK_OVERLAP_same_priority_defined
   apply(subst(asm) OFPFF_CHECK_OVERLAP_same_priority_defined)
oops


lemma defines "same_priority_match flow_table \<equiv> ((map (map (\<lambda>(_, match, _). match))) (group_descending_priority flow_table))"
  assumes "has_table_miss_entry flow_table" and "distinct (same_priority_match flow_table)"
   and "\<forall> same_priority_matches \<in> set (same_priority_match flow_table).
       (\<forall> entry \<in> set same_priority_matches. \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry same_priority_matches) entry)"
 shows "OF_match_table \<gamma> flow_table packet \<noteq> Undefined"
  proof -
    from assms have "\<forall>m \<in> set (same_priority_match flow_table). \<not> overlapping_entries \<gamma> m"
      unfolding same_priority_match_def
      using no_OFPFF_CHECK_OVERLAP_same_priority
   thm OFPFF_CHECK_OVERLAP_same_priority_defined
   apply(subst(asm) OFPFF_CHECK_OVERLAP_same_priority_defined)
oops





fun process_OF_table :: "(string \<times> 'p)"
  "process_of_table (ingress_port, p)"

end
