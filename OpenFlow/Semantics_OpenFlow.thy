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

(*priority \<times> Match Fields \<times> instructions
 not modeled: counters, timeouts, cookie ("Not used when processing packets"), flags,
     instructions (only an output list of egress ports will be modeled)
*)
type_synonym ('m, 'a) flow_entry_match="16 word \<times> 'm match_fields \<times> 'a"


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

text{*The flow entries should always be distinct*}
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
    if \<exists>x. matching_entries = {x} then Defined (Some (snd (the_elem matching_entries))) else
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


(*TODO: why distinct?*)
lemma no_OFPFF_CHECK_OVERLAP_same_priority: 
      "distinct flow_entries_match \<Longrightarrow>
      (\<forall>entry \<in> set flow_entries_match.
        \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry flow_entries_match) entry)
      \<longleftrightarrow>
      \<not> (\<exists>packet. \<exists>entry1 \<in> set flow_entries_match. \<exists>entry2 \<in> set flow_entries_match. entry1 \<noteq> entry2 \<and> OF_match \<gamma> entry1 packet \<and> OF_match \<gamma> entry2 packet)"
  apply(simp add: OF_same_priority_match_def)
  apply(simp add: OFPFF_CHECK_OVERLAP_same_priority_def OF_match_table_def
                  group_descending_priority_def sort_descending_key_def
             split: option.split)
  by blast

lemma "distinct (map (\<lambda>(m, _). m) same_priority_match) \<Longrightarrow>
      (\<forall>entry \<in> set (map (\<lambda>(m, _). m) same_priority_match).
        \<not> OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry (map (\<lambda>(m, _). m) same_priority_match)) entry)
      \<longleftrightarrow>
      (\<forall>packet. OF_same_priority_match \<gamma> same_priority_match packet \<noteq> Undefined)"
  apply(subst no_OFPFF_CHECK_OVERLAP_same_priority)
   apply(simp)
  apply(simp)
  apply(simp add: OF_same_priority_match_def)
  apply(rule iffI)
   apply(intro allI)
   apply(erule_tac x=packet in allE)
   apply(case_tac "[(m, _)\<leftarrow>same_priority_match . OF_match \<gamma> m packet]")
    apply(simp)
   apply(simp)
   apply(case_tac list)
    apply(simp)
    apply fast
   apply(simp)
   oops



(*Every flow table must support a table-miss flow entry to process table misses.
The table-miss flow entry is identified by its match and its priority (see 5.2), it wildcards all match
fields (all fields omitted) and has the lowest priority (0).*)

definition has_table_miss_entry :: " ('m, 'a) flow_entry_match list \<Rightarrow> bool" where
  "has_table_miss_entry flow_table \<equiv> \<exists> table_miss_action. (0, MatchFields {}, table_miss_action) \<in> set flow_table"

lemma "has_table_miss_entry flow_table \<Longrightarrow>
  \<forall> same_priority_matches \<in> set ((map (map (\<lambda>(_, match, _). match))) (group_descending_priority flow_table)).
     \<forall> entry \<in> set same_priority_matches.
    OFPFF_CHECK_OVERLAP_same_priority \<gamma> (remove1 entry same_priority_matches) entry \<Longrightarrow> OF_match_table \<gamma> flow_table packet \<noteq> Undefined"
oops






fun process_OF_table :: "(string \<times> 'p)"
  "process_of_table (ingress_port, p)"

end
