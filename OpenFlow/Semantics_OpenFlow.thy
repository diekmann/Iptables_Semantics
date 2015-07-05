theory Semantics_OpenFlow
imports List_Group Sort_Descending
  "../Bitmagic/IPv4Addr"
begin

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

(*priority \<times> Match Fields \<times> instructions
 not modeled: counters, timeouts, cookie ("Not used when processing packets"), flags,
     instructions (only an output list of egress ports will be modeled)
*)
type_synonym ('m, 'a) flow_entry_match="16 word \<times> 'm set \<times> 'a"


(*the packet also contains the ingress port*)
definition OF_match :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> 'm set \<Rightarrow> 'p \<Rightarrow> bool" where
  "OF_match \<gamma> match_fields packet \<equiv> \<forall> field \<in> match_fields. \<gamma> field packet"


(*
"If there are multiple matching flow entries with the same highest priority, the selected flow entry is explicitly undefined."
OFP 1.0.0 also stated that non-wildcarded matches implicitly have the highest priority (which is gone in 1.5).
*)
definition OF_same_priority_match :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m set \<times> 'a) list \<Rightarrow> 'p \<Rightarrow> 'a option" where
  "OF_same_priority_match \<gamma> flow_entries packet \<equiv> let matching_entries = (filter (\<lambda>(m, _). OF_match \<gamma> m packet) flow_entries) in 
    case matching_entries of [] \<Rightarrow> None
                            | [(_, action)] \<Rightarrow> Some action
                            | _ \<Rightarrow> undefined
    "


(*"The packet is matched against the table and only the highest priority flow entry that matches the
packet must be selected" *)


(*assumes: sorted_descending flow_table and partitioned by same priority*)
fun internal_OF_match_table :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> (('m set \<times> 'a) list) list \<Rightarrow> 'p \<Rightarrow> 'a" where
  "internal_OF_match_table \<gamma> [] packet = undefined" |
  "internal_OF_match_table \<gamma> (same_priority_flow_table#ts) packet =
      (case OF_same_priority_match \<gamma> same_priority_flow_table packet
          of None \<Rightarrow> internal_OF_match_table \<gamma> ts packet
           | Some a \<Rightarrow> a)"


definition OF_match_table :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m, 'a) flow_entry_match list \<Rightarrow> 'p \<Rightarrow> 'a" where
  "OF_match_table \<gamma> flow_table packet = internal_OF_match_table \<gamma>
      (map (map (\<lambda>(_, match, action). (match,action))) (list_group_eq_key (\<lambda>(priority,_,_). priority) (sort_descending_key (\<lambda>(priority,_,_). priority) flow_table)))
      packet"


(*
"For add requests (OFPFC_ADD) with the OFPFF_CHECK_OVERLAP flag set, the switch must first check for
any overlapping flow entries in the requested table. Two flow entries overlap if a single packet may
match both, and both entries have the same priority. If an overlap conflict exists between an existing
flow entry and the add request, the switch must refuse the addition and respond with an Overlap error
message (see 7.5.4.6)."*)

definition OFPFF_CHECK_OVERLAP_same_priority :: "('m \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('m set) list \<Rightarrow> 'm set \<Rightarrow> bool" where
  "OFPFF_CHECK_OVERLAP_same_priority \<gamma> flow_entries_match new_entry_match \<equiv>
      \<exists>packet. \<exists>entrie \<in> set flow_entries_match. OF_match \<gamma> new_entry_match packet \<and> OF_match \<gamma> entrie packet"


(*Every flow table must support a table-miss flow entry to process table misses.
The table-miss flow entry is identified by its match and its priority (see 5.2), it wildcards all match
fields (all fields omitted) and has the lowest priority (0).*)



fun process_OF_table :: "(string \<times> 'p)"
  "process_of_table (ingress_port, p)"

end
