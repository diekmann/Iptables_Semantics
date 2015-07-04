theory Semantics_OpenFlow
imports Main Firewall_Common Misc Semantics 
  "Primitive_Matchers/IpAddresses"
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


  (*TODO: move*)
  text{* sorting descending *}
  context linorder
  begin
  fun sorted_descending :: "'a list \<Rightarrow> bool" where
    "sorted_descending [] \<longleftrightarrow> True" |
    "sorted_descending (a#as) \<longleftrightarrow> (\<forall>x \<in> set as. a \<ge> x) \<and> sorted_descending as"
  
  definition sort_descending_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
    "sort_descending_key f xs \<equiv> rev (sort_key f xs)"
  end
  lemma sorted_descending_Cons: "sorted_descending (x#xs) \<longleftrightarrow> sorted_descending xs \<and> (\<forall>y\<in>set xs. y \<le> x)"
  by(induction xs) auto
  
  lemma sorted_descending_tail: "sorted_descending (xs@[x]) \<longleftrightarrow> sorted_descending xs \<and> (\<forall>y\<in>set xs. x \<le> y)"
  by(induction xs) auto
  
  lemma sorted_descending: "sorted_descending (rev xs) \<longleftrightarrow> sorted xs"
  apply(induction xs)
   apply(simp)
  apply(simp add: sorted_Cons sorted_descending_tail)
  done
  
  lemma sort_descending: "sorted_descending (sort_descending_key (\<lambda>x. x) xs)"
    by(simp add: sort_descending_key_def sorted_descending)



(*"The packet is matched against the table and only the highest priority flow entry that matches the
packet must be selected" *)

function (sequential) list_group_eq :: "'a list \<Rightarrow> 'a list list" where
  "list_group_eq [] = []" |
  "list_group_eq (x#xs) = [x # takeWhile (op = x) xs] @ list_group_eq (dropWhile (op = x) xs)"
by pat_completeness auto
termination list_group_eq
apply (relation "measure (\<lambda>N. length N )")
apply(simp_all add: le_imp_less_Suc length_dropWhile_le)
done

value "list_group_eq [1::int,2,2,2,3,1,4,5,5,5]"


function (sequential) list_group_eq_key :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "list_group_eq_key _ [] = []" |
  "list_group_eq_key f (x#xs) = [x # takeWhile (\<lambda>y. f x = f y) xs] @ list_group_eq_key f (dropWhile (\<lambda>y. f x = f y) xs)"
by pat_completeness auto
termination list_group_eq_key
apply (relation "measure (\<lambda>(f,N). length N )")
apply(simp_all add: le_imp_less_Suc length_dropWhile_le)
done

value "list_group_eq_key fst [(1::int, ''''), (2,''a''), (2,''b''), (2, ''c''), (3, ''c''), (1,''''), (4,'''')]"

lemma "list_group_eq_key id xs = list_group_eq xs"
apply(induction xs)
 apply(simp_all add: id_def)
by (smt append.simps(1) append.simps(2) dropWhile.simps(1) dropWhile.simps(2) dropWhile_cong list.sel(3) list_group_eq.elims list_group_eq_key.elims takeWhile_cong)

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


(*Every flow table must support a table-miss flow entry to process table misses.
The table-miss flow entry is identified by its match and its priority (see 5.2), it wildcards all match
fields (all fields omitted) and has the lowest priority (0).*)



fun process_OF_table :: "(string \<times> 'p)"
  "process_of_table (ingress_port, p)"

end
