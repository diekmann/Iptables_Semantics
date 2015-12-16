theory AnnotateRouting
imports RoutingRange
begin

subsection{*Annoted routintables*}
text{* The range relation destroys a vital piece of information: given an entry in the range relation, 
	it is not easily possible to find which prefix it originated from. That prefix is interesting
	because it is a very succinct way to represent the information. *}

type_synonym annotated_routing = "(routing_rule \<times> ipv4range) list"

fun annotate_rt_i :: "prefix_routing \<Rightarrow> ipv4range \<Rightarrow> annotated_routing" where
"annotate_rt_i [] lo = [(\<lparr>routing_match = \<lparr>pfxm_prefix=0,pfxm_length=0\<rparr>, routing_action = []\<rparr>,lo)]" | (* insert default route to nirvana *)
"annotate_rt_i (a#as) lo = (
	let rpm = range_prefix_match (routing_match a) lo; m = fst rpm; nm = snd rpm in (
	(a,m) # annotate_rt_i as nm))"
	
definition "annotate_rt tbl = annotate_rt_i tbl wordinterval_UNIV"

lemma annotate_smallening: "e \<in> set (annotate_rt_i tbl s) \<Longrightarrow> wordinterval_subset (snd e) s"
proof(induction tbl arbitrary: s)
	case (Cons a as)
	thus ?case (is ?kees) proof(cases "e = (a, fst (range_prefix_match (routing_match a) s))")
		case False
		hence el: "e \<in> set (annotate_rt_i as (snd (range_prefix_match (routing_match a) s)))"
			using Cons.prems by(simp add: Let_def)
		show ?kees using Cons.IH[OF el]
			by(simp add: range_prefix_match_def Let_def ipv4range_setminus_def) blast
	qed (simp add: range_prefix_match_def Let_def ipv4range_intersection_def)
qed simp

lemma "e \<in> set (annotate_rt_i tbl s) \<Longrightarrow> k \<in> wordinterval_to_set (snd e) \<Longrightarrow> valid_prefixes tbl \<Longrightarrow>
	routing_action (fst e) = routing_table_semantics tbl k"
proof(induction tbl arbitrary: s)
	case (Cons a as)
	note s = Cons.prems(1)[unfolded annotate_rt_i.simps Let_def set_Cons]
	note vpfx = valid_prefixes_split[OF Cons.prems(3)] 
	show ?case (is ?kees) proof(cases "e = (a, fst (range_prefix_match (routing_match a) s))")
		case False
		hence es: "e \<in> set (annotate_rt_i as (snd (range_prefix_match (routing_match a) s)))" using s by blast
		note eq = Cons.IH[OF this Cons.prems(2) conjunct2[OF vpfx]]
		have "\<not>prefix_match_semantics (routing_match a) k" (is ?nom)
		proof -
			show ?nom unfolding prefix_match_if_in_my_set[OF conjunct1[OF vpfx]]
			using annotate_smallening[OF es] Cons.prems(2)
			unfolding wordinterval_subset_set_eq
				by(auto simp add: 
					range_prefix_match_def Let_def ipv4range_setminus_def prefix_to_range_set_eq[symmetric] ipv4range_to_set_def)
		qed
		thus ?kees using eq by simp
	next
		case True
		hence fe: "fst e = a" by simp
		from True have "k \<in> (wordinterval_to_set \<circ> fst \<circ> range_prefix_match (routing_match a) $ s)"
			using Cons.prems(2) by(simp add: comp_def)
		hence "prefix_match_semantics (routing_match a) k" 
			unfolding comp_def fun_app_def
			unfolding prefix_match_if_in_my_set[OF conjunct1, OF vpfx]
			unfolding range_prefix_match_def Let_def
			by(simp add: ipv4range_intersection_def ipv4range_to_set_def prefix_to_range_set_eq[symmetric])
		thus ?kees by(simp add: fe)
	qed
qed simp

lemma range_destination_deadend: "wordinterval_empty k \<Longrightarrow> range_destination tbl k = []"
	by(induction tbl) 
	(simp_all add: ipv4range_to_set_def Let_def range_prefix_match_def ipv4range_setminus_def ipv4range_intersection_def)

lemma "filter (\<lambda>(s, _). \<not>ipv4range_empty s) (map (\<lambda>(r, s). (s, routing_action r)) (annotate_rt_i tbl s)) 
	= range_destination tbl s"
	apply(induction tbl arbitrary: s)
	 apply simp
	apply(simp add: Let_def)
	apply clarify
	apply(subgoal_tac "wordinterval_empty (snd (range_prefix_match (routing_match a) s))")
	 apply(simp add: range_destination_deadend)
	apply(simp add: range_prefix_match_def Let_def ipv4range_setminus_def ipv4range_to_set_def prefix_to_range_set_eq[symmetric])
done

end