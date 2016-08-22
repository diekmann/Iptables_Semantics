section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports "../Primitive_Matchers/Ipassmt"
        "../../Routing/Routing_Table"
begin
context
begin

subsection\<open>Routing IP Assignment\<close>
text\<open>Up to now, the definitions were all still on word intervals because those are much more convenient to work with.\<close>

definition "routing_ipassmt rt = map_option cidr_split \<circ> map_of (routing_ipassmt_wi rt) \<circ> (\<lambda>x. case x of Iface x \<Rightarrow> x)"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

lemma "valid_prefixes rt \<Longrightarrow> ipassmt_sanity_disjoint (routing_ipassmt rt)"
unfolding ipassmt_sanity_disjoint_def routing_ipassmt_def comp_def
  apply(clarify)
  apply(subst the_map_option, (simp;fail))+
  apply(simp)
  
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
  apply(rule routing_ipassmt_wi_disjoint; assumption)
done

(* TODO: move all of these*)
subsection\<open>IP Assignment difference\<close>
definition "option2wordinterval s \<equiv> (case s of None \<Rightarrow> Empty_WordInterval | Some s \<Rightarrow> ipcidr_tuple_to_wordinterval  s)"
definition "ip_assmt_diff a b \<equiv> let
t = \<lambda>s. (case s of None \<Rightarrow> Empty_WordInterval | Some s \<Rightarrow> ipcidr_tuple_to_wordinterval s);
k = \<lambda>x y d. cidr_split (wordinterval_setminus (t (x d)) (t (y d))) in
{(d, k a b d, k b a d)| d. d \<in> (dom a \<union> dom b)}
"

end
end
