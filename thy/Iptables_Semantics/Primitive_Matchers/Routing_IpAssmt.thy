section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports Ipassmt
        "../../Routing/Routing_Table"
begin
context
begin

subsection\<open>Routing IP Assignment\<close>
text\<open>Up to now, the definitions were all still on word intervals because those are much more convenient to work with.\<close>

definition "routing_ipassmt rt = (map (apfst Iface \<circ> apsnd cidr_split) (routing_ipassmt_wi rt))"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

lemma "valid_prefixes (rt::('i::len) prefix_routing) \<Longrightarrow> ipassmt_sanity_disjoint (map_of (routing_ipassmt rt))"
unfolding ipassmt_sanity_disjoint_def routing_ipassmt_def comp_def
  apply(clarsimp)
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
using routing_ipassmt_wi_disjoint[where 'i = 'i] by meson
end

end
