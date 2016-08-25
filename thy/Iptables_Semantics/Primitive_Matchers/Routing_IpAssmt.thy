section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports Ipassmt
        "../../Routing/Routing_Table"
begin
context
begin

subsection\<open>Routing IP Assignment\<close>
text\<open>Up to now, the definitions were all still on word intervals because those are much more convenient to work with.\<close>

definition routing_ipassmt :: "'i::len routing_rule list \<Rightarrow> (iface \<times> ('i word \<times> nat) list) list"
  where
  "routing_ipassmt rt \<equiv> map (apfst Iface \<circ> apsnd cidr_split) (routing_ipassmt_wi rt)"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

private lemma map_of_map_Iface: "map_of (map (\<lambda>x. (Iface (fst x), f (snd x))) xs) (Iface ifce) = 
        map_option f ((map_of xs) ifce)"
  by (induct xs) (auto)

value "routing_ipassmt_wi ([]::32 prefix_routing)"  (* we're cheating a bit here\<dots> [(output_iface (routing_action undefined), WordInterval (0::32 word) (0xFFFFFFFF::32 word))] *)

lemma routing_ipassmt: "
    valid_prefixes rt \<Longrightarrow>
    routing_table_semantics rt (p_dst p) = \<lparr>output_iface = oifce, next_hop = ignored\<rparr> \<Longrightarrow>
    p_oiface p = oifce \<Longrightarrow>
    \<exists>p_ips. map_of (routing_ipassmt rt) (Iface oifce) = Some p_ips \<and> p_dst p \<in> ipcidr_union_set (set p_ips)"
  apply(simp add: routing_ipassmt_def)
  apply(drule routing_ipassmt_wi[where output_port=oifce and k="p_dst p"])
  apply(simp)
  apply(elim exE, rename_tac ip_range)
  apply(rule_tac x="cidr_split ip_range" in exI)
  apply(simp)
  apply(simp add: comp_def)
  apply(simp add: map_of_map_Iface)
  apply(rule_tac x="ip_range" in exI)
  apply(simp)
  by (simp add: routing_ipassmt_wi_distinct)


lemma routing_ipassmt_ipassmt_sanity_disjoint: "valid_prefixes (rt::('i::len) prefix_routing) \<Longrightarrow>
    ipassmt_sanity_disjoint (map_of (routing_ipassmt rt))"
unfolding ipassmt_sanity_disjoint_def routing_ipassmt_def comp_def
  apply(clarsimp)
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
using routing_ipassmt_wi_disjoint[where 'i = 'i] by meson
end

end
