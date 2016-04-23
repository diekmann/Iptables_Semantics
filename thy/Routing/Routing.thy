theory Routing
imports "../Bitmagic/NumberWangCaesar" CaesarTheories
begin

subsection{*Definition*}

record routing_action = 
  output_iface :: string
  next_hop :: "ipv4addr option" (* no next hop if locally attached *)

(* Routing rule matching ip route unicast type *)
record routing_rule =
  routing_match :: "32 prefix_match" (* done on the dst *)
  metric :: nat
  routing_action :: routing_action

definition "default_metric = 0"

type_synonym prefix_routing = "routing_rule list"

definition valid_prefixes where
  "valid_prefixes r = foldr conj (map (\<lambda>rr. valid_prefix (routing_match rr)) r) True"
lemma valid_prefixes_split: "valid_prefixes (r#rs) \<Longrightarrow> valid_prefix (routing_match r) \<and> valid_prefixes rs"
  using valid_prefixes_def by force
lemma valid_prefixes_alt_def: "valid_prefixes r = (\<forall>e \<in> set r. valid_prefix (routing_match e))"
  unfolding valid_prefixes_def
  unfolding foldr_map
  unfolding comp_def
  unfolding foldr_True_set
  ..
  
fun is_longest_prefix_routing :: "prefix_routing \<Rightarrow> bool" where
  "is_longest_prefix_routing (r1#r2#rs) = ((pfxm_length (routing_match r1) \<ge> pfxm_length (routing_match r2)) \<and>
   is_longest_prefix_routing (r2#rs))" |
  "is_longest_prefix_routing _ = True"

(*example: get longest prefix match by sorting by pfxm_length*)
definition "rr_ctor m l a nh me \<equiv> \<lparr> routing_match = PrefixMatch (ipv4addr_of_dotdecimal m) l, metric = me, routing_action =\<lparr>output_iface = a, next_hop = (map_option ipv4addr_of_dotdecimal nh)\<rparr> \<rparr>"
value "rev (sort_key (\<lambda>r. pfxm_length (routing_match r)) [
  rr_ctor (0,0,0,1) 3 '''' None 0,
  rr_ctor (0,0,0,2) 8 [] None 0,
  rr_ctor (0,0,0,3) 4 [] None 0])"
lemma longest_prefix_routing_no_sort: 
  "is_longest_prefix_routing tbl \<Longrightarrow>
  (sort_key (\<lambda>r. 32 - pfxm_length (routing_match r)) tbl) = tbl"
  by (induction tbl rule: is_longest_prefix_routing.induct) auto

(* todo: document that it is runtime checkable *)
fun has_default_route :: "prefix_routing \<Rightarrow> bool" where
"has_default_route (r#rs) = (((pfxm_length (routing_match r)) = 0) \<or> has_default_route rs)" |
"has_default_route Nil = False"

lemma has_default_route_alt: "has_default_route rt \<longleftrightarrow> (\<exists>r \<in> set rt. pfxm_length (routing_match r) = 0)" by(induction rt) simp_all

definition correct_routing :: "prefix_routing \<Rightarrow> bool" where 
  "correct_routing r \<equiv> is_longest_prefix_routing r \<and> has_default_route r \<and> valid_prefixes r"

lemma is_longest_prefix_routing_rule_exclusion1:
  assumes "is_longest_prefix_routing (r1 # rn # rss)"
  shows "is_longest_prefix_routing (r1 # rss)"
using assms  by(case_tac rss, simp_all)
  
lemma is_longest_prefix_routing_rules_injection:
  assumes "is_longest_prefix_routing r"
  assumes "r = r1 # rs @ r2 # rss"
  shows "(pfxm_length (routing_match r1) \<ge> pfxm_length (routing_match r2))"
using assms
proof(induction rs arbitrary: r)
  case (Cons rn rs)
  let ?ro = "r1 # rs @ r2 # rss"
  have "is_longest_prefix_routing ?ro" using Cons.prems is_longest_prefix_routing_rule_exclusion1[of r1 rn "rs @ r2 # rss"] by simp
  from Cons.IH[OF this] show ?case by simp
qed simp

subsection{*Single Packet Semantics*}

(* WARNING: all proofs assume correct_routing: list is sorted by descending prefix length, prefixes are valid. Some need a default route. *)
fun routing_table_semantics :: "prefix_routing \<Rightarrow> ipv4addr \<Rightarrow> routing_action" where
"routing_table_semantics [] _ = routing_action (undefined::routing_rule)" | 
"routing_table_semantics (r#rs) p = (if prefix_match_semantics (routing_match r) p then routing_action r else routing_table_semantics rs p)"

lemma routing_table_semantics_ports_from_table: "valid_prefixes rtbl \<Longrightarrow> has_default_route rtbl \<Longrightarrow> 
  routing_table_semantics rtbl packet = r \<Longrightarrow> r \<in> routing_action ` set rtbl"
proof(induction rtbl)
  case (Cons r rs)
  note v_pfxs = valid_prefixes_split[OF Cons.prems(1)]
  show ?case
  proof(cases "pfxm_length (routing_match r) = 0")
    case True
    note zero_prefix_match_all[OF conjunct1[OF v_pfxs] True] Cons.prems(3)
    then show ?thesis by simp
  next
    case False
    hence "has_default_route rs" using Cons.prems(2) by simp
    from Cons.IH[OF conjunct2[OF v_pfxs] this] Cons.prems(3) show ?thesis by force
  qed
qed simp

end
