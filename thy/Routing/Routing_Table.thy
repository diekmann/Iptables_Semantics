section\<open>Routing Table\<close>
theory Routing_Table
imports "../IP_Addresses/Prefix_Match"
        "../IP_Addresses/IPv4" "../IP_Addresses/IPv6"
        "Linorder_Helper"
        "../IP_Addresses/Prefix_Match_toString"
begin

text\<open>This section makes the necessary definitions to work with a routing table using longest prefix matching.\<close>
subsection\<open>Definition\<close>

record(overloaded) 'i routing_action = 
  output_iface :: string
  next_hop :: "'i word option" (* no next hop iff locally attached *)

(* Routing rule matching ip route unicast type *)
record(overloaded) 'i routing_rule =
  routing_match :: "('i::len) prefix_match" (* done on the dst *)
  metric :: nat
  routing_action :: "'i routing_action"

text\<open>This definition is engineered to model routing tables on packet forwarding devices.
It eludes, e.g., the source address hint, which is only relevant for packets originating from the device itself.\<close>
(* See also: http://linux-ip.net/html/routing-saddr-selection.html *)

context
begin

definition "default_metric = 0"

type_synonym 'i prefix_routing = "('i routing_rule) list"

abbreviation "routing_oiface a \<equiv> output_iface (routing_action a)" (* I needed this a lot... *)
abbreviation "routing_prefix r \<equiv> pfxm_length (routing_match r)"

definition valid_prefixes where
  "valid_prefixes r = foldr conj (map (\<lambda>rr. valid_prefix (routing_match rr)) r) True"
lemma valid_prefixes_split: "valid_prefixes (r#rs) \<Longrightarrow> valid_prefix (routing_match r) \<and> valid_prefixes rs"
  using valid_prefixes_def by force

lemma foldr_True_set: "foldr (\<lambda>x. op \<and> (f x)) l True = (\<forall>x \<in> set l. f x)"
  by (induction l) simp_all
lemma valid_prefixes_alt_def: "valid_prefixes r = (\<forall>e \<in> set r. valid_prefix (routing_match e))"
  unfolding valid_prefixes_def
  unfolding foldr_map
  unfolding comp_def
  unfolding foldr_True_set
  ..
  
fun has_default_route :: "('i::len) prefix_routing \<Rightarrow> bool" where
"has_default_route (r#rs) = (((pfxm_length (routing_match r)) = 0) \<or> has_default_route rs)" |
"has_default_route Nil = False"

lemma has_default_route_alt: "has_default_route rt \<longleftrightarrow> (\<exists>r \<in> set rt. pfxm_length (routing_match r) = 0)" by(induction rt) simp_all

subsection\<open>Single Packet Semantics\<close>

fun routing_table_semantics :: "('i::len) prefix_routing \<Rightarrow> 'i word \<Rightarrow> 'i routing_action" where
"routing_table_semantics [] _ = routing_action (undefined::'i routing_rule)" | 
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

subsection\<open>Longest Prefix Match\<close>

text\<open>We can abuse @{const LinordHelper} to sort.\<close>
definition "routing_rule_sort_key \<equiv> \<lambda>r. LinordHelper (0 - (of_nat :: nat \<Rightarrow> int) (pfxm_length (routing_match r))) (metric r)"
text\<open>There is actually a slight design choice here. We can choose to sort based on @{thm less_eq_prefix_match_def} (thus including the address) or only the prefix length (excluding it).
  Which is taken does not matter gravely, since the bits of the prefix can't matter. They're either eqal or the rules don't overlap and the metric decides. (It does matter for the resulting list though.)
  Ignoring the prefix and taking only its length is slightly easier.\<close>

(*example: get longest prefix match by sorting by pfxm_length*)
definition "rr_ctor m l a nh me \<equiv> \<lparr> routing_match = PrefixMatch (ipv4addr_of_dotdecimal m) l, metric = me, routing_action =\<lparr>output_iface = a, next_hop = (map_option ipv4addr_of_dotdecimal nh)\<rparr> \<rparr>"
value "sort_key routing_rule_sort_key [
  rr_ctor (0,0,0,1) 3 '''' None 0,
  rr_ctor (0,0,0,2) 8 [] None 0,
  rr_ctor (0,0,0,3) 4 [] None 13,
  rr_ctor (0,0,0,3) 4 [] None 42]"

definition "is_longest_prefix_routing \<equiv> sorted \<circ> map routing_rule_sort_key"

definition correct_routing :: "('i::len) prefix_routing \<Rightarrow> bool" where 
  "correct_routing r \<equiv> is_longest_prefix_routing r \<and> valid_prefixes r"
text\<open>Many proofs and functions around routing require at least parts of @{const correct_routing} as an assumption.
Obviously, @{const correct_routing} is not given for arbitrary routing tables. Therefore,
@{const correct_routing} is made to be executable and should be checked for any routing table after parsing.
Note: @{const correct_routing} used to also require @{const has_default_route},
but none of the proofs require it anymore and it is not given for any routing table.\<close>

lemma is_longest_prefix_routing_rule_exclusion:
  assumes "is_longest_prefix_routing (r1 # rn # rss)"
  shows "is_longest_prefix_routing (r1 # rss)"
using assms by(case_tac rss) (auto simp add: is_longest_prefix_routing_def)

lemma int_of_nat_less: "int_of_nat a < int_of_nat b \<Longrightarrow> a < b" by (simp add: int_of_nat_def)

lemma is_longest_prefix_routing_sorted_by_length:
  assumes "is_longest_prefix_routing r"
     and "r = r1 # rs @ r2 # rss"
  shows "(pfxm_length (routing_match r1) \<ge> pfxm_length (routing_match r2))"
using assms
proof(induction rs arbitrary: r)
  case (Cons rn rs)
  let ?ro = "r1 # rs @ r2 # rss"
  have "is_longest_prefix_routing ?ro" using Cons.prems is_longest_prefix_routing_rule_exclusion[of r1 rn "rs @ r2 # rss"] by simp
  from Cons.IH[OF this] show ?case by simp
next
  case Nil thus ?case by(auto simp add: is_longest_prefix_routing_def routing_rule_sort_key_def linord_helper_less_eq1_def less_eq_linord_helper_def int_of_nat_def)    
qed

definition "sort_rtbl :: ('i::len) routing_rule list \<Rightarrow> 'i routing_rule list \<equiv> sort_key routing_rule_sort_key"

lemma is_longest_prefix_routing_sort: "is_longest_prefix_routing (sort_rtbl r)" unfolding sort_rtbl_def is_longest_prefix_routing_def by simp

definition "unambiguous_routing rtbl \<equiv> (\<forall>rt1 rt2 rr ra. rtbl = rt1 @ rr # rt2 \<longrightarrow> ra \<in> set (rt1 @ rt2) \<longrightarrow> routing_match rr = routing_match ra \<longrightarrow> routing_rule_sort_key rr \<noteq> routing_rule_sort_key ra)"
lemma unambiguous_routing_Cons: "unambiguous_routing (r # rtbl) \<Longrightarrow> unambiguous_routing rtbl"
  unfolding unambiguous_routing_def by(clarsimp) (metis append_Cons in_set_conv_decomp)
lemma "unambiguous_routing (rr # rtbl) \<Longrightarrow> is_longest_prefix_routing (rr # rtbl) \<Longrightarrow> ra \<in> set rtbl \<Longrightarrow> routing_match rr = routing_match ra \<Longrightarrow> routing_rule_sort_key rr < routing_rule_sort_key ra"
  unfolding is_longest_prefix_routing_def unambiguous_routing_def by(fastforce simp add: sorted_Cons)
primrec unambiguous_routing_code where
"unambiguous_routing_code [] = True" |
"unambiguous_routing_code (rr#rtbl) = (list_all (\<lambda>ra. routing_match rr \<noteq> routing_match ra \<or> routing_rule_sort_key rr \<noteq> routing_rule_sort_key ra) rtbl \<and> unambiguous_routing_code rtbl)"
lemma unambiguous_routing_code[code_unfold]: "unambiguous_routing rtbl \<longleftrightarrow> unambiguous_routing_code rtbl"
proof(induction rtbl)
  case (Cons rr rtbl) show ?case (is "?l \<longleftrightarrow> ?r") proof
    assume l: ?l
    with unambiguous_routing_Cons Cons.IH have "unambiguous_routing_code rtbl" by blast
    moreover have "list_all (\<lambda>ra. routing_match rr \<noteq> routing_match ra \<or> routing_rule_sort_key rr \<noteq> routing_rule_sort_key ra) rtbl"
      using l unfolding unambiguous_routing_def by(fastforce simp add: list_all_iff)
    ultimately show ?r by simp
  next
    assume r: ?r
    with Cons.IH have "unambiguous_routing rtbl" by simp
    from r have *: "list_all (\<lambda>ra. routing_match rr \<noteq> routing_match ra \<or>  routing_rule_sort_key rr \<noteq> routing_rule_sort_key ra) rtbl" by simp
    have False if "rr # rtbl = rt1 @ rra # rt2" "ra \<in> set (rt1 @ rt2)" "routing_rule_sort_key rra = routing_rule_sort_key ra \<and> routing_match rra = routing_match ra" for rt1 rt2 rra ra
    proof(cases "rt1 = []")
      case True thus ?thesis using that * by(fastforce simp add: list_all_iff)
    next
      case False
      with that(1) have rtbl: "rtbl = tl rt1 @ rra # rt2" by (metis list.sel(3) tl_append2)
      show ?thesis proof(cases "ra = hd rt1") (* meh case split\<dots> *)
        case False hence "ra \<in> set (tl rt1 @ rt2)" using that by(cases rt1; simp)
        with \<open>unambiguous_routing rtbl\<close> show ?thesis  using that(3) rtbl unfolding unambiguous_routing_def by fast
      next
        case True hence "rr = ra" using that \<open>rt1 \<noteq> []\<close> by(cases rt1; simp) 
        thus ?thesis using that * unfolding rtbl by(fastforce simp add: list_all_iff)
      qed
    qed
    thus ?l unfolding unambiguous_routing_def by blast 
  qed
qed(simp add: unambiguous_routing_def)

lemma unambigous_prefix_routing_weak_mono:
  assumes lpfx: "is_longest_prefix_routing (rr#rtbl)"
  assumes e:"rr' \<in> set rtbl"
  shows "routing_rule_sort_key rr' \<ge> routing_rule_sort_key rr"
using assms  by(simp add: linorder_class.sorted_Cons is_longest_prefix_routing_def)
lemma unambigous_prefix_routing_strong_mono:
  assumes lpfx: "is_longest_prefix_routing (rr#rtbl)" 
  assumes uam: "unambiguous_routing (rr#rtbl)" 
  assumes e:"rr' \<in> set rtbl"
  assumes ne: "routing_match rr' = routing_match rr"
  shows "routing_rule_sort_key rr' > routing_rule_sort_key rr" 
proof -
  from uam e ne have "routing_rule_sort_key rr \<noteq> routing_rule_sort_key rr'" by(fastforce simp add: unambiguous_routing_def)
  moreover from unambigous_prefix_routing_weak_mono lpfx e have "routing_rule_sort_key rr \<le> routing_rule_sort_key rr'" .
  ultimately show ?thesis by simp
qed

lemma "routing_rule_sort_key (rr_ctor (0,0,0,0) 8 [] None 0) > routing_rule_sort_key (rr_ctor (0,0,0,0) 24 [] None 0)" by eval
(* get the inequality right\<dots> bigger means lower priority *)
text\<open>In case you don't like that formulation of @{const is_longest_prefix_routing} over sorting, this is your lemma.\<close>
theorem existential_routing: "valid_prefixes rtbl \<Longrightarrow> is_longest_prefix_routing rtbl \<Longrightarrow> has_default_route rtbl \<Longrightarrow> unambiguous_routing rtbl \<Longrightarrow>
routing_table_semantics rtbl addr = act \<longleftrightarrow> (\<exists>rr \<in> set rtbl. prefix_match_semantics (routing_match rr) addr \<and> routing_action rr = act \<and>
  (\<forall>ra \<in> set rtbl. routing_rule_sort_key ra < routing_rule_sort_key rr \<longrightarrow> \<not>prefix_match_semantics (routing_match ra) addr))"
proof(induction rtbl)
  case Nil thus ?case by simp
next
  case (Cons rr rtbl)
  show ?case proof(cases "prefix_match_semantics (routing_match rr) addr")
    case False
    hence [simp]: "routing_table_semantics (rr # rtbl) addr = routing_table_semantics (rr # rtbl) addr" by simp
    show ?thesis proof(cases "routing_prefix rr = 0")
      case True text\<open>Need special treatment, rtbl won't have a default route, so the IH is not usable.\<close>
      have "valid_prefix (routing_match rr)" using Cons.prems valid_prefixes_split by blast
      with True False have False using zero_prefix_match_all by blast
      thus ?thesis ..
    next
      case False
      with Cons.prems have mprems: "valid_prefixes rtbl" "is_longest_prefix_routing rtbl" "has_default_route rtbl" "unambiguous_routing rtbl" 
        by(simp_all add: valid_prefixes_split unambiguous_routing_Cons is_longest_prefix_routing_def sorted_Cons)
      show ?thesis using Cons.IH[OF mprems] False \<open>\<not> prefix_match_semantics (routing_match rr) addr\<close> by simp
    qed
  next
    case True
    from True have [simp]: "routing_table_semantics (rr # rtbl) addr = routing_action rr" by simp
    show ?thesis (is "?l \<longleftrightarrow> ?r") proof
      assume ?l
      hence [simp]: "act = routing_action rr" by(simp add: True)
      have *: "(\<forall>ra\<in>set (rr # rtbl). routing_rule_sort_key rr \<le> routing_rule_sort_key ra)"
        using \<open>is_longest_prefix_routing (rr # rtbl)\<close>  by(clarsimp simp: is_longest_prefix_routing_def sorted_Cons)
      thus ?r by(fastforce simp add: True)
    next
      assume ?r
      then guess rr' .. note rr' = this
      have "rr' = rr" proof(rule ccontr)
        assume C: "rr' \<noteq> rr"
        from C have e: "rr' \<in> set rtbl" using rr' by simp
        show False proof cases
          assume eq: "routing_match rr' = routing_match rr"
          with e have "routing_rule_sort_key rr < routing_rule_sort_key rr'" using unambigous_prefix_routing_strong_mono[OF Cons.prems(2,4) _ eq] by simp
          with True rr' show False by simp
        next
          assume ne: "routing_match rr' \<noteq> routing_match rr"
          from rr' Cons.prems have "valid_prefix (routing_match rr)" "valid_prefix (routing_match rr')" "prefix_match_semantics (routing_match rr') addr" by(auto simp add: valid_prefixes_alt_def)
          note same_length_prefixes_distinct[OF this(1,2) ne[symmetric] _ True this(3)]
          moreover have "routing_prefix rr = routing_prefix rr'" (is ?pe) proof -
            have "routing_rule_sort_key rr < routing_rule_sort_key rr' \<longrightarrow> \<not> prefix_match_semantics (routing_match rr) addr" using rr' by simp
            with unambigous_prefix_routing_weak_mono[OF Cons.prems(2) e] True have "routing_rule_sort_key rr = routing_rule_sort_key rr'" by simp
            thus ?pe by(simp add: routing_rule_sort_key_def int_of_nat_def)
          qed
          ultimately show False .
        qed
      qed
      thus ?l using rr' by simp
    qed
  qed
qed
    


subsection\<open>Printing\<close>

definition "routing_rule_32_toString (rr::32 routing_rule) \<equiv> 
  prefix_match_32_toString (routing_match rr) 
@ (case next_hop (routing_action rr) of Some nh \<Rightarrow> '' via '' @ ipv4addr_toString nh | _ \<Rightarrow> [])
@ '' dev '' @ routing_oiface rr 
@ '' metric '' @ string_of_nat (metric rr)"

definition "routing_rule_128_toString (rr::128 routing_rule) \<equiv> 
  prefix_match_128_toString (routing_match rr) 
@ (case next_hop (routing_action rr) of Some nh \<Rightarrow> '' via '' @ ipv6addr_toString nh | _ \<Rightarrow> [])
@ '' dev '' @ routing_oiface rr 
@ '' metric '' @ string_of_nat (metric rr)"

lemma "map routing_rule_32_toString 
[rr_ctor (42,0,0,0) 7 ''eth0'' None 808, 
 rr_ctor (0,0,0,0) 0 ''eth1'' (Some (222,173,190,239)) 707] =
[''42.0.0.0/7 dev eth0 metric 808'',
 ''0.0.0.0/0 via 222.173.190.239 dev eth1 metric 707'']" by eval

section\<open>Routing table to Relation\<close>

text\<open>Walking through a routing table splits the (remaining) IP space when traversing a routing table into a pair of sets:
 the pair contains the IPs concerned by the current rule and those left alone.\<close>
private definition ipset_prefix_match where 
  "ipset_prefix_match pfx rg = (let pfxrg = prefix_to_wordset pfx in (rg \<inter> pfxrg, rg - pfxrg))"
private lemma ipset_prefix_match_m[simp]:  "fst (ipset_prefix_match pfx rg) = rg \<inter> (prefix_to_wordset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
private lemma ipset_prefix_match_nm[simp]: "snd (ipset_prefix_match pfx rg) = rg - (prefix_to_wordset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
private lemma ipset_prefix_match_distinct: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<inter> (snd rpm) = {}" by force
private lemma ipset_prefix_match_complete: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<union> (snd rpm) = rg" by force
private lemma rpm_m_dup_simp: "rg \<inter> fst (ipset_prefix_match (routing_match r) rg) = fst (ipset_prefix_match (routing_match r) rg)"
  by simp
private definition range_prefix_match :: "'i::len prefix_match \<Rightarrow> 'i wordinterval \<Rightarrow> 'i wordinterval \<times> 'i wordinterval" where
  "range_prefix_match pfx rg \<equiv> (let pfxrg = prefix_to_wordinterval pfx in 
  (wordinterval_intersection rg pfxrg, wordinterval_setminus rg pfxrg))"
private lemma range_prefix_match_set_eq:
  "(\<lambda>(r1,r2). (wordinterval_to_set r1, wordinterval_to_set r2)) (range_prefix_match pfx rg) =
    ipset_prefix_match pfx (wordinterval_to_set rg)"
  unfolding range_prefix_match_def ipset_prefix_match_def Let_def 
  using wordinterval_intersection_set_eq wordinterval_setminus_set_eq prefix_to_wordinterval_set_eq  by auto
private lemma range_prefix_match_sm[simp]:  "wordinterval_to_set (fst (range_prefix_match pfx rg)) = 
    fst (ipset_prefix_match pfx (wordinterval_to_set rg))"
  by (metis fst_conv ipset_prefix_match_m  wordinterval_intersection_set_eq prefix_to_wordinterval_set_eq range_prefix_match_def)
private lemma range_prefix_match_snm[simp]: "wordinterval_to_set (snd (range_prefix_match pfx rg)) =
    snd (ipset_prefix_match pfx (wordinterval_to_set rg))"
  by (metis snd_conv ipset_prefix_match_nm wordinterval_setminus_set_eq prefix_to_wordinterval_set_eq range_prefix_match_def)

subsection\<open>Wordintervals for Ports by Routing\<close>
text\<open>This split, although rather trivial, 
can be used to construct the sets (or rather: the intervals) 
of IPs that are actually matched by an entry in a routing table.\<close>

private fun routing_port_ranges :: "'i prefix_routing \<Rightarrow> 'i wordinterval \<Rightarrow> (string \<times> ('i::len) wordinterval) list" where
"routing_port_ranges [] lo = (if wordinterval_empty lo then [] else [(routing_oiface (undefined::'i routing_rule),lo)])" | (* insert default route to nirvana. has to match what routing_table_semantics does. *)
"routing_port_ranges (a#as) lo = (
	let rpm = range_prefix_match (routing_match a) lo; m = fst rpm; nm = snd rpm in (
	(routing_oiface a,m) # routing_port_ranges as nm))"

private lemma routing_port_ranges_subsets:
"(a1, b1) \<in> set (routing_port_ranges tbl s) \<Longrightarrow> wordinterval_to_set b1 \<subseteq> wordinterval_to_set s"
  by(induction tbl arbitrary: s; fastforce simp add: Let_def split: if_splits)

private lemma routing_port_ranges_sound: "e \<in> set (routing_port_ranges tbl s) \<Longrightarrow> k \<in> wordinterval_to_set (snd e) \<Longrightarrow> valid_prefixes tbl \<Longrightarrow>
	fst e = output_iface (routing_table_semantics tbl k)"
proof(induction tbl arbitrary: s)
	case (Cons a as)
	note s = Cons.prems(1)[unfolded routing_port_ranges.simps Let_def list.set]
	note vpfx = valid_prefixes_split[OF Cons.prems(3)] 
	show ?case (is ?kees) proof(cases "e = (routing_oiface a, fst (range_prefix_match (routing_match a) s))")
		case False
		hence es: "e \<in> set (routing_port_ranges as (snd (range_prefix_match (routing_match a) s)))" using s by blast
		note eq = Cons.IH[OF this Cons.prems(2) conjunct2[OF vpfx]]
		have "\<not>prefix_match_semantics (routing_match a) k" (is ?nom)
		proof -
		  from routing_port_ranges_subsets[of "fst e" "snd e", unfolded prod.collapse, OF es]
		  have *: "wordinterval_to_set (snd e) \<subseteq> wordinterval_to_set (snd (range_prefix_match (routing_match a) s))" .
			show ?nom unfolding prefix_match_semantics_wordset[OF conjunct1[OF vpfx]]
			  using * Cons.prems(2)	unfolding wordinterval_subset_set_eq
				by(auto simp add: range_prefix_match_def Let_def)
		qed
		thus ?kees using eq by simp
	next
		case True
		hence fe: "fst e = routing_oiface a" by simp
		from True have "k \<in> wordinterval_to_set (fst (range_prefix_match (routing_match a) s))"
			using Cons.prems(2) by(simp)
		hence "prefix_match_semantics (routing_match a) k" 
			unfolding prefix_match_semantics_wordset[OF conjunct1, OF vpfx]
			unfolding range_prefix_match_def Let_def
			by simp
		thus ?kees by(simp add: fe)
	qed
qed (simp split: if_splits)

private lemma routing_port_ranges_disjoined:
assumes vpfx: "valid_prefixes tbl"
  and ins:  "(a1, b1) \<in> set (routing_port_ranges tbl s)" "(a2, b2) \<in> set (routing_port_ranges tbl s)"
  and nemp: "wordinterval_to_set b1 \<noteq> {}"
shows "b1 \<noteq> b2 \<longleftrightarrow> wordinterval_to_set b1 \<inter> wordinterval_to_set b2 = {}"
using assms
proof(induction tbl arbitrary: s)
  case (Cons r rs)
  have vpfx: "valid_prefix (routing_match r)" "valid_prefixes rs" using Cons.prems(1) using valid_prefixes_split by blast+
  { (* In case that one of b1 b2 stems from r and one does not, we assume it is b1 WLOG. *)
    fix a1 b1 a2 b2
    assume one: "b1 = fst (range_prefix_match (routing_match r) s)"
    assume two: "(a2, b2) \<in> set (routing_port_ranges rs (snd (range_prefix_match (routing_match r) s)))"
    have dc: "wordinterval_to_set (snd (range_prefix_match (routing_match r) s)) \<inter>
          wordinterval_to_set (fst (range_prefix_match (routing_match r) s)) = {}" by force
    hence "wordinterval_to_set b1 \<inter> wordinterval_to_set b2 = {}"
    unfolding one using two[THEN routing_port_ranges_subsets] by fast
  } note * = this
  show ?case
  using \<open>(a1, b1) \<in> set (routing_port_ranges (r # rs) s)\<close> \<open>(a2, b2) \<in> set (routing_port_ranges (r # rs) s)\<close> nemp
    Cons.IH[OF vpfx(2)] * 
    by(fastforce simp add: Let_def)    
qed (simp split: if_splits)

private lemma routing_port_rangesI:
"valid_prefixes tbl \<Longrightarrow>
 output_iface (routing_table_semantics tbl k) = output_port \<Longrightarrow>
 k \<in> wordinterval_to_set wi \<Longrightarrow>
 (\<exists>ip_range. (output_port, ip_range) \<in> set (routing_port_ranges tbl wi) \<and> k \<in> wordinterval_to_set ip_range)"
proof(induction tbl arbitrary: wi)
  case Nil thus ?case by simp blast
next
  case (Cons r rs)
  from Cons.prems(1) have vpfx: "valid_prefix (routing_match r)" and vpfxs: "valid_prefixes rs" 
    by(simp_all add: valid_prefixes_split)
  show ?case
  proof(cases "prefix_match_semantics (routing_match r) k")
    case True
    thus ?thesis 
      using Cons.prems(2) using vpfx \<open>k \<in> wordinterval_to_set wi\<close>
      by (intro exI[where x =  "fst (range_prefix_match (routing_match r) wi)"]) 
         (simp add: prefix_match_semantics_wordset Let_def)
  next
    case False
    with \<open>k \<in> wordinterval_to_set wi\<close> have ksnd: "k \<in> wordinterval_to_set (snd (range_prefix_match (routing_match r) wi))"
      by (simp add: prefix_match_semantics_wordset vpfx)
    have mpr: "output_iface (routing_table_semantics rs k) = output_port" using Cons.prems False by simp
    note Cons.IH[OF vpfxs mpr ksnd]
    thus ?thesis by(fastforce simp: Let_def)
  qed
qed

subsection\<open>Reduction\<close>
text\<open>So far, one entry in the list would be generated for each routing table entry. 
This next step reduces it to one for each port. 
The resulting list will represent a function from port to IP wordinterval.
(It can also be understood as a function from IP (interval) to port (where the intervals don't overlap).\<close>

definition "reduce_range_destination l \<equiv>
let ps = remdups (map fst l) in
let c = \<lambda>s. (wordinterval_Union \<circ> map snd \<circ> filter ((op = s) \<circ> fst)) l in
[(p, c p). p \<leftarrow> ps]
"

definition "routing_ipassmt_wi tbl \<equiv> reduce_range_destination (routing_port_ranges tbl wordinterval_UNIV)"

lemma routing_ipassmt_wi_distinct: "distinct (map fst (routing_ipassmt_wi tbl))"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(simp add: comp_def)

private lemma routing_port_ranges_superseted:
"(a1,b1) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<Longrightarrow> 
  \<exists>b2. (a1,b2) \<in> set (routing_ipassmt_wi tbl) \<and> wordinterval_to_set b1 \<subseteq> wordinterval_to_set b2"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(force simp add: Set.image_iff wordinterval_Union)

private lemma routing_ipassmt_wi_subsetted:
"(a1,b1) \<in> set (routing_ipassmt_wi tbl) \<Longrightarrow> 
 (a1,b2) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<Longrightarrow>  wordinterval_to_set b2 \<subseteq> wordinterval_to_set b1"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(fastforce simp add: Set.image_iff wordinterval_Union comp_def)

text\<open>This lemma should hold without the @{const valid_prefixes} assumption, but that would break the semantic argument and make the proof a lot harder.\<close>
lemma routing_ipassmt_wi_disjoint:
assumes vpfx: "valid_prefixes (tbl::('i::len) prefix_routing)"
  and dif: "a1 \<noteq> a2"
  and ins:  "(a1, b1) \<in> set (routing_ipassmt_wi tbl)" "(a2, b2) \<in> set (routing_ipassmt_wi tbl)"
shows "wordinterval_to_set b1 \<inter> wordinterval_to_set b2 = {}"
proof(rule ccontr)
  note iuf = ins[unfolded routing_ipassmt_wi_def reduce_range_destination_def Let_def, simplified, unfolded Set.image_iff comp_def, simplified]
  assume "(wordinterval_to_set b1 \<inter> wordinterval_to_set b2 \<noteq> {})"
  hence "wordinterval_to_set b1 \<inter> wordinterval_to_set b2 \<noteq> {}" by simp
  text\<open>If the intervals are not disjoint, there exists a witness of that.\<close>
  then obtain x where x[simp]: "x \<in> wordinterval_to_set b1" "x \<in> wordinterval_to_set b2" by blast
  text\<open>This witness has to have come from some entry in the result of @{const routing_port_ranges}, for both of @{term b1} and @{term b2}.\<close>
  hence "\<exists>b1g. x \<in> wordinterval_to_set b1g \<and> wordinterval_to_set b1g \<subseteq> wordinterval_to_set b1 \<and> (a1, b1g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)"
    using iuf(1) by(fastforce simp add: wordinterval_Union) (* strangely, this doesn't work with obtain *)
  then obtain b1g where b1g: "x \<in> wordinterval_to_set b1g" "wordinterval_to_set b1g \<subseteq> wordinterval_to_set b1" "(a1, b1g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)" by clarsimp
  from x have "\<exists>b2g. x \<in> wordinterval_to_set b2g \<and> wordinterval_to_set b2g \<subseteq> wordinterval_to_set b2 \<and> (a2, b2g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)"
    using iuf(2) by(fastforce simp add: wordinterval_Union)
  then obtain b2g where b2g: "x \<in> wordinterval_to_set b2g" "wordinterval_to_set b2g \<subseteq> wordinterval_to_set b2" "(a2, b2g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)" by clarsimp
  text\<open>Soudness tells us that the both @{term a1} and @{term a2} have to be the result of routing @{term x}.\<close>
  note routing_port_ranges_sound[OF b1g(3), unfolded fst_conv snd_conv, OF b1g(1) vpfx] routing_port_ranges_sound[OF b2g(3), unfolded fst_conv snd_conv, OF b2g(1) vpfx]
  text\<open>A contradiction follows from @{thm dif}.\<close>
  with dif show False by simp
qed

lemma routing_ipassmt_wi_sound:
  assumes vpfx: "valid_prefixes tbl"
  and ins: "(ea,eb) \<in> set (routing_ipassmt_wi tbl)"
  and x: "k \<in> wordinterval_to_set eb"
  shows "ea = output_iface (routing_table_semantics tbl k)"
proof -
  note iuf = ins[unfolded routing_ipassmt_wi_def reduce_range_destination_def Let_def, simplified, unfolded Set.image_iff comp_def, simplified]
  from x have "\<exists>b1g. k \<in> wordinterval_to_set b1g \<and> wordinterval_to_set b1g \<subseteq> wordinterval_to_set eb \<and> (ea, b1g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)"
    using iuf(1) by(fastforce simp add: wordinterval_Union)
  then obtain b1g where b1g: "k \<in> wordinterval_to_set b1g" "wordinterval_to_set b1g \<subseteq> wordinterval_to_set eb" "(ea, b1g) \<in> set (routing_port_ranges tbl wordinterval_UNIV)" by clarsimp
  note routing_port_ranges_sound[OF b1g(3), unfolded fst_conv snd_conv, OF b1g(1) vpfx]
  thus ?thesis .
qed

theorem routing_ipassmt_wi:
assumes vpfx: "valid_prefixes tbl"
  shows 
  "output_iface (routing_table_semantics tbl k) = output_port \<longleftrightarrow>
    (\<exists>ip_range. k \<in> wordinterval_to_set ip_range \<and> (output_port, ip_range) \<in> set (routing_ipassmt_wi tbl))"
proof (intro iffI, goal_cases)
  case 2 with vpfx routing_ipassmt_wi_sound show ?case by blast
next
  case 1
  then obtain ip_range where "(output_port, ip_range) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<and> k \<in> wordinterval_to_set ip_range"
    using routing_port_rangesI[where wi = wordinterval_UNIV, OF vpfx] by auto
  thus ?case
    unfolding routing_ipassmt_wi_def reduce_range_destination_def
    unfolding Let_def comp_def
    by(force simp add: Set.image_iff wordinterval_Union)
qed

(* this was not given for the old reduced_range_destination *)
lemma routing_ipassmt_wi_has_all_interfaces:
  assumes in_tbl: "r \<in> set tbl"
  shows "\<exists>s. (routing_oiface r,s) \<in> set (routing_ipassmt_wi tbl)"
proof -
  from in_tbl have "\<exists>s. (routing_oiface r,s) \<in> set (routing_port_ranges tbl S)" for S
  proof(induction tbl arbitrary: S)
    case (Cons l ls)
    show ?case
    proof(cases "r = l")
      case True thus ?thesis using Cons.prems by(auto simp: Let_def)
    next
      case False with Cons.prems have "r \<in> set ls" by simp
      from Cons.IH[OF this] show ?thesis by(simp add: Let_def) blast
    qed
  qed simp
  thus ?thesis
    unfolding routing_ipassmt_wi_def reduce_range_destination_def
    by(force simp add: Set.image_iff)
qed

end

end
