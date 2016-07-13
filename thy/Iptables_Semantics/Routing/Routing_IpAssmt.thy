section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports "../Primitive_Matchers/Ipassmt"
        Routing_Table
begin

context
begin

text\<open>Walking through a routing table splits the (remaining) IP space when traversing a routing table: the pair contains the IPs
  concerned by the current rule and those left alone.\<close>
definition ipset_prefix_match where 
  "ipset_prefix_match pfx rg = (let pfxrg = prefix_to_wordset pfx in (rg \<inter> pfxrg, rg - pfxrg))"
lemma ipset_prefix_match_m[simp]:  "fst (ipset_prefix_match pfx rg) = rg \<inter> (prefix_to_wordset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
lemma ipset_prefix_match_nm[simp]: "snd (ipset_prefix_match pfx rg) = rg - (prefix_to_wordset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
lemma ipset_prefix_match_distinct: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<inter> (snd rpm) = {}" by force
lemma ipset_prefix_match_complete: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<union> (snd rpm) = rg" by force
lemma rpm_m_dup_simp: "rg \<inter> fst (ipset_prefix_match (routing_match r) rg) = fst (ipset_prefix_match (routing_match r) rg)"
  by simp
definition range_prefix_match :: "'a::len prefix_match \<Rightarrow> 'a wordinterval \<Rightarrow> 'a wordinterval \<times> 'a wordinterval" where
  "range_prefix_match pfx rg \<equiv> (let pfxrg = prefix_to_wordinterval pfx in 
  (wordinterval_intersection rg pfxrg, wordinterval_setminus rg pfxrg))"
lemma range_prefix_match_set_eq:
  "(\<lambda>(r1,r2). (wordinterval_to_set r1, wordinterval_to_set r2)) (range_prefix_match pfx rg) =
    ipset_prefix_match pfx (wordinterval_to_set rg)"
  unfolding range_prefix_match_def ipset_prefix_match_def Let_def 
  using wordinterval_intersection_set_eq wordinterval_setminus_set_eq prefix_to_wordinterval_set_eq  by auto
lemma range_prefix_match_sm[simp]:  "wordinterval_to_set (fst (range_prefix_match pfx rg)) = 
    fst (ipset_prefix_match pfx (wordinterval_to_set rg))"
  by (metis fst_conv ipset_prefix_match_m  wordinterval_intersection_set_eq prefix_to_wordinterval_set_eq range_prefix_match_def)
lemma range_prefix_match_snm[simp]: "wordinterval_to_set (snd (range_prefix_match pfx rg)) =
    snd (ipset_prefix_match pfx (wordinterval_to_set rg))"
  by (metis snd_conv ipset_prefix_match_nm wordinterval_setminus_set_eq prefix_to_wordinterval_set_eq range_prefix_match_def)

subsection\<open>Wordintervals for Ports by Routing\<close>

private fun routing_port_ranges :: "prefix_routing \<Rightarrow> 32 wordinterval \<Rightarrow> (string \<times> 32 wordinterval) list" where
"routing_port_ranges [] lo = (if wordinterval_empty lo then [] else [(routing_oiface (undefined::routing_rule),lo)])" | (* insert default route to nirvana. has to match what routing_table_semantics does. *)
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

(* There are a lot of unnamed lemmas in this theory / on routing_port_ranges. Some of them I might want to use in the future, but most are just here because they're insight-providing. *)

lemma
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

subsection\<open>Reduction\<close>
text\<open>So far, one entry in the list would be generated for each routing table entry. This reduces it to one for each port. The resulting list will represent a function from port to wordinterval.\<close>

private definition "reduce_range_destination l \<equiv>
let ps = remdups (map fst l) in
let c = \<lambda>s. (wordinterval_Union \<circ> map snd \<circ> filter ((op = s) \<circ> fst)) l in
[(p, c p). p \<leftarrow> ps]
"

private definition "routing_ipassmt_wi tbl \<equiv> reduce_range_destination (routing_port_ranges tbl wordinterval_UNIV)"

lemma routing_ipassmt_wi_distinct: "distinct (map fst (routing_ipassmt_wi tbl))"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(simp add: comp_def)

(*TODO: names*)

lemma "(a1,b1) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<Longrightarrow> 
  \<exists>b2. wordinterval_to_set b1 \<subseteq> wordinterval_to_set b2 \<and> (a1,b2) \<in> set (routing_ipassmt_wi tbl)"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(force simp add: Set.image_iff wordinterval_Union)

lemma
"(a1,b1) \<in> set (routing_ipassmt_wi tbl) \<Longrightarrow> 
 (a1,b2) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<Longrightarrow>  wordinterval_to_set b2 \<subseteq> wordinterval_to_set b1"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(fastforce simp add: Set.image_iff wordinterval_Union comp_def)

lemma
"(a1,b1) \<in> set (routing_ipassmt_wi tbl) \<Longrightarrow> w \<in> wordinterval_to_set b1 \<Longrightarrow>
 (a1,b2) \<in> set (routing_port_ranges tbl wordinterval_UNIV) \<Longrightarrow>  wordinterval_to_set b2 \<subseteq> wordinterval_to_set b1"
  unfolding routing_ipassmt_wi_def reduce_range_destination_def
  by(fastforce simp add: Set.image_iff wordinterval_Union comp_def)

text\<open>From a pure, technical standpoint, this lemma should hold without the @{const valid_prefixes} assumption, but that would break the semantic argument and make the proof a lot harder.\<close>
lemma routing_ipassmt_wi_disjoint:
assumes vpfx: "valid_prefixes tbl"
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

theorem assumes "valid_prefixes tbl"
  shows 
  "output_iface (routing_table_semantics tbl k) = output_port \<longleftrightarrow>
    (\<exists>ip_range. k \<in> wordinterval_to_set ip_range \<and> (output_port, ip_range) \<in> set (routing_ipassmt_wi tbl))"
  apply(rule)
   defer
   apply(elim exE)
   using assms routing_ipassmt_wi_sound apply blast
  oops (*TODO*)

(* this was not given for the old reduced_range_destination *)
lemma
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
    by(force simp add:  Set.image_iff)
qed

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

end

(* TODO: move all of these*)
subsection\<open>IP Assignment difference\<close>
definition "option2wordinterval s \<equiv> (case s of None \<Rightarrow> Empty_WordInterval | Some s \<Rightarrow> ipcidr_tuple_to_wordinterval  s)"
definition "ip_assmt_diff a b \<equiv> let
t = \<lambda>s. (case s of None \<Rightarrow> Empty_WordInterval | Some s \<Rightarrow> ipcidr_tuple_to_wordinterval s);
k = \<lambda>x y d. cidr_split (wordinterval_setminus (t (x d)) (t (y d))) in
{(d, k a b d, k b a d)| d. d \<in> (dom a \<union> dom b)}
"

end
