theory CIDRSplit
imports IPv4Addr NumberWangCaesar
begin

context
begin

section{*CIDR Split Motivation*}
  text{*When talking about ranges of IP addresses, we can make the ranges explicit by listing them.*}

  value "map (ipv4addr_of_nat \<circ> nat) [1 .. 4]"
  definition ipv4addr_upto :: "ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> ipv4addr list" where
    "ipv4addr_upto i j \<equiv> map (ipv4addr_of_nat \<circ> nat) [int (nat_of_ipv4addr i) .. int (nat_of_ipv4addr j)]"
  lemma ipv4addr_upto: "set (ipv4addr_upto i j) = {i .. j}"
    proof -
    have helpX:"\<And>f (i::nat) (j::nat). (f \<circ> nat) ` {int i..int j} = f ` {i .. j}"
      apply(intro set_eqI)
      apply(safe)
       apply(force)
      by (metis Set_Interval.transfer_nat_int_set_functions(2) image_comp image_eqI)
    have ipv4addr_of_nat_def': "ipv4addr_of_nat = of_nat" using ipv4addr_of_nat_def fun_eq_iff by presburger
    show ?thesis
      unfolding ipv4addr_upto_def
      apply(intro set_eqI)
      apply(simp add: ipv4addr_of_nat_def' nat_of_ipv4addr_def)
      apply(safe)
        apply(simp_all)
        apply (metis (no_types, hide_lams) le_unat_uoi nat_mono uint_nat unat_def word_le_nat_alt)
       apply (metis (no_types, hide_lams) le_unat_uoi nat_mono uint_nat unat_def word_le_nat_alt)
      apply(simp add: helpX)
      by (metis atLeastAtMost_iff image_eqI word_le_nat_alt word_unat.Rep_inverse)
    qed

  text{*The function @{const ipv4addr_upto} gives back a list of all the ips in the list.
        This list can be pretty huge! In the following, we will use CIDR notation (e.g. 192.168.0.0/24)
        to describe the list more compactly. *}

subsection{*Prefix Match Range stuff*}

definition prefix_to_range :: "prefix_match \<Rightarrow> 32 wordinterval" where
  "prefix_to_range pfx = WordInterval (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"
lemma prefix_to_range_set_eq: "wordinterval_to_set (prefix_to_range pfx) = prefix_to_ipset pfx"
  unfolding prefix_to_range_def prefix_to_ipset_def by simp

lemma prefix_to_range_ipv4range_range: "prefix_to_range pfx = ipv4range_range ((pfxm_prefix pfx), (pfxm_prefix pfx OR pfxm_mask pfx))"
  unfolding ipv4range_range.simps prefix_to_range_def by simp

corollary "valid_prefix pfx \<Longrightarrow> wordinterval_to_set (prefix_to_range pfx) = ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)"
using wordinterval_to_set_ipv4range_set_from_bitmask prefix_to_range_set_eq by simp


lemma prefix_bitrang_list_union: "\<forall> pfx \<in> set cidrlist. (valid_prefix pfx) \<Longrightarrow>
       wordinterval_to_set (list_to_wordinterval (map prefix_to_range cidrlist)) = \<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` set (cidrlist))"
       apply(induction cidrlist)
        apply(simp)
       apply(simp)
       apply(subst prefix_to_range_set_eq)
       apply(subst wordinterval_to_set_ipv4range_set_from_bitmask)
        apply(simp)
       apply(simp add: pfxm_prefix_def pfxm_length_def)
       apply(clarify)
       apply(simp)
       done

(*TODO: move*)
lemma prefix_to_ipset_subset_ipv4range_set_from_bitmask: 
    "prefix_to_ipset pfx \<subseteq> ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)"
  apply(rule)
  apply(simp add: prefix_to_ipset_def addr_in_ipv4range_set_from_bitmask_code)
  apply(intro impI conjI)
   apply (metis (erased, hide_lams) order_trans word_and_le2)
  by (metis pfxm_mask_def)


private definition pfxes :: "nat list" where "pfxes \<equiv> map nat [0..32]"

(* Split of one range *)
definition "ipv4range_split1 r \<equiv> (
   let ma = ipv4range_lowest_element r in
   case ma of None \<Rightarrow> (None, r) |
              Some a \<Rightarrow> let cs = (map (\<lambda>s. (a,s)) pfxes) in
                        let cfs = filter (\<lambda>s. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r) cs in (* anything that is a valid prefix should also be a subset. but try prooving that.*)
                        let mc = find (const True) cfs in 
                        (case mc of None \<Rightarrow> (None, r) |
                                  Some m \<Rightarrow> (mc, ipv4range_setminus r (prefix_to_range m))))"

private lemma flipnot: "a=b \<Longrightarrow> (\<not>a)=(\<not>b)" by simp (* not flipknot *)

private lemma find_const_True: "find (const True) l = None \<longleftrightarrow> l = []"
  by(cases l, simp_all add: const_def) 
private lemma ipv4range_split_innard_helper: "ipv4range_lowest_element r = Some a \<Longrightarrow> 
  [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_to_set (prefix_to_range s) \<subseteq> ipv4range_to_set r] \<noteq> []"
proof -
  assume a: "ipv4range_lowest_element r = Some a"
  have b: "(a,32) \<in> set (map (Pair a) pfxes)"
    unfolding pfxes_def
    unfolding set_map set_upto
    using  Set.image_iff atLeastAtMost_iff int_eq_iff of_nat_numeral order_refl
    by (metis (erased, hide_lams))
  have c: "valid_prefix (a,32)" unfolding valid_prefix_def pfxm_defs by simp
  have "ipv4range_to_set (prefix_to_range (a,32)) = {a}" unfolding prefix_to_range_def pfxm_defs by simp
  moreover have "a \<in> ipv4range_to_set r" using a ipv4range_lowest_element_set_eq ipv4range_lowest_none_empty
    by (metis is_lowest_element_def option.distinct(1))
  ultimately have d: " ipv4range_to_set (prefix_to_range (a,32)) \<subseteq> ipv4range_to_set r" by simp
  show ?thesis
    unfolding flipnot[OF set_empty[symmetric]]
    unfolding set_filter
    using b c d by blast
qed
private lemma r_split1_not_none: "\<not>ipv4range_empty r \<Longrightarrow> fst (ipv4range_split1 r) \<noteq> None"
  unfolding ipv4range_split1_def Let_def
  apply(cases "ipv4range_lowest_element r")
   apply(simp add: ipv4range_lowest_none_empty)
  apply(simp only:)
  apply(case_tac "find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r]")
   apply(simp add: find_const_True ipv4range_split_innard_helper)
  apply(simp)
done
private lemma find_in: "Some a = find f s \<Longrightarrow> a \<in> {x \<in> set s. f x}"
  by (metis findSomeD mem_Collect_eq)
theorem ipv4range_split1_preserve: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> ipv4range_eq (ipv4range_union (prefix_to_range s) u) r"
proof(unfold ipv4range_eq_set_eq)
  assume as: "(Some s, u) = ipv4range_split1 r"
  have nn: "ipv4range_lowest_element r \<noteq> None"
    using as unfolding ipv4range_split1_def Let_def
    by (metis (erased, lifting) Pair_inject option.distinct(2) option.simps(4))
  then obtain a where a:  "Some a = (ipv4range_lowest_element r)" unfolding not_None_eq by force
  then have cpf: "find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r] \<noteq> None" (is "?cpf \<noteq> None")
    unfolding flipnot[OF find_const_True]
    using ipv4range_split_innard_helper
    by simp
  then obtain m where m: "m = the ?cpf" by blast
  have s_def: "ipv4range_split1 r =
    (find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r], ipv4range_setminus r (prefix_to_range m))"
    unfolding m ipv4range_split1_def Let_def using cpf
    unfolding a[symmetric]
    unfolding option.simps(5)
    using option.collapse
    by force
  have "u = ipv4range_setminus r (prefix_to_range s)"
    using as unfolding s_def using m by (metis (erased, lifting) Pair_inject handy_lemma)
  moreover have "ipv4range_subset (prefix_to_range s) r"
    using as unfolding s_def
    apply(rule Pair_inject)
    apply(unfold const_def)
    apply(drule find_in)
    apply(unfold set_filter)
    by blast
  ultimately show "ipv4range_to_set (ipv4range_union (prefix_to_range s) u) = ipv4range_to_set r" by auto
qed

private lemma "((a,b),(c,d)) = ((a,b),c,d)" by simp (* Fuck. *)

private lemma prefix_never_empty: "\<not>ipv4range_empty (prefix_to_range d)"
proof -
  have ie: "pfxm_prefix d \<le> pfxm_prefix d || pfxm_mask d" by (metis le_word_or2)
  have "ipv4range_element (fst d) (prefix_to_range d)"
    unfolding ipv4range_element_set_eq
    unfolding ipv4range_to_set_def
    unfolding prefix_to_range_set_eq
    unfolding prefix_to_ipset_def 
    using first_in_uptoD[OF ie] 
    unfolding pfxm_defs
    .
  thus ?thesis
    unfolding ipv4range_empty_set_eq
    unfolding ipv4range_element_set_eq
    by blast
qed

lemma ipv4range_split1_never_empty: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> \<not>ipv4range_empty (prefix_to_range s)"
  unfolding ipv4range_split1_def Let_def
  using prefix_never_empty
  by simp

lemma ipv4range_split1_some_r_ne: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> \<not>ipv4range_empty r"
proof(rule ccontr)
  case goal1
  have "ipv4range_lowest_element r = None" unfolding ipv4range_lowest_none_empty using goal1(2) unfolding not_not .
  then have "ipv4range_split1 r = (None, r)" unfolding ipv4range_split1_def Let_def by simp
  then show False using goal1(1) by simp
qed

lemma ipv4range_split1_distinct: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> ipv4range_empty (ipv4range_intersection (prefix_to_range s) u)"
proof -
  case goal1
  note ne = ipv4range_split1_never_empty[OF goal1]
  have nn: "ipv4range_lowest_element r \<noteq> None" using ipv4range_split1_some_r_ne[OF goal1, unfolded ipv4range_lowest_none_empty[symmetric]] .
  obtain a where ad: "Some a = ipv4range_lowest_element r" using nn by force
  {
    fix rr :: "32 word \<times> nat \<Rightarrow> 'a option \<times> 32 wordinterval"
    have "(case find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r] of None \<Rightarrow> (None, r)
                 | Some m \<Rightarrow> rr m) = rr (the (find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r]))"
                  using ipv4range_split_innard_helper[OF ad[symmetric]] find_const_True by fastforce
  } note uf2 = this
  from goal1 have "u = ipv4range_setminus r (prefix_to_range s)"
    unfolding ipv4range_split1_def Let_def
    unfolding ad[symmetric] option.cases
    unfolding uf2
    unfolding Pair_eq
    by (metis option.sel)
  then show ?thesis by force
qed

function ipv4range_split :: "32 wordinterval \<Rightarrow> (ipv4addr \<times> nat) list"where
  "ipv4range_split rs = (if \<not>ipv4range_empty rs then case ipv4range_split1 rs of (Some s, u) \<Rightarrow> s # ipv4range_split u | _ \<Rightarrow> [] else [])"
  by(simp, blast)

termination ipv4range_split
proof(relation "measure (card \<circ> ipv4range_to_set)", rule wf_measure, unfold in_measure comp_def)
  note vernichter = ipv4range_empty_set_eq ipv4range_intersection_set_eq ipv4range_union_set_eq ipv4range_eq_set_eq
  case goal1
  note some = goal1(2)[unfolded goal1(3)]
  from ipv4range_split1_never_empty[OF this] have "\<not> ipv4range_empty (prefix_to_range x2)" .
  thus ?case
    unfolding vernichter
    unfolding ipv4range_split1_preserve[OF some, unfolded vernichter, symmetric]
    unfolding card_Un_disjoint[OF finite finite ipv4range_split1_distinct[OF some, unfolded vernichter]]
    by (metis add.commute add_left_cancel card_0_eq finite linorder_neqE_nat monoid_add_class.add.right_neutral not_add_less1)
qed

lemma unfold_rsplit_case:
  assumes su: "(Some s, u) = ipv4range_split1 rs"
  shows "(case ipv4range_split1 rs of (None, u) \<Rightarrow> [] | (Some s, u) \<Rightarrow> s # ipv4range_split u) = s # ipv4range_split u"
using su by (metis option.simps(5) split_conv)

lemma ipv4range_split_union: "ipv4range_eq (list_to_wordinterval (map prefix_to_range (ipv4range_split r))) r"
proof(induction r rule: ipv4range_split.induct, subst ipv4range_split.simps, case_tac "ipv4range_empty rs")
  case goal1
  thm Empty_WordInterval_set_eq ipv4range_eq_set_eq[of Empty_WordInterval rs, unfolded ipv4range_to_set_def Empty_WordInterval_set_eq]
  show ?case using goal1(2)
    by(simp add: ipv4range_eq_set_eq[of Empty_WordInterval rs, unfolded ipv4range_to_set_def Empty_WordInterval_set_eq] ipv4range_to_set_def)
next
  case goal2
  obtain u s where su: "(Some s, u) = ipv4range_split1 rs" using r_split1_not_none[OF goal2(2)] by (metis option.collapse surjective_pairing)
  note mIH = goal2(1)[OF goal2(2) su, of s]
  show ?case
    unfolding eqTrueI[OF goal2(2)]
    unfolding if_True
    unfolding unfold_rsplit_case[OF su]
    unfolding ipv4range_eq_set_eq
    unfolding ipv4range_to_set_def
    unfolding list.map
    unfolding list_to_wordinterval_set_eq_simp
    using mIH[unfolded ipv4range_eq_set_eq ipv4range_to_set_def]
    using ipv4range_split1_preserve[OF su, unfolded ipv4range_eq_set_eq ipv4range_to_set_def ipv4range_union_def]
    unfolding wordinterval_union_set_eq
    by presburger
qed

(* Wolololo *)
value "ipv4range_split (RangeUnion (WordInterval (ipv4addr_of_dotdecimal (64,0,0,0)) 0x5FEFBBCC) (WordInterval 0x5FEEBB1C (ipv4addr_of_dotdecimal (127,255,255,255))))"
value "ipv4range_split (WordInterval 0 (ipv4addr_of_dotdecimal (255,255,255,254)))"


text{* @{text "10.0.0.0/8 - 10.8.0.0/16"}*}
lemma "map (\<lambda>(ip,n). (dotdecimal_of_ipv4addr ip, n)) (ipv4range_split (ipv4range_setminus
          (ipv4range_range ((ipv4addr_of_dotdecimal (10,0,0,0)), (ipv4addr_of_dotdecimal (10,255,255,255))))
          (ipv4range_range ((ipv4addr_of_dotdecimal (10,8,0,0)), (ipv4addr_of_dotdecimal (10,8,255,255)))))) =
 [((10, 0, 0, 0), 13), ((10, 9, 0, 0), 16), ((10, 10, 0, 0), 15), ((10, 12, 0, 0), 14), ((10, 16, 0, 0), 12), ((10, 32, 0, 0), 11), ((10, 64, 0, 0), 10),
  ((10, 128, 0, 0), 9)]" by eval

declare ipv4range_split.simps[simp del]

corollary ipv4range_split: "(\<Union> (prefix_to_ipset ` (set (ipv4range_split r)))) = wordinterval_to_set r"
  proof -
  have prefix_to_range_set_eq_fun: "prefix_to_ipset = (wordinterval_to_set \<circ> prefix_to_range)"
    by(simp add: prefix_to_range_set_eq fun_eq_iff)

  { fix r
    have "\<Union>((wordinterval_to_set \<circ> prefix_to_range) ` set (ipv4range_split r))= 
        (wordinterval_to_set (list_to_wordinterval (map prefix_to_range (ipv4range_split r))))"
        by (metis (erased, lifting) list.map_comp list_to_wordinterval_set_eq set_map)
    also have "\<dots> = (wordinterval_to_set r)"
      by (metis ipv4range_eq_set_eq ipv4range_split_union ipv4range_to_set_def)
    finally have "\<Union>((wordinterval_to_set \<circ> prefix_to_range) ` set (ipv4range_split r)) = wordinterval_to_set r" .
  } note ipv4range_eq_eliminator=this[of r]

  show ?thesis
  unfolding prefix_to_range_set_eq_fun
  using ipv4range_eq_eliminator by auto
qed
corollary ipv4range_split_single: "(\<Union> (prefix_to_ipset ` (set (ipv4range_split (WordInterval start end))))) = {start .. end}"
  using ipv4range_split by simp

lemma all_valid_Ball: "Ball (set (ipv4range_split r)) valid_prefix"
proof(induction r rule: ipv4range_split.induct, subst ipv4range_split.simps, case_tac "ipv4range_empty rs")
  case goal1 thus ?case
    by(simp only: not_True_eq_False if_False Ball_def set_simps empty_iff) clarify
next
  case goal2
  obtain u s where su: "(Some s, u) = ipv4range_split1 rs" using r_split1_not_none[OF goal2(2)] by (metis option.collapse surjective_pairing)
  note mIH = goal2(1)[OF goal2(2) su refl]
  have vpfx: "valid_prefix s"
  proof -
    obtain a where a: "ipv4range_lowest_element rs = Some a"
      using goal2(2)[unfolded flipnot[OF ipv4range_lowest_none_empty, symmetric]]
      by force
    obtain m where m: "find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs] = Some m"
      using ipv4range_split_innard_helper[OF a, unfolded flipnot[OF find_const_True, symmetric]]
      by force
    note su[unfolded ipv4range_split1_def Let_def]
    then have "(Some s, u) =
          (case find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs] of None \<Rightarrow> (None, rs)
           | Some m \<Rightarrow> (find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs], ipv4range_setminus rs (prefix_to_range m)))"
       unfolding a by simp
    then have "(Some s, u) =
          (Some m, ipv4range_setminus rs (prefix_to_range m))"
       unfolding m by simp
    moreover
    note find_in[OF m[symmetric]]
    ultimately
    show "valid_prefix s" by simp
  qed
  show ?case
    unfolding eqTrueI[OF goal2(2)]
    unfolding if_True
    unfolding unfold_rsplit_case[OF su]
    unfolding list.set
    using mIH vpfx
    by blast
qed


(*also works with corny definitions*)
corollary ipv4range_split_bitmask: 
  "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipv4range_split r))) ) = wordinterval_to_set r"
  proof -
  --"without valid prefix assumption"
  have prefix_to_ipset_subset_ipv4range_set_from_bitmask_helper:
    "\<And>X. (\<Union>x\<in>X. prefix_to_ipset x) \<subseteq> (\<Union>x\<in>X. case x of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa)"
    apply(rule)
    using prefix_to_ipset_subset_ipv4range_set_from_bitmask[simplified pfxm_prefix_def pfxm_length_def] by fastforce

  have ipv4range_set_from_bitmask_subseteq_prefix_to_ipset_helper:
    "\<And>X. \<forall> x \<in> X. valid_prefix x \<Longrightarrow> (\<Union>x\<in>X. case x of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa) \<subseteq> (\<Union>x\<in>X. prefix_to_ipset x)"
    apply(rule)
    apply(rename_tac x)
    apply(safe)
    apply(rename_tac a b)
    apply(erule_tac x="(a,b)" in ballE)
     apply(simp_all)
    apply(drule wordinterval_to_set_ipv4range_set_from_bitmask)
    apply(rule_tac x="(a, b)" in bexI)
    apply(simp_all add: pfxm_prefix_def pfxm_length_def)
    done

  show ?thesis
    unfolding ipv4range_split[symmetric]
    apply(simp add: ipv4range_range_def)
    apply(rule)
     apply(simp add: ipv4range_set_from_bitmask_subseteq_prefix_to_ipset_helper all_valid_Ball)
    apply(simp add: prefix_to_ipset_subset_ipv4range_set_from_bitmask_helper)
    done
qed
corollary ipv4range_split_bitmask_single: 
  "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipv4range_split (ipv4range_range (start, end))))) ) = {start .. end}"
using ipv4range_split_bitmask ipv4range_range.simps by simp


(*
lemma "(\<Union> (base, len) \<in> set (ipv4range_split (ipv4range_range start end)). ipv4range_set_from_bitmask base len) = {start .. end}"
(*using [[simp_trace, simp_trace_depth_limit=10]]*)
using [[simproc del: list_to_set_comprehension]] (* okay, simplifier is a bit broken **)
  apply(simp del: ) (*simp: "Tactic failed"*)
  oops
*)

end

end
