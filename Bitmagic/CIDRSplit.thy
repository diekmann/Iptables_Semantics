theory CIDRSplit
imports IPv4Addr NumberWangCaesar
begin

subsection{*Prefix Match Range stuff*}

definition prefix_to_range :: "prefix_match \<Rightarrow> 32 bitrange" where
  "prefix_to_range pfx = Bitrange (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"
lemma prefix_to_range_set_eq: "bitrange_to_set (prefix_to_range pfx) = prefix_to_ipset pfx"
  unfolding prefix_to_range_def prefix_to_ipset_def by simp

lemma prefix_to_range_ipv4range_range: "prefix_to_range pfx = ipv4range_range (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"
  unfolding ipv4range_range_def prefix_to_range_def by simp

(*declare[[show_types]]
declare[[unify_trace_failure]]*)
lemma bitrange_to_set_ipv4range_set_from_bitmask:  assumes "valid_prefix pfx"
      shows "bitrange_to_set (prefix_to_range pfx) = ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)"
proof-
  have prefix_match_if_in_corny_set: "(prefix_to_ipset pfx) = ipv4range_set_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
    unfolding prefix_to_ipset_def ipv4range_set_from_netmask_def Let_def
    unfolding word_bool_alg.double_compl
    proof -
      case goal1
      have *: "pfxm_prefix pfx AND NOT pfxm_mask pfx = pfxm_prefix pfx"
        unfolding mask_eq_0_eq_x[symmetric] using valid_prefix_E[OF assms] word_bw_comms(1)[of "pfxm_prefix pfx"] by simp
      hence **: "pfxm_prefix pfx AND NOT pfxm_mask pfx OR pfxm_mask pfx = pfxm_prefix pfx OR pfxm_mask pfx"
        by simp
      show ?case unfolding * ** ..
    qed
    
    have "\<And>len. ((mask len)::ipv4addr) << 32 - len = ~~ mask (32 - len)"
    using maskshift_eq_not_mask by simp
    from this[of "(pfxm_length pfx)"] have mask_def2_symmetric: "((mask (pfxm_length pfx)::ipv4addr) << 32 - pfxm_length pfx) = NOT pfxm_mask pfx"
      unfolding pfxm_mask_def by simp

    have ipv4range_set_from_netmask_bitmask: 
      "ipv4range_set_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) = ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)"
     unfolding ipv4range_set_from_netmask_def ipv4range_set_from_bitmask_alt
     unfolding pfxm_mask_def[symmetric]
     unfolding mask_def2_symmetric
     apply(simp)
     unfolding Let_def
     thm pfxm_mask_def
     using assms[simplified valid_prefix_def] by (metis helper3 word_bw_comms(2)) 
    
    show ?thesis by (metis ipv4range_set_from_netmask_bitmask local.prefix_match_if_in_corny_set prefix_to_range_set_eq) 
qed

definition pfxes :: "nat list" where "pfxes \<equiv> map nat [0..32]"

(* Split of one range *)
definition "ipv4range_split1 r \<equiv> (
   let ma = ipv4range_lowest_element r in
   case ma of None \<Rightarrow> (None, r) |
              Some a \<Rightarrow> let cs = (map (\<lambda>s. (a,s)) pfxes) in
                        let cfs = filter (\<lambda>s. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r) cs in (* anything that is a valid prefix should also be a subset. but try prooving that.*)
                        let mc = find (const True) cfs in 
                        (case mc of None \<Rightarrow> (None, r) |
                                  Some m \<Rightarrow> (mc, ipv4range_setminus r (prefix_to_range m))))"

lemma flipnot: "a=b \<Longrightarrow> (\<not>a)=(\<not>b)" by simp (* not flipknot *)

lemma find_const_True: "find (const True) l = None \<longleftrightarrow> l = []"
  by(cases l, simp_all add: const_def) 
lemma ipv4range_split_innard_helper: "ipv4range_lowest_element r = Some a \<Longrightarrow> 
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
lemma r_split1_not_none: "\<not>ipv4range_empty r \<Longrightarrow> fst (ipv4range_split1 r) \<noteq> None"
  unfolding ipv4range_split1_def Let_def
  apply(cases "ipv4range_lowest_element r")
   apply(simp add: ipv4range_lowest_none_empty)
  apply(simp only:)
  apply(case_tac "find (const True) [s\<leftarrow>map (Pair a) pfxes . valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r]")
   apply(simp add: find_const_True ipv4range_split_innard_helper)
  apply(simp)
done
lemma find_in: "Some a = find f s \<Longrightarrow> a \<in> {x \<in> set s. f x}"
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

lemma "((a,b),(c,d)) = ((a,b),c,d)" by simp (* Fuck. *)

lemma prefix_never_empty: "\<not>ipv4range_empty (prefix_to_range d)"
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
    fix rr :: "32 word \<times> nat \<Rightarrow> 'a option \<times> 32 bitrange"
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

function ipv4range_split :: "32 bitrange \<Rightarrow> (ipv4addr \<times> nat) list"where
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

lemma ipv4range_split_union: "ipv4range_eq (list_to_bitrange (map prefix_to_range (ipv4range_split r))) r"
proof(induction r rule: ipv4range_split.induct, subst ipv4range_split.simps, case_tac "ipv4range_empty rs")
  case goal1
  thm Empty_Bitrange_set_eq ipv4range_eq_set_eq[of Empty_Bitrange rs, unfolded ipv4range_to_set_def Empty_Bitrange_set_eq]
  show ?case using goal1(2)
    by(simp add: ipv4range_eq_set_eq[of Empty_Bitrange rs, unfolded ipv4range_to_set_def Empty_Bitrange_set_eq] ipv4range_to_set_def)
next
  case goal2
  obtain u s where su: "(Some s, u) = ipv4range_split1 rs" using r_split1_not_none[OF goal2(2)] by (metis option.collapse surjective_pairing)
  note mIH = goal2(1)[OF goal2(2) su, of s]
  have uf: "(case ipv4range_split1 rs of (None, u) \<Rightarrow> [] | (Some s, u) \<Rightarrow> s # ipv4range_split u) = s # ipv4range_split u"
    using su by (metis option.simps(5) split_conv)
  show ?case
    unfolding eqTrueI[OF goal2(2)]
    unfolding if_True
    unfolding uf
    unfolding ipv4range_eq_set_eq
    unfolding ipv4range_to_set_def
    unfolding list.map
    unfolding list_to_bitrange_set_eq_simp
    using mIH[unfolded ipv4range_eq_set_eq ipv4range_to_set_def]
    using ipv4range_split1_preserve[OF su, unfolded ipv4range_eq_set_eq ipv4range_to_set_def ipv4range_union_def]
    unfolding bitrange_union_set_eq
    by presburger
qed

(* Wolololo *)
value "ipv4range_split (RangeUnion (Bitrange (ipv4addr_of_dotteddecimal (64,0,0,0)) 0x5FEFBBCC) (Bitrange 0x5FEEBB1C (ipv4addr_of_dotteddecimal (127,255,255,255))))"
value "ipv4range_split (Bitrange 0 (ipv4addr_of_dotteddecimal (255,255,255,254)))"


lemma "(\<Union> (base, len) \<in> set (ipv4range_split (ipv4range_range start end)). ipv4range_set_from_bitmask base len) = {start .. end}"
using [[simp_trace, simp_trace_depth_limit=10]]
  apply(simp) (*simp: "Tactic failed"*)
  oops
end
