theory CIDRSplit
imports IPv4Addr NumberWangCaesar
begin


context
begin

section{*CIDR Split Motivation*}
  text{*When talking about ranges of IP addresses, we can make the ranges explicit by listing them.*}

  lemma "map (ipv4addr_of_nat \<circ> nat) [1 .. 4] = [1, 2, 3, 4]" by eval
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

private definition prefix_to_range :: "prefix_match \<Rightarrow> 32 wordinterval" where
  "prefix_to_range pfx = WordInterval (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"
private lemma prefix_to_range_set_eq: "wordinterval_to_set (prefix_to_range pfx) = prefix_to_ipset pfx"
  unfolding prefix_to_range_def prefix_to_ipset_def by simp

private lemma prefix_to_range_ipv4range_range: "prefix_to_range pfx = ipv4range_range ((pfxm_prefix pfx), (pfxm_prefix pfx OR pfxm_mask pfx))"
  unfolding ipv4range_range.simps prefix_to_range_def by simp

private corollary "valid_prefix pfx \<Longrightarrow> wordinterval_to_set (prefix_to_range pfx) = ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)"
using wordinterval_to_set_ipv4range_set_from_bitmask prefix_to_range_set_eq by simp


private lemma prefix_match_list_union: "\<forall> pfx \<in> set cidrlist. (valid_prefix pfx) \<Longrightarrow>
   (\<Union> x \<in> set (map prefix_to_range cidrlist). wordinterval_to_set x) = (\<Union>pfx\<in>set cidrlist. ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx))"
  apply simp
  apply(induction cidrlist)
   apply(simp; fail)
  apply(simp)
  apply(subst prefix_to_range_set_eq)
  apply(subst wordinterval_to_set_ipv4range_set_from_bitmask)
   apply(simp; fail)
  apply(simp)
  done


private lemma "\<Union>((\<lambda>(base, len). ipv4range_set_from_bitmask base len) ` prefix_match_to_CIDR ` set (cidrlist)) =
      \<Union>((\<lambda>pfx. ipv4range_set_from_bitmask (pfxm_prefix pfx) (pfxm_length pfx)) ` set (cidrlist))"
unfolding prefix_match_to_CIDR_def2 by blast 


private definition pfxes :: "nat list" where "pfxes \<equiv> map nat [0..32]"

(* Split of one range *)
definition ipv4range_split1 :: "32 wordinterval \<Rightarrow> prefix_match option \<times> 32 wordinterval" where
  "ipv4range_split1 r \<equiv> (
   let ma = ipv4range_lowest_element r in
   case ma of None \<Rightarrow> (None, r) |
              Some a \<Rightarrow> let cs = (map (\<lambda>s. PrefixMatch a s) pfxes) in
                        let cfs = filter (\<lambda>s. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r) cs in (* anything that is a subset should also be a valid prefix. but try prooving that.*)
                        let mc = find (const True) cfs in 
                        (case mc of None \<Rightarrow> (None, r) |
                                  Some m \<Rightarrow> (mc, ipv4range_setminus r (prefix_to_range m))))"

private lemma flipnot: "a=b \<Longrightarrow> (\<not>a)=(\<not>b)" by simp (* not flipknot *)

private lemma "find (const True) cfs = (if cfs = [] then None else Some (hd cfs))"
by(induction cfs) (simp_all split: split_if_asm add: const_def)

private lemma find_const_True: "find (const True) l = None \<longleftrightarrow> l = []"
  by(cases l, simp_all add: const_def) 
private lemma ipv4range_split_innard_helper: "ipv4range_lowest_element r = Some a \<Longrightarrow> 
  [s \<leftarrow> map (\<lambda>s. PrefixMatch a s) pfxes. valid_prefix s \<and> ipv4range_to_set (prefix_to_range s) \<subseteq> ipv4range_to_set r] \<noteq> []"
proof -
  assume a: "ipv4range_lowest_element r = Some a"
  have b: "(a,32) \<in> set (map (Pair a) pfxes)"
    unfolding pfxes_def
    unfolding set_map set_upto
    using  Set.image_iff atLeastAtMost_iff int_eq_iff of_nat_numeral order_refl
    by (metis (erased, hide_lams))
  have c: "valid_prefix (PrefixMatch a 32)" unfolding valid_prefix_def pfxm_mask_def by simp
  have "ipv4range_to_set (prefix_to_range (PrefixMatch a 32)) = {a}" unfolding prefix_to_range_def pfxm_mask_def by simp
  moreover have "a \<in> ipv4range_to_set r" using a ipv4range_lowest_element_set_eq ipv4range_lowest_none_empty
    by (metis is_lowest_element_def option.distinct(1))
  ultimately have d: "ipv4range_to_set (prefix_to_range (PrefixMatch a 32)) \<subseteq> ipv4range_to_set r" by simp
  show ?thesis
    unfolding flipnot[OF set_empty[symmetric]]
    apply simp
    using b c d by auto
qed
private lemma r_split1_not_none: "\<not>ipv4range_empty r \<Longrightarrow> fst (ipv4range_split1 r) \<noteq> None"
  unfolding ipv4range_split1_def Let_def
  apply(cases "ipv4range_lowest_element r")
   apply(simp add: ipv4range_lowest_none_empty; fail)
  apply(simp only:)
  apply(case_tac "find (const True) [s\<leftarrow>map (\<lambda>s. PrefixMatch a s) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r]")
   apply(simp add: find_const_True ipv4range_split_innard_helper; fail)
  apply(simp)
done
private lemma find_in: "Some a = find f s \<Longrightarrow> a \<in> {x \<in> set s. f x}"
  by (metis findSomeD mem_Collect_eq)
private theorem ipv4range_split1_preserve: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> ipv4range_eq (ipv4range_union (prefix_to_range s) u) r"
proof(unfold ipv4range_eq_set_eq)
  assume as: "(Some s, u) = ipv4range_split1 r"
  have nn: "ipv4range_lowest_element r \<noteq> None"
    using as unfolding ipv4range_split1_def Let_def
    by (metis (erased, lifting) Pair_inject option.distinct(2) option.simps(4))
  then obtain a where a:  "Some a = (ipv4range_lowest_element r)" unfolding not_None_eq by force
  then have cpf: "find (const True) [s\<leftarrow>map (\<lambda>s. PrefixMatch a s) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r] \<noteq> None" (is "?cpf \<noteq> None")
    unfolding flipnot[OF find_const_True]
    using ipv4range_split_innard_helper
    by simp
  then obtain m where m: "m = the ?cpf" by blast
  have s_def: "ipv4range_split1 r =
    (find (const True) [s\<leftarrow>map (\<lambda>s. PrefixMatch a s) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r], ipv4range_setminus r (prefix_to_range m))"
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

definition ipv4range_split1_2 :: "32 wordinterval \<Rightarrow> prefix_match option \<times> 32 wordinterval" where
  "ipv4range_split1_2 r \<equiv> (
   let ma = ipv4range_lowest_element r in
   case ma of None \<Rightarrow> (None, r) |
              Some a \<Rightarrow> let cs = (map (\<lambda>s. PrefixMatch a s) pfxes);
                            ms = (filter (\<lambda>s. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r) cs) in
                            (Some (hd ms), ipv4range_setminus r (prefix_to_range (hd ms))))"

private lemma hd_find_const: "l \<noteq> [] \<Longrightarrow> hd l = the (find (const True) l)"
proof -
	assume "l \<noteq> []" then obtain a ls where [simp]: "l = a # ls" by(cases l) blast+
	then show "hd l = the (find (const True) l)" by(simp add: const_def)
qed

lemma ipv4range_split1_2_eq[code]: "ipv4range_split1 s = ipv4range_split1_2 s"
	apply(simp add: ipv4range_split1_2_def ipv4range_split1_def split: option.splits)
	apply(clarify)
	apply(frule hd_find_const[OF ipv4range_split_innard_helper])
	apply(simp split: option.splits add: Let_def)
	apply(rule ccontr)
	apply(unfold not_ex not_Some_eq find_const_True)
	apply(drule ipv4range_split_innard_helper)
	apply simp
done

private lemma "((a,b),(c,d)) = ((a,b),c,d)" by simp (* Fuck. *)

private lemma prefix_never_empty: "\<not>ipv4range_empty (prefix_to_range d)"
proof -
  have ie: "pfxm_prefix d \<le> pfxm_prefix d || pfxm_mask d" by (metis le_word_or2)
  have "ipv4range_element (pfxm_prefix d) (prefix_to_range d)"
    unfolding ipv4range_element_set_eq
    unfolding ipv4range_to_set_def
    unfolding prefix_to_range_set_eq
    unfolding prefix_to_ipset_def 
    using first_in_uptoD[OF ie]
    .
  thus ?thesis
    unfolding ipv4range_empty_set_eq
    unfolding ipv4range_element_set_eq
    by blast
qed

private lemma ipv4range_split1_never_empty: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> \<not>ipv4range_empty (prefix_to_range s)"
  unfolding ipv4range_split1_def Let_def
  using prefix_never_empty
  by simp

private lemma ipv4range_split1_some_r_ne: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> \<not>ipv4range_empty r"
proof(rule ccontr)
  case goal1
  have "ipv4range_lowest_element r = None" unfolding ipv4range_lowest_none_empty using goal1(2) unfolding not_not .
  then have "ipv4range_split1 r = (None, r)" unfolding ipv4range_split1_def Let_def by simp
  then show False using goal1(1) by simp
qed

private lemma ipv4range_split1_distinct: "(Some s, u) = ipv4range_split1 r \<Longrightarrow> ipv4range_empty (ipv4range_intersection (prefix_to_range s) u)"
proof -
  case goal1
  note ne = ipv4range_split1_never_empty[OF goal1]
  have nn: "ipv4range_lowest_element r \<noteq> None" using ipv4range_split1_some_r_ne[OF goal1, unfolded ipv4range_lowest_none_empty[symmetric]] .
  obtain a where ad: "Some a = ipv4range_lowest_element r" using nn by force
  {
    fix rr :: "prefix_match \<Rightarrow> 'a option \<times> 32 wordinterval"
    have "(case find (const True) [s\<leftarrow>map (PrefixMatch a) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r] of None \<Rightarrow> (None, r)
                 | Some m \<Rightarrow> rr m) = rr (the (find (const True) [s\<leftarrow>map (PrefixMatch a) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) r]))"
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
private lemma "ipv4range_empty r \<longleftrightarrow> fst (ipv4range_split1 r) = None"
by (metis (no_types, lifting) Pair_inject case_option_If2 ipv4range_lowest_none_empty ipv4range_split1_def prod.collapse r_split1_not_none) 

function ipv4range_split_internal :: "32 wordinterval \<Rightarrow> prefix_match list"where
  "ipv4range_split_internal rs = (if \<not>ipv4range_empty rs then case ipv4range_split1 rs of (Some s, u) \<Rightarrow> s # ipv4range_split_internal u | _ \<Rightarrow> [] else [])"
  by(simp, blast)

termination ipv4range_split_internal
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

private lemma unfold_rsplit_case:
  assumes su: "(Some s, u) = ipv4range_split1 rs"
  shows "(case ipv4range_split1 rs of (None, u) \<Rightarrow> [] | (Some s, u) \<Rightarrow> s # ipv4range_split_internal u) = s # ipv4range_split_internal u"
using su by (metis option.simps(5) split_conv)

private lemma ipv4range_split_internal_union: "\<Union>set (map wordinterval_to_set (map prefix_to_range (ipv4range_split_internal r))) = wordinterval_to_set r"
proof(induction r rule: ipv4range_split_internal.induct, subst ipv4range_split_internal.simps, case_tac "ipv4range_empty rs")
  case goal1
  show ?case using goal1(2) by (simp add: ipv4range_to_set_def)
next
  case goal2
  obtain u s where su: "(Some s, u) = ipv4range_split1 rs" using r_split1_not_none[OF goal2(2)] by (metis option.collapse surjective_pairing)
  from goal2(1)[OF goal2(2) su, of s] have mIH: "\<Union>set (map wordinterval_to_set (map prefix_to_range (ipv4range_split_internal u))) = wordinterval_to_set u" by presburger
  from ipv4range_split1_preserve[OF su, unfolded ipv4range_eq_set_eq ipv4range_to_set_def ipv4range_union_def] have
    helper1: "wordinterval_to_set (prefix_to_range s) \<union> wordinterval_to_set u = wordinterval_to_set rs"
    unfolding wordinterval_union_set_eq by simp
  show ?case
    unfolding eqTrueI[OF goal2(2)]
    unfolding if_True
    unfolding unfold_rsplit_case[OF su]
    unfolding list.map
    using mIH helper1
    by (metis Sup_insert list.set(2))
qed

(* Wolololo *)
lemma "ipv4range_split_internal
          (RangeUnion (WordInterval (ipv4addr_of_dotdecimal (64,0,0,0))         (ipv4addr_of_dotdecimal (95, 239, 187, 204)))
                      (WordInterval (ipv4addr_of_dotdecimal (95, 238, 187, 28)) (ipv4addr_of_dotdecimal (127,255,255,255))))
       = [PrefixMatch (ipv4addr_of_dotdecimal (64, 0, 0, 0)) 2]" by eval
lemma "length (ipv4range_split_internal (WordInterval 0 (ipv4addr_of_dotdecimal (255,255,255,254)))) = 32" by eval



(*
text{* @{text "10.0.0.0/8 - 10.8.0.0/16"}*}
lemma "map (\<lambda>pfx. (dotdecimal_of_ipv4addr (pfxm_prefix pfx), (pfxm_length pfx))) (ipv4range_split_internal (ipv4range_setminus
          (ipv4range_range ((ipv4addr_of_dotdecimal (10,0,0,0)), (ipv4addr_of_dotdecimal (10,255,255,255))))
          (ipv4range_range ((ipv4addr_of_dotdecimal (10,8,0,0)), (ipv4addr_of_dotdecimal (10,8,255,255)))))) =
 [((10, 0, 0, 0), 13), ((10, 9, 0, 0), 16), ((10, 10, 0, 0), 15), ((10, 12, 0, 0), 14), ((10, 16, 0, 0), 12), ((10, 32, 0, 0), 11), ((10, 64, 0, 0), 10),
  ((10, 128, 0, 0), 9)]" 
  by eval


lemma "map (\<lambda>pfx. (dotdecimal_of_ipv4addr (pfxm_prefix pfx), (pfxm_length pfx))) (ipv4range_split_internal (
    (ipv4range_range ((ipv4addr_of_dotdecimal (10,0,0,1)), (ipv4addr_of_dotdecimal (10,0,0,15)))))) =
    [((10, 0, 0, 1), 32), ((10, 0, 0, 2), 31), ((10, 0, 0, 4), 30), ((10, 0, 0, 8), 29)]" by eval
*)

declare ipv4range_split_internal.simps[simp del]

private corollary ipv4range_split_internal: "(\<Union> (prefix_to_ipset ` (set (ipv4range_split_internal r)))) = wordinterval_to_set r"
  proof -
  have prefix_to_range_set_eq_fun: "prefix_to_ipset = (wordinterval_to_set \<circ> prefix_to_range)"
    by(simp add: prefix_to_range_set_eq fun_eq_iff)
  have "\<Union>(prefix_to_ipset ` set (ipv4range_split_internal r)) =
        UNION (set (map prefix_to_range (ipv4range_split_internal r))) wordinterval_to_set"
    by(simp add: prefix_to_range_set_eq_fun)
  thus ?thesis
   using ipv4range_split_internal_union by simp
qed
private corollary ipv4range_split_internal_single: "(\<Union> (prefix_to_ipset ` (set (ipv4range_split_internal (WordInterval start end))))) = {start .. end}"
  using ipv4range_split_internal by simp

private lemma ipv4range_split_internal_all_valid_Ball: "Ball (set (ipv4range_split_internal r)) valid_prefix"
proof(induction r rule: ipv4range_split_internal.induct, subst ipv4range_split_internal.simps, case_tac "ipv4range_empty rs")
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
    obtain m where m: "find (const True) [s\<leftarrow>map (PrefixMatch a) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs] = Some m"
      using ipv4range_split_innard_helper[OF a, unfolded flipnot[OF find_const_True, symmetric]]
      by force
    note su[unfolded ipv4range_split1_def Let_def]
    then have "(Some s, u) =
          (case find (const True) [s\<leftarrow>map (PrefixMatch a) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs] of None \<Rightarrow> (None, rs)
           | Some m \<Rightarrow> (find (const True) [s\<leftarrow>map (PrefixMatch a) pfxes. valid_prefix s \<and> ipv4range_subset (prefix_to_range s) rs], ipv4range_setminus rs (prefix_to_range m)))"
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

text{*Since @{const ipv4range_split_internal} only returns valid prefixes, we can safely convert it to CIDR lists*}

definition ipv4range_split :: "32 wordinterval \<Rightarrow> (32 word \<times> nat) list" where
  "ipv4range_split rs \<equiv> map prefix_match_to_CIDR (ipv4range_split_internal rs)"

(*also works with corny definitions*)
corollary ipv4range_split_bitmask: 
  "(\<Union> ((\<lambda> (base, len). ipv4range_set_from_bitmask base len) ` (set (ipv4range_split r))) ) = wordinterval_to_set r"
  proof -
  --"without valid prefix assumption"
  have prefix_to_ipset_subset_ipv4range_set_from_bitmask_helper:
    "\<And>X. (\<Union>x\<in>X. prefix_to_ipset x) \<subseteq> (\<Union>x\<in>X. ipv4range_set_from_bitmask (pfxm_prefix x) (pfxm_length x))"
    apply(rule)
    using prefix_to_ipset_subset_ipv4range_set_from_bitmask by fastforce

  have ipv4range_set_from_bitmask_subseteq_prefix_to_ipset_helper:
    "\<And>X. \<forall> x \<in> X. valid_prefix x \<Longrightarrow> (\<Union>x\<in>X. ipv4range_set_from_bitmask (pfxm_prefix x) (pfxm_length x)) \<subseteq> (\<Union>x\<in>X. prefix_to_ipset x)"
    using wordinterval_to_set_ipv4range_set_from_bitmask by auto

  show ?thesis
    unfolding ipv4range_split_internal[symmetric] ipv4range_split_def
    apply(simp add: ipv4range_range_def prefix_match_to_CIDR_def2)
    apply(rule)
     apply(simp add: ipv4range_set_from_bitmask_subseteq_prefix_to_ipset_helper ipv4range_split_internal_all_valid_Ball)
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
