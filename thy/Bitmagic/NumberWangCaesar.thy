theory NumberWangCaesar
imports "./IPv4Addr" "./l4v/lib/WordLemmaBucket"
begin

(*Contributed by Julius Michaelis*)

text{*We define a type for ips in CIDR notation, e.g. 192.168.0.0/24.*}
(*datatype prefix_match = PrefixMatch (pfxm_prefix: ipv4addr) (pfxm_length: nat)*)
datatype 'a prefix_match = PrefixMatch (pfxm_prefix: "'a::len word") (pfxm_length: nat)
(*definition "pfxm_mask x \<equiv> mask (32 - pfxm_length x)"*)

definition "prefix_match_less_eq1 a b = (if pfxm_length a = pfxm_length b then pfxm_prefix a \<le> pfxm_prefix b else pfxm_length a > pfxm_length b)"
instantiation prefix_match :: (len) linorder
begin
	definition "a \<le> b \<longleftrightarrow> prefix_match_less_eq1 a b"
	definition "a < b \<longleftrightarrow> (a \<noteq> b \<and> prefix_match_less_eq1 a b)"
instance
by default (auto simp: less_eq_prefix_match_def less_prefix_match_def prefix_match.expand prefix_match_less_eq1_def split: if_splits)
end

value "sorted_list_of_set {PrefixMatch 0 32 :: 32 prefix_match, PrefixMatch 42 32, PrefixMatch 0 0, PrefixMatch 0 1, PrefixMatch 12 31}"

context
begin

definition pfxm_mask :: "'a prefix_match \<Rightarrow> 'a::len word" where
  "pfxm_mask x \<equiv> mask ((len_of (TYPE('a))) - pfxm_length x)"

(*
(*TODO: wo could use this to generalize to arbitrary word lengths*)
definition pfxm_mask :: "prefix_match \<Rightarrow> 'a::len word" where
  "pfxm_mask x \<equiv> mask ((len_of TYPE ('a)) - pfxm_length x)"
*)


definition valid_prefix :: "('a::len) prefix_match \<Rightarrow> bool" where
  "valid_prefix pf = ((pfxm_mask pf) AND pfxm_prefix pf = 0)"

text{*The type @{typ "'a prefix_match"} usually requires @{const valid_prefix}.
      When we allow working on arbitrary IPs in CIDR notation, we will use the type @{typ "(ipv4addr \<times> nat)"} directly.*}

(*TODO: generalize to 'a::len word*)
definition prefix_match_to_CIDR :: "32 prefix_match \<Rightarrow> (ipv4addr \<times> nat)" where
  "prefix_match_to_CIDR pfx \<equiv> (pfxm_prefix pfx, pfxm_length pfx)"
lemma prefix_match_to_CIDR_def2: "prefix_match_to_CIDR \<equiv> \<lambda>pfx. (pfxm_prefix pfx, pfxm_length pfx)"
  using prefix_match_to_CIDR_def by presburger


private lemma valid_prefix_E: "valid_prefix pf \<Longrightarrow> ((pfxm_mask pf) AND pfxm_prefix pf = 0)" 
  unfolding valid_prefix_def .
private lemma valid_preifx_alt_def: fixes p::"'a::len prefix_match"
  shows "valid_prefix p = (pfxm_prefix p AND (2 ^ ((len_of TYPE ('a)) - pfxm_length p) - 1) = 0)"
  unfolding valid_prefix_def
  unfolding mask_def
  using word_bw_comms(1)
   arg_cong[where f = "\<lambda>x. (pfxm_prefix p AND x - 1 = 0)"]
   shiftl_1
  unfolding pfxm_prefix_def pfxm_mask_def mask_def
  by metis


subsection{*Address Semantics*}


definition prefix_match_semantics where
"prefix_match_semantics m a = (pfxm_prefix m = (NOT pfxm_mask m) AND a)"

(*private lemma mask_32_max_word: "mask 32 = (max_word :: 32 word)" using WordLemmaBucket.mask_32_max_word by simp*)

subsection{*Set Semantics*}

definition prefix_to_ipset :: "'a::len prefix_match \<Rightarrow> 'a word set" where
  "prefix_to_ipset pfx = {pfxm_prefix pfx .. pfxm_prefix pfx OR pfxm_mask pfx}"

private lemma pfx_not_empty: "valid_prefix pfx \<Longrightarrow> prefix_to_ipset pfx \<noteq> {}"
  unfolding valid_prefix_def prefix_to_ipset_def by(simp add: le_word_or2)

 definition ipset_prefix_match where 
  "ipset_prefix_match pfx rg = (let pfxrg = prefix_to_ipset pfx in (rg \<inter> pfxrg, rg - pfxrg))"
private lemma ipset_prefix_match_m[simp]:  "fst (ipset_prefix_match pfx rg) = rg \<inter> (prefix_to_ipset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
private lemma ipset_prefix_match_nm[simp]: "snd (ipset_prefix_match pfx rg) = rg - (prefix_to_ipset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
private lemma ipset_prefix_match_distinct: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<inter> (snd rpm) = {}" by force
private lemma ipset_prefix_match_complete: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<union> (snd rpm) = rg" by force
private lemma rpm_m_dup_simp: "rg \<inter> fst (ipset_prefix_match (routing_match r) rg) = fst (ipset_prefix_match (routing_match r) rg)"
  by simp


lemma prefix_to_ipset_subset_ipv4range_set_from_prefix: 
    "prefix_to_ipset pfx \<subseteq> ipv4range_set_from_prefix (pfxm_prefix pfx) (pfxm_length pfx)"
  apply(rule subsetI)
  apply(simp add: prefix_to_ipset_def addr_in_ipv4range_set_from_prefix_code)
  apply(intro impI conjI)
   apply (metis (erased, hide_lams) order_trans word_and_le2)
  apply(simp add: pfxm_mask_def)
  done

subsection{*Equivalence Proofs*}

private lemma helper3: "(x::'a::len word) OR y = x OR y AND NOT x" by (simp add: word_oa_dist2)
(*private lemma helper1: "NOT (0\<Colon>32 word) = x\<^sub>1\<^sub>9 OR NOT x\<^sub>1\<^sub>9" using word_bool_alg.double_compl by simp
private lemma helper2: "(x\<^sub>0\<Colon>32 word) AND NOT 0 = x\<^sub>0" by simp*)

private lemma packet_ipset_prefix_eq1:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "\<not>prefix_match_semantics match addr" 
  shows "addr \<in> (snd (ipset_prefix_match match addrrg))"
using assms
proof -
  have "pfxm_prefix match \<le> addr \<Longrightarrow> \<not> addr \<le> pfxm_prefix match OR pfxm_mask match"
  proof -
    case goal1
    have a1: "pfxm_mask match AND pfxm_prefix match = 0"
      using assms(2) unfolding valid_prefix_def .
    have a2: "pfxm_prefix match \<noteq> NOT pfxm_mask match AND addr"
      using assms(3) unfolding prefix_match_semantics_def .
    have f1: "pfxm_prefix match = pfxm_prefix match AND NOT pfxm_mask match"
      using a1 by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f2: "\<forall>x\<^sub>1\<^sub>1. (pfxm_prefix match OR x\<^sub>1\<^sub>1) AND NOT pfxm_mask match = pfxm_prefix match OR x\<^sub>1\<^sub>1 AND NOT pfxm_mask match"
      by (metis word_bool_alg.conj_disj_distrib2)
    moreover
    { assume "\<not> pfxm_prefix match \<le> addr AND NOT pfxm_mask match"
      hence "\<not> (pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match OR pfxm_mask match)"
        using f1 neg_mask_mono_le unfolding pfxm_prefix_def pfxm_mask_def by metis }
    moreover
    { assume "pfxm_prefix match \<le> addr AND NOT pfxm_mask match \<and> addr AND NOT pfxm_mask match \<noteq> (pfxm_prefix match OR pfxm_mask match) AND NOT pfxm_mask match"
      hence "\<exists>x\<^sub>0. \<not> addr AND NOT mask x\<^sub>0 \<le> (pfxm_prefix match OR pfxm_mask match) AND NOT mask x\<^sub>0"
        using f2 unfolding pfxm_prefix_def pfxm_mask_def by (metis dual_order.antisym word_bool_alg.conj_cancel_right word_log_esimps(3))
      hence "\<not> (pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match OR pfxm_mask match)"
        using neg_mask_mono_le by auto }
    ultimately show "?case"
      using a2 by (metis goal1 word_bool_alg.conj_cancel_right word_bool_alg.conj_commute word_log_esimps(3))
  qed
  from this show ?thesis using assms(1)
    unfolding ipset_prefix_match_def Let_def snd_conv prefix_to_ipset_def
    by simp
qed

private lemma packet_ipset_prefix_eq2:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "prefix_match_semantics match addr" 
  shows "addr \<in> (fst (ipset_prefix_match match addrrg))"
using assms
  apply(subst ipset_prefix_match_def)
  apply(simp only: Let_def fst_def)
  apply(simp add: prefix_to_ipset_def)
  apply(transfer)
  apply(simp only: prefix_match_semantics_def valid_prefix_def)
  apply(simp add: word_and_le1)
  apply(metis helper3 le_word_or2 word_bw_comms(1) word_bw_comms(2))
done

private lemma packet_ipset_prefix_eq3:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "addr \<in> (snd (ipset_prefix_match match addrrg))"
  shows "\<not>prefix_match_semantics match addr"
using assms
  apply(subst(asm) ipset_prefix_match_def)
  apply(simp only: Let_def fst_def)
  apply(simp)
  apply(subst(asm) prefix_to_ipset_def)
  apply(transfer)
  apply(simp only: prefix_match_semantics_def valid_prefix_def Set_Interval.ord_class.atLeastAtMost_iff prefix_to_ipset_def)
  apply(simp)
  apply(metis helper3 le_word_or2 word_and_le2 word_bw_comms(1) word_bw_comms(2))
done

private lemma packet_ipset_prefix_eq4:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "addr \<in> (fst (ipset_prefix_match match addrrg))"
  shows "prefix_match_semantics match addr"
using assms
proof -
  have "pfxm_prefix match = NOT pfxm_mask match AND addr"
  proof -
    have a1: "pfxm_mask match AND pfxm_prefix match = 0" using assms(2) unfolding valid_prefix_def .
    have a2: "pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match OR pfxm_mask match"
      using assms(3) unfolding ipset_prefix_match_def Let_def fst_conv prefix_to_ipset_def by simp
    have f2: "\<forall>x\<^sub>0. pfxm_prefix match AND NOT mask x\<^sub>0 \<le> addr AND NOT mask x\<^sub>0"
      using a2 neg_mask_mono_le by blast
    have f3: "\<forall>x\<^sub>0. addr AND NOT mask x\<^sub>0 \<le> (pfxm_prefix match OR pfxm_mask match) AND NOT mask x\<^sub>0"
      using a2 neg_mask_mono_le by blast
    have f4: "pfxm_prefix match = pfxm_prefix match AND NOT pfxm_mask match"
      using a1 by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f5: "\<forall>x\<^sub>6. (pfxm_prefix match OR x\<^sub>6) AND NOT pfxm_mask match = pfxm_prefix match OR x\<^sub>6 AND NOT pfxm_mask match"
      using word_ao_dist by (metis)
    have f6: "\<forall>x\<^sub>2 x\<^sub>3. addr AND NOT mask x\<^sub>2 \<le> x\<^sub>3 \<or> \<not> (pfxm_prefix match OR pfxm_mask match) AND NOT mask x\<^sub>2 \<le> x\<^sub>3"
      using f3 dual_order.trans by auto
    have "pfxm_prefix match = (pfxm_prefix match OR pfxm_mask match) AND NOT pfxm_mask match"
      using f5 by auto
    hence "pfxm_prefix match = addr AND NOT pfxm_mask match"
      using f2 f4 f6 unfolding pfxm_prefix_def pfxm_mask_def by (metis eq_iff)
    thus "pfxm_prefix match = NOT pfxm_mask match AND addr"
      by (metis word_bw_comms(1))
  qed
  from this show ?thesis unfolding prefix_match_semantics_def .
qed

private lemma packet_ipset_prefix_eq24:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "prefix_match_semantics match addr = (addr \<in> (fst (ipset_prefix_match match addrrg)))"
using packet_ipset_prefix_eq2[OF assms] packet_ipset_prefix_eq4[OF assms] by fast

private lemma packet_ipset_prefix_eq13:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "\<not>prefix_match_semantics match addr = (addr \<in> (snd (ipset_prefix_match match addrrg)))"
using packet_ipset_prefix_eq1[OF assms] packet_ipset_prefix_eq3[OF assms] by fast

private lemma prefix_match_if_in_my_set: assumes "valid_prefix pfx" 
  shows "prefix_match_semantics pfx (a :: ipv4addr) \<longleftrightarrow> a \<in> prefix_to_ipset pfx"
  using packet_ipset_prefix_eq24[OF _ assms]
by (metis (erased, hide_lams) Int_iff UNIV_I fst_conv ipset_prefix_match_def)

lemma prefix_match_if_in_corny_set: 
  assumes "valid_prefix pfx"
  shows "prefix_match_semantics pfx (a :: ipv4addr) \<longleftrightarrow> a \<in> ipv4range_set_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
  unfolding prefix_match_if_in_my_set[OF assms]
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


(*TODO move*)
private lemma ipv4addr_and_maskshift_eq_and_not_mask: "(base::32 word) AND (mask m << 32 - m) = base AND NOT mask (32 - m)"
  apply word_bitwise
  apply (subgoal_tac "m > 32 \<or> m \<in> set (map nat (upto 0 32))")
   apply (simp add: upto_code upto_aux_rec, elim disjE)
                                    apply (simp add: size_mask_32word)
                                  apply (simp_all add: size_mask_32word) [33]
  apply (simp add: upto_code upto_aux_rec, presburger)
done

(*TODO: should be private*)
lemma maskshift_eq_not_mask: "((mask m << 32 - m) :: 32 word) = NOT mask (32 - m)"
  apply word_bitwise
  apply (subgoal_tac "m > 32 \<or> m \<in> set (map nat (upto 0 32))")
   apply (simp add: upto_code upto_aux_rec, elim disjE)
                                    apply (simp add: size_mask_32word)
                                  apply (simp_all add: size_mask_32word) [33]
  apply (simp add: upto_code upto_aux_rec, presburger)
done

private lemma ipv4addr_andnotmask_eq_ormaskandnot: "((base::32 word) AND NOT mask (32 - m)) = ((base OR mask (32 - m)) AND NOT mask (32 - m))"
  apply word_bitwise
  apply (subgoal_tac "m > 32 \<or> m \<in> set (map nat (upto 0 32))")
   apply (simp add: upto_code upto_aux_rec, elim disjE)
                                    apply (simp add: size_mask_32word)
                                  apply (simp_all add: size_mask_32word) [33]
  apply (simp add: upto_code upto_aux_rec, presburger)
done

(* we needed this lemma once. It is commented out because the proof is slow. No comment about its overwhelming elegance.
As of commit 225779834c209401231eeec664adcc756701c5f7, isabelle 2015, it is still working, but horribly slow.
private lemma ipv4addr_andnot_eq_takem: "(a::32 word) AND NOT mask (32 - m) = b AND NOT mask (32 - m) \<longleftrightarrow> (take (m) (to_bl a)) = (take (m) (to_bl b))"
  apply word_bitwise
  apply (subgoal_tac "m > 32 \<or> m \<in> set (map nat (upto 0 32))")
   apply (simp add: upto_code upto_aux_rec, elim disjE)
                                    apply (simp_all add: size_mask_32word) [34]
                                  apply satx
                                 apply satx
                                apply satx
                               apply satx
                              apply satx
                             apply satx
                            apply satx
                           apply satx
                          apply satx
                         apply satx
                        apply satx
                       apply satx
                      apply satx
                     apply satx
                    apply satx
                   apply satx
                  apply satx
                 apply satx
                apply satx
               apply satx
              apply satx
             apply satx
            apply satx
           apply satx
          apply satx
         apply satx
        apply satx
       apply satx
      apply satx
     apply satx
    apply satx
   apply satx
  apply (simp add: upto_code upto_aux_rec, presburger)
done
*)

private lemma size_mask_32word': "size ((mask (32 - m))::32 word) = 32" by(simp add:word_size)


(*declare[[show_types]]
declare[[unify_trace_failure]]*)
lemma wordinterval_to_set_ipv4range_set_from_prefix: assumes "valid_prefix pfx"
      shows "prefix_to_ipset pfx = ipv4range_set_from_prefix (pfxm_prefix pfx) (pfxm_length pfx)"
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

    have ipv4range_set_from_netmask_prefix: 
      "ipv4range_set_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) = ipv4range_set_from_prefix (pfxm_prefix pfx) (pfxm_length pfx)"
     unfolding ipv4range_set_from_netmask_def ipv4range_set_from_prefix_alt
     unfolding pfxm_mask_def[symmetric]
     unfolding mask_def2_symmetric
     apply(simp)
     unfolding Let_def
     using assms[unfolded valid_prefix_def]
     by (metis helper3 pfxm_mask_def size_mask_32word' word_bw_comms(2) word_size)
     (*word_size and size_mask_32word' needed since generalization to 'a::len word, though everything in here is 32*)
    
    show ?thesis by (metis ipv4range_set_from_netmask_prefix local.prefix_match_if_in_corny_set) 
qed


private lemma helper_32_case_split: "32 < m \<or> m \<in> set (map nat [0..32])"
  by (simp add: upto_code upto_aux_rec, presburger)
private lemma ipv4addr_andnot_impl_takem: "(a::32 word) AND NOT mask (32 - m) = b \<Longrightarrow> (take (m) (to_bl a)) = (take (m) (to_bl b))"
  apply word_bitwise
  apply (subgoal_tac "m > 32 \<or> m \<in> set (map nat (upto 0 32))")
   prefer 2
   apply(simp only: helper_32_case_split)
  apply (simp add: upto_code upto_aux_rec, elim disjE)
                                   apply (simp add: size_mask_32word size_mask_32word')
  apply (simp_all add: size_mask_32word size_mask_32word')
done


definition ip4_set :: "32 word \<Rightarrow> nat \<Rightarrow> 32 word set" where "ip4_set i r = {j . i AND NOT mask (32 - r) = j AND NOT mask (32 - r)}"

private lemma "(m1 \<or> m2) \<and> (m3 \<or> m4) \<longleftrightarrow> (m1 \<and> m3) \<or> (m1 \<and> m4) \<or> (m2 \<and> m3) \<or> (m2 \<and> m4)"
  by blast

private lemma caesar_proof_without_structures: "mask (32 - l) AND pfxm_p = 0 \<Longrightarrow>
           (a \<in> ipv4range_set_from_netmask (pfxm_p) (NOT mask (32 - l))) \<longleftrightarrow> (pfxm_p = NOT mask (32 - l) AND a)"
proof -
  assume a: "mask (32 - l) AND pfxm_p = 0"
  with prefix_match_if_in_corny_set[unfolded valid_prefix_def prefix_match_semantics_def Let_def, symmetric, where pfx="PrefixMatch pfxm_p l"]
  show "(a \<in> ipv4range_set_from_netmask (pfxm_p) (NOT mask (32 - l))) \<longleftrightarrow> (pfxm_p = NOT mask (32 - l) AND a)"
    unfolding pfxm_mask_def by(simp)
qed
  

private lemma mask_and_not_mask_helper: "mask (len - m) AND base AND NOT mask (len - m) = 0"
  by(simp add: word_bw_lcs)

lemma ipv4range_set_from_netmask_base_mask_consume: 
  "ipv4range_set_from_netmask (base AND NOT mask (32 - m)) (NOT mask (32 - m)) =
  ipv4range_set_from_netmask base (NOT mask (32 - m))"
  unfolding ipv4range_set_from_netmask_def
  by(simp add: AND_twice)

lemma ipv4range_set_from_prefix_eq_ip4_set: "ipv4range_set_from_prefix base m = ip4_set base m"
  unfolding ip4_set_def
  unfolding set_eq_iff
  unfolding mem_Collect_eq
  unfolding ipv4range_set_from_prefix_alt1
  unfolding maskshift_eq_not_mask
  using caesar_proof_without_structures[OF mask_and_not_mask_helper, of _ base m]
  unfolding ipv4range_set_from_netmask_base_mask_consume
  unfolding word_bw_comms(1)[of _ " ~~ mask (32 - m)"]
  ..


(*the bitmagic (pfxm_prefix pfx) AND pfxm_mask pfx). we just want to make sure to get a valid_prefix*)
lemma cornys_hacky_call_to_prefix_to_range_to_start_with_a_valid_prefix: fixes base::"'a::len word"
  shows "valid_prefix (PrefixMatch (base AND NOT mask ((len_of TYPE ('a)) - len)) len)"
  apply(simp add: valid_prefix_def pfxm_mask_def pfxm_length_def pfxm_prefix_def)
  by (metis mask_and_not_mask_helper)
end

function word_upto :: "'a word \<Rightarrow> 'a word \<Rightarrow> ('a::len0) word list" where
"word_upto a b = (if a = b then [a] else word_upto a (b - 1) @ [b])"
by auto

termination word_upto
apply(relation "measure (unat \<circ> split (op -) \<circ> prod.swap)")
apply(rule wf_measure)
apply(unfold in_measure)
apply(unfold comp_def)
apply(simp)
apply(subgoal_tac "unat (b - a - 1) < unat (b - a)")
apply(simp add: diff_right_commute)
apply(rule measure_unat)
apply auto
done

declare word_upto.simps[simp del]

(* Most of the lemmas I show about word_upto hold without a \<le> b, but I don't need that right now and it's giving me a headache *)

lemma word_upto_set_eq2: "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<Longrightarrow> a \<le> x \<and> x \<le> b"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst(asm) word_upto.simps)
apply(simp)
apply(subst(asm) word_upto.simps)
apply(simp)
apply(erule disjE)
apply simp
proof -
	case goal1
	from goal1(2-3) have "b \<noteq> 0" by force
	from goal1(2,3) have "a \<le> b - 1" by (metis `b \<noteq> 0` le_step_down_nat order_class.order.antisym unat_minus_one word_le_nat_alt) 
	from goal1(1)[OF this goal1(4)] show ?case by (metis dual_order.trans goal1(2) goal1(3) less_imp_le measure_unat word_le_0_iff word_le_nat_alt)
qed

lemma word_upto_set_eq3: "a \<le> x \<and> x \<le> b \<Longrightarrow> x \<in> set (word_upto a b)"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst word_upto.simps)
apply(simp; force)
apply(subst word_upto.simps)
apply(simp)
apply(case_tac "x = b")
apply(simp;fail)
proof -
	case goal1
	from goal1(2-4) have "b \<noteq> 0" by force
	from goal1(2,4) have "x \<le> b - 1" by (metis `b \<noteq> 0` dual_order.antisym le_step_down_nat unat_minus_one word_le_nat_alt) 
	from goal1(1) this show ?case by simp
qed

lemma word_upto_set_eq: "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<longleftrightarrow> a \<le> x \<and> x \<le> b"
	using word_upto_set_eq3 word_upto_set_eq2 by metis
	
lemma word_upto_distinct_hlp: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<notin> set (word_upto a (b - 1))"
	apply(rule ccontr, unfold not_not)
	apply(subgoal_tac "a \<le> b - 1")
	 apply(drule word_upto_set_eq2[of a "b -1" b])
	  apply(simp add: word_upto.simps; fail)
	 apply(subgoal_tac "b \<noteq> 0")
	  apply(meson leD measure_unat word_le_nat_alt)
	 apply(blast intro: iffD1[OF word_le_0_iff])
	apply(metis antisym_conv le_step_down_nat unat_minus_one word_le_0_iff word_le_nat_alt)
done

lemma distinct_word_upto: "a \<le> b \<Longrightarrow> distinct (word_upto a b)"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
apply(subst word_upto.simps)
apply(simp; force)
apply(subst word_upto.simps)
apply(case_tac "a \<le> b - 1")
apply(simp)
apply(rule word_upto_distinct_hlp;simp_all;fail)
apply(simp)
apply(rule ccontr)
apply(metis le_step_down_nat less_le not_le unat_minus_one word_le_nat_alt word_not_simps(1))
done

abbreviation "word_of_nat \<equiv> of_nat :: nat \<Rightarrow> ('l :: len) word"
lemma word_upto_eq_upto: "s \<le> e \<Longrightarrow> e \<le> unat (max_word :: 'l word) \<Longrightarrow>
	word_upto ((word_of_nat :: nat \<Rightarrow> ('l :: len) word) s) (word_of_nat e) = map word_of_nat (upt s (Suc e))"
proof(induction e)
	let ?mwon = "word_of_nat :: nat \<Rightarrow> 'l word"
	let ?mmw = "max_word :: 'l word"
	case (Suc e)
	show ?case
	proof(cases "?mwon s = ?mwon (Suc e)")
		case True
		have "s = Suc e" using le_unat_uoi Suc.prems True by metis
		with True show ?thesis by(subst word_upto.simps) (simp)
	next
		case False 
		hence le: "s \<le> e" using le_SucE Suc.prems by blast
		have lm: "e \<le> unat ?mmw" using Suc.prems by simp
		have sucm: "word_of_nat (Suc e) - 1 = word_of_nat e" using Suc.prems(2) by simp
		note mIH = Suc.IH[OF le lm]
		show ?thesis by(subst word_upto.simps) (simp add: False[simplified] Suc.prems mIH sucm)
	qed
qed(simp add: word_upto.simps)

lemma word_upto_alt: "(a :: ('l :: len) word) \<le> b \<Longrightarrow> word_upto a b = map word_of_nat (upt (unat a) (Suc (unat b)))"
proof -
	let ?mmw = "max_word :: 'l word"
	assume le: "a \<le> b"
	hence nle: "unat a \<le> unat b" by(unat_arith)
	have lem: "unat b \<le> unat ?mmw" by (simp add: word_unat_less_le) 
	note word_upto_eq_upto[OF nle lem, unfolded word_unat.Rep_inverse]
	thus "word_upto a b = map word_of_nat [unat a..<Suc (unat b)]" .
qed

definition "stop_word_upto_unfold = word_upto"
lemma [code_unfold]: "word_upto a b = (if a \<le> b then map word_of_nat (upt (unat a) (Suc (unat b))) else stop_word_upto_unfold a b)"
	using word_upto_alt stop_word_upto_unfold_def by metis
value[code] "word_upto (3 :: 16 word) 5"
(* TODO: Does this break something? *)

lemma sorted_word_upto:
	fixes a b :: "('l :: len) word"
	assumes "a \<le> b"
	shows "sorted (word_upto a b)"
using assms
proof(induction b)
	fix b
	assume le_prem: "a \<le> 1 + b"
	assume nmax_prem: "1 + b \<noteq> 0"
    assume IH: "a \<le> b \<Longrightarrow> sorted (word_upto a b)"
	show "sorted (word_upto a (1 + b))" proof(cases "a = 1 + b")
		case True thus ?thesis by(simp add: word_upto.simps)
	next
		case False
		have fprem: "a \<le> b" using le_prem False by (metis add.commute antisym_conv1 plus_one_helper)
		note mIH = IH[OF this]
		show ?thesis by(subst word_upto.simps)
			(simp add: fprem lt1_neq0 nmax_prem word_le_plus_either word_upto_set_eq False sorted_append mIH)
	qed
qed(simp add: word_upto.simps)
	
 
lemma "valid_prefix a \<Longrightarrow> valid_prefix b \<Longrightarrow> card (prefix_to_ipset a) < card (prefix_to_ipset b) \<Longrightarrow> a \<le> b"
oops (* Das geht bestümmt irgendwie™ 
proof -
	case goal1
	hence "pfxm_length a > pfxm_length b" sledgehammer  sorry
	thus ?thesis by (simp add: less_eq_prefix_match_def prefix_match_less_eq1_def)
qed
*)

end
