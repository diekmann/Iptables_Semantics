theory PrefixMatch
imports "IPAddr"
begin

(*Contributed by Julius Michaelis*)

section\<open>Prefix match\<close>
text\<open>
  The main difference between the prefix matched defined here and CIDR notation is a validity constraint 
  imposed on prefix matches.

  For example, 192.168.42.42/16 is valid CIDR notation whereas for a prefix match, it must be 192.168.0.0/16.

  I.e. the last bits of the prefix must be set to zero.
\<close>

text\<open>We define a type for ips in CIDR notation, e.g. 192.168.0.0/24.\<close>
context
  notes [[typedef_overloaded]]
begin
  datatype 'a prefix_match = PrefixMatch (pfxm_prefix: "'a::len word") (pfxm_length: nat)
end

definition pfxm_mask :: "'a prefix_match \<Rightarrow> 'a::len word" where
  "pfxm_mask x \<equiv> mask (len_of (TYPE('a)) - pfxm_length x)"

definition valid_prefix :: "('a::len) prefix_match \<Rightarrow> bool" where
  "valid_prefix pf = ((pfxm_mask pf) AND pfxm_prefix pf = 0)"

text\<open>The type @{typ "'a prefix_match"} usually requires @{const valid_prefix}.
      When we allow working on arbitrary IPs in CIDR notation, we will use the type @{typ "('i::len word \<times> nat)"} directly.\<close>

lemma valid_prefix_00(*[simp,intro!]*): "valid_prefix (PrefixMatch 0 0)" by (simp add: valid_prefix_def)

definition prefix_match_to_CIDR :: "('i::len) prefix_match \<Rightarrow> ('i word \<times> nat)" where
  "prefix_match_to_CIDR pfx \<equiv> (pfxm_prefix pfx, pfxm_length pfx)"

lemma prefix_match_to_CIDR_def2: "prefix_match_to_CIDR = (\<lambda>pfx. (pfxm_prefix pfx, pfxm_length pfx))"
  unfolding prefix_match_to_CIDR_def fun_eq_iff by simp





definition "prefix_match_dtor m \<equiv> (case m of PrefixMatch p l \<Rightarrow> (p,l))"

definition "prefix_match_less_eq1 a b = (if pfxm_length a = pfxm_length b then pfxm_prefix a \<le> pfxm_prefix b else pfxm_length a > pfxm_length b)"
instantiation prefix_match :: (len) linorder
begin
	definition "a \<le> b \<longleftrightarrow> prefix_match_less_eq1 a b"
	definition "a < b \<longleftrightarrow> (a \<noteq> b \<and> prefix_match_less_eq1 a b)"
instance
apply standard
by(auto simp: less_eq_prefix_match_def less_prefix_match_def prefix_match.expand prefix_match_less_eq1_def split: if_splits)
end

lemma "sorted_list_of_set {PrefixMatch 0 32 :: 32 prefix_match, PrefixMatch 42 32, PrefixMatch 0 0, PrefixMatch 0 1, PrefixMatch 12 31} =
       [PrefixMatch 0 32, PrefixMatch 0x2A 32, PrefixMatch 0xC 31, PrefixMatch 0 1, PrefixMatch 0 0]" by eval


context
begin

private lemma valid_prefix_E: "valid_prefix pf \<Longrightarrow> ((pfxm_mask pf) AND pfxm_prefix pf = 0)" 
  unfolding valid_prefix_def .
private lemma valid_prefix_alt: fixes p::"'a::len prefix_match"
  shows "valid_prefix p = (pfxm_prefix p AND (2 ^ ((len_of TYPE ('a)) - pfxm_length p) - 1) = 0)"
  unfolding valid_prefix_def
  unfolding mask_def
  using word_bw_comms(1)
   arg_cong[where f = "\<lambda>x. (pfxm_prefix p AND x - 1 = 0)"]
   shiftl_1
  unfolding pfxm_prefix_def pfxm_mask_def mask_def
  by metis

subsection\<open>Address Semantics\<close>

definition prefix_match_semantics where
  "prefix_match_semantics m a = (pfxm_prefix m = (NOT pfxm_mask m) AND a)"


subsection\<open>Set Semantics\<close>

definition prefix_to_wordset :: "'a::len prefix_match \<Rightarrow> 'a word set" where
  "prefix_to_wordset pfx = {pfxm_prefix pfx .. pfxm_prefix pfx OR pfxm_mask pfx}"

private lemma pfx_not_empty: "valid_prefix pfx \<Longrightarrow> prefix_to_wordset pfx \<noteq> {}"
  unfolding valid_prefix_def prefix_to_wordset_def by(simp add: le_word_or2)

text\<open>Walking through a routing table:
  Splits the (remaining) IP space when traversing a routing table: the pair contains the IPs
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

lemma zero_prefix_match_all: "valid_prefix m \<Longrightarrow> pfxm_length m = 0 \<Longrightarrow> prefix_match_semantics m ip"
  by(simp add: pfxm_mask_def mask_2pm1 valid_prefix_alt prefix_match_semantics_def)

lemma prefix_to_wordset_subset_ipset_from_cidr: 
    "prefix_to_wordset pfx \<subseteq> ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
  apply(rule subsetI)
  apply(simp add: prefix_to_wordset_def addr_in_ipset_from_cidr_code)
  apply(intro impI conjI)
   apply (metis (erased, hide_lams) order_trans word_and_le2)
  apply(simp add: pfxm_mask_def)
  done

subsection\<open>Equivalence Proofs\<close>

lemma pfx_match_addr_ipset: "valid_prefix rr \<Longrightarrow> prefix_match_semantics rr addr \<Longrightarrow> (addr \<in> prefix_to_wordset rr)"
  by(simp add: prefix_match_semantics_def prefix_to_wordset_def valid_prefix_def)
     (metis (no_types, lifting) neg_mask_add_mask pfxm_mask_def word_and_le1 word_ao_absorbs(1) word_ao_absorbs(6) word_bool_alg.conj.commute word_neg_and_le)
(* inversion should hold\<dots> *)

private lemma packet_ipset_prefix_eq1:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "\<not>prefix_match_semantics match addr" 
  shows "addr \<in> (snd (ipset_prefix_match match addrrg))"
using assms
proof -
  have "pfxm_prefix match \<le> addr \<Longrightarrow> \<not> addr \<le> pfxm_prefix match OR pfxm_mask match"
  proof(goal_cases)
    case 1
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
      using a2 by (metis 1 word_bool_alg.conj_cancel_right word_bool_alg.conj_commute word_log_esimps(3))
  qed
  from this show ?thesis using assms(1)
    unfolding ipset_prefix_match_def Let_def snd_conv prefix_to_wordset_def
    by simp
qed


private lemma packet_ipset_prefix_eq3:
  assumes "addr \<in> (snd (ipset_prefix_match match addrrg))"
  shows "\<not>prefix_match_semantics match addr"
proof -
  have helper3: "(x::'a::len word) OR y = x OR y AND NOT x" for x y by (simp add: word_oa_dist2)
  from assms have "addr \<notin> prefix_to_wordset match"
    apply(subst(asm) ipset_prefix_match_def)
    by(simp add: Let_def fst_def)
  thus ?thesis
    apply(subst(asm) prefix_to_wordset_def)
    apply(simp only: prefix_match_semantics_def valid_prefix_def
                     Set_Interval.ord_class.atLeastAtMost_iff prefix_to_wordset_def)
    apply(simp)
    apply(metis helper3 le_word_or2 word_and_le2 word_bw_comms(1) word_bw_comms(2))
    done
qed

private lemma packet_ipset_prefix_eq24:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "prefix_match_semantics match addr = (addr \<in> (fst (ipset_prefix_match match addrrg)))"
apply(cases match)
using assms
apply(simp add: prefix_match_semantics_def prefix_to_wordset_def pfxm_mask_def valid_prefix_def)
using zero_base_lsb_imp_set_eq_as_bit_operation by auto



private lemma packet_ipset_prefix_eq13:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "\<not>prefix_match_semantics match addr = (addr \<in> (snd (ipset_prefix_match match addrrg)))"
using packet_ipset_prefix_eq1[OF assms] packet_ipset_prefix_eq3 by fast

lemma prefix_match_if_in_prefix_to_wordset: assumes "valid_prefix pfx" 
  shows "prefix_match_semantics pfx a \<longleftrightarrow> a \<in> prefix_to_wordset pfx"
  using packet_ipset_prefix_eq24[OF _ assms]
by (metis (erased, hide_lams) Int_iff UNIV_I fst_conv ipset_prefix_match_def)

private lemma valid_prefix_ipset_from_netmask_ipset_from_cidr:
  shows "ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) = ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
  using assms apply(cases pfx)
  apply(simp add: ipset_from_cidr_alt2 pfxm_mask_def)
 done
  

lemma prefix_match_if_in_corny_set: 
  assumes "valid_prefix pfx"
  shows "prefix_match_semantics pfx a \<longleftrightarrow> a \<in> ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
  unfolding prefix_match_if_in_prefix_to_wordset[OF assms]
  unfolding valid_prefix_ipset_from_netmask_ipset_from_cidr
  unfolding prefix_to_wordset_def
  apply(subst ipset_from_cidr_base_wellforemd)
   subgoal using assms by(simp add: valid_prefix_def pfxm_mask_def)
  by(simp add: pfxm_mask_def)
  

lemma prefix_match_if_in_corny_set2:
  assumes "valid_prefix pfx"
  shows "prefix_match_semantics pfx (a :: 'i::len word) \<longleftrightarrow> a \<in> ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
 unfolding prefix_match_if_in_corny_set[OF assms] pfxm_mask_def ipset_from_cidr_def
 by (metis (full_types) NOT_mask_shifted_lenword word_not_not)

(*TODO: can this be deleted?*)
private lemma maskshift_eq_not_mask_generic: "((mask m << len_of TYPE('a) - m) :: 'a::len word) = NOT mask (len_of TYPE('a) - m)"
  using NOT_mask_shifted_lenword by (metis word_not_not) 


(*declare[[show_types]]
declare[[unify_trace_failure]]*)
(*TODO: due to generalization, this can be simplified*)
lemma prefix_to_wordset_ipset_from_cidr: assumes "valid_prefix (pfx::'a::len prefix_match)"
      shows "prefix_to_wordset pfx = ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
proof -
  have helper3: "(x::'a::len word) OR y = x OR y AND NOT x" for x y by (simp add: word_oa_dist2)
  have prefix_match_if_in_corny_set: "(prefix_to_wordset pfx) = ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
    unfolding prefix_to_wordset_def ipset_from_netmask_def Let_def
    unfolding word_bool_alg.double_compl
    proof(goal_cases)
      case 1
      have *: "pfxm_prefix pfx AND NOT pfxm_mask pfx = pfxm_prefix pfx"
        unfolding mask_eq_0_eq_x[symmetric] using valid_prefix_E[OF assms] word_bw_comms(1)[of "pfxm_prefix pfx"] by simp
      hence **: "pfxm_prefix pfx AND NOT pfxm_mask pfx OR pfxm_mask pfx = pfxm_prefix pfx OR pfxm_mask pfx"
        by simp
      show ?case unfolding * ** ..
    qed
    
    have "\<And>len. ((mask len)::'a::len word) << len_of TYPE('a) - len = ~~ mask (len_of TYPE('a) - len)"
    using NOT_mask_shifted_lenword by (metis word_not_not)
    from this[of "(pfxm_length pfx)"] have mask_def2_symmetric:
      "((mask (pfxm_length pfx)::'a::len word) << len_of TYPE('a) - pfxm_length pfx) = NOT pfxm_mask pfx"
      unfolding pfxm_mask_def by simp

    have ipset_from_netmask_prefix: 
      "ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) = ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
     unfolding ipset_from_netmask_def ipset_from_cidr_alt
     unfolding pfxm_mask_def[symmetric]
     unfolding mask_def2_symmetric
     apply(simp)
     unfolding Let_def
     using assms[unfolded valid_prefix_def]
     by (metis helper3 word_bw_comms(2))
    
    show ?thesis by (metis ipset_from_netmask_prefix local.prefix_match_if_in_corny_set) 
qed

private lemma "(m1 \<or> m2) \<and> (m3 \<or> m4) \<longleftrightarrow> (m1 \<and> m3) \<or> (m1 \<and> m4) \<or> (m2 \<and> m3) \<or> (m2 \<and> m4)"
  by blast

private lemma caesar_proof_without_structures: "mask (len_of TYPE('a) - l) AND (pfxm_p::'a::len word) = 0 \<Longrightarrow>
           (a \<in> ipset_from_netmask (pfxm_p) (NOT mask (len_of TYPE('a) - l))) \<longleftrightarrow> (pfxm_p = NOT mask (len_of TYPE('a) - l) AND a)"
proof -
  assume a: "mask (len_of TYPE('a) - l) AND pfxm_p = 0"
  with prefix_match_if_in_corny_set[unfolded valid_prefix_def prefix_match_semantics_def Let_def, symmetric,
      where pfx="PrefixMatch pfxm_p l"]
  show "(a \<in> ipset_from_netmask (pfxm_p) (NOT mask (len_of TYPE('a) - l))) \<longleftrightarrow> (pfxm_p = NOT mask (len_of TYPE('a) - l) AND a)"
    unfolding pfxm_mask_def by(simp)
qed

(*TODO: delete*)
private lemma mask_and_not_mask_helper: "mask (len - m) AND base AND NOT mask (len - m) = 0"
  by(simp add: word_bw_lcs)


(*the bitmagic (pfxm_prefix pfx) AND pfxm_mask pfx). we just want to make sure to get a valid_prefix*)
lemma cornys_hacky_call_to_prefix_to_wordinterval_to_start_with_a_valid_prefix: fixes base::"'a::len word"
  shows "valid_prefix (PrefixMatch (base AND NOT mask ((len_of TYPE ('a)) - len)) len)"
  apply(simp add: valid_prefix_def pfxm_mask_def pfxm_length_def pfxm_prefix_def)
  by (metis mask_and_not_mask_helper)

definition prefix_to_wordinterval :: "'a::len prefix_match \<Rightarrow> 'a wordinterval" where
  "prefix_to_wordinterval pfx = WordInterval (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"

lemma prefix_to_wordinterval_set_eq: "wordinterval_to_set (prefix_to_wordinterval pfx) = prefix_to_wordset pfx"
  unfolding prefix_to_wordinterval_def prefix_to_wordset_def by simp

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

end




text\<open>Getting a lowest element\<close>
  lemma ipset_from_cidr_lowest: "a \<in> ipset_from_cidr a n" 
    using ip_cidr_set_def ipset_from_cidr_eq_ip_cidr_set by blast

  (*this is why I call the previous lemma 'lowest'*)
  lemma "valid_prefix (PrefixMatch a n) \<Longrightarrow> is_lowest_element a (ipset_from_cidr a n)"
    apply(simp add: is_lowest_element_def ipset_from_cidr_lowest)
    apply(simp add: ipset_from_cidr_eq_ip_cidr_set ip_cidr_set_def)
    apply(simp add: valid_prefix_def pfxm_mask_def)
    apply clarify
    by (metis add.left_neutral antisym_conv word_and_le2 word_bw_comms(1) word_plus_and_or_coroll2)


 
lemma "valid_prefix a \<Longrightarrow> valid_prefix b \<Longrightarrow> card (prefix_to_wordset a) < card (prefix_to_wordset b) \<Longrightarrow> a \<le> b"
oops (* Das geht bestümmt irgendwie™ 
proof -
	case goal1
	hence "pfxm_length a > pfxm_length b" sledgehammer  sorry
	thus ?thesis by (simp add: less_eq_prefix_match_def prefix_match_less_eq1_def)
qed
*)

text\<open>The only stuff here that is not about @{type prefix_match}\<close>
lemma suc2plus_inj_on: "inj_on (of_nat :: nat \<Rightarrow> ('l :: len) word) {0..unat (max_word :: 'l word)}"
proof(rule inj_onI)
	let ?mmw = "(max_word :: 'l word)"
	let ?mstp = "(of_nat :: nat \<Rightarrow> 'l word)"
	fix x y :: nat
	assume "x \<in> {0..unat ?mmw}" "y \<in> {0..unat ?mmw}"
	hence se: "x \<le> unat ?mmw" "y \<le> unat ?mmw" by simp_all
	assume eq: "?mstp x = ?mstp y"
	note f = le_unat_uoi[OF se(1)] le_unat_uoi[OF se(2)]
	(*show "x = y"
	apply(subst f(1)[symmetric])
	apply(subst f(2)[symmetric])
	apply(subst word_unat.Rep_inject)
	using eq .*)
	show "x = y" using eq le_unat_uoi se by metis
qed

lemma distinct_of_nat_list: (* TODO: Move to CaesarWordLemmaBucket *)
	"distinct l \<Longrightarrow> \<forall>e \<in> set l. e \<le> unat (max_word :: ('l::len) word) \<Longrightarrow> distinct (map (of_nat :: nat \<Rightarrow> 'l word) l)"
proof(induction l)
	let ?mmw = "(max_word :: 'l word)"
	let ?mstp = "(of_nat :: nat \<Rightarrow> 'l word)"
	case (Cons a as)
	have "distinct as" "\<forall>e\<in>set as. e \<le> unat ?mmw" using Cons.prems by simp_all 
	note mIH = Cons.IH[OF this]
	moreover have "?mstp a \<notin> ?mstp ` set as"
	proof 
		have representable_set: "set as \<subseteq> {0..unat ?mmw}" using \<open>\<forall>e\<in>set (a # as). e \<le> unat max_word\<close> by fastforce
		have a_reprbl: "a \<in> {0..unat ?mmw}" using \<open>\<forall>e\<in>set (a # as). e \<le> unat max_word\<close> by simp
		assume "?mstp a \<in> ?mstp ` set as"
		with inj_on_image_mem_iff[OF suc2plus_inj_on a_reprbl representable_set]
		have "a \<in> set as" by simp
		with \<open>distinct (a # as)\<close> show False by simp
	qed
	ultimately show ?case by simp
qed simp

end
