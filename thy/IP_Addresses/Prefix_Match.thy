(*  Title:      Prefix_Match.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory Prefix_Match
imports IP_Address
begin


section\<open>Prefix Match\<close>
text\<open>
  The main difference between the prefix match defined here and CIDR notation is a validity
  constraint imposed on prefix matches.

  For example, 192.168.42.42/16 is valid CIDR notation whereas for a prefix match,
  it must be 192.168.0.0/16.

  I.e. the last bits of the prefix must be set to zero.
\<close>

context
  notes [[typedef_overloaded]]
begin
  datatype 'a prefix_match = PrefixMatch (pfxm_prefix: "'a::len word") (pfxm_length: nat)
end

definition pfxm_mask :: "'a prefix_match \<Rightarrow> 'a::len word" where
  "pfxm_mask x \<equiv> mask (len_of (TYPE('a)) - pfxm_length x)"

definition valid_prefix :: "('a::len) prefix_match \<Rightarrow> bool" where
  "valid_prefix pf = ((pfxm_mask pf) AND pfxm_prefix pf = 0)"

text\<open>When zeroing all least significant bits which exceed the @{const pfxm_length},
     you get a @{const valid_prefix}\<close>
lemma mk_valid_prefix:
  fixes base::"'a::len word"
  shows "valid_prefix (PrefixMatch (base AND NOT mask (len_of TYPE ('a) - len)) len)"
proof -
  have "mask (len - m) AND base AND NOT mask (len - m) = 0"
    for m len and base::"'a::len word" by(simp add: word_bw_lcs)
  thus ?thesis
  by(simp add: valid_prefix_def pfxm_mask_def pfxm_length_def pfxm_prefix_def)
qed


text\<open>The type @{typ "'a prefix_match"} usually requires @{const valid_prefix}.
      When we allow working on arbitrary IPs in CIDR notation,
      we will use the type @{typ "('i::len word \<times> nat)"} directly.\<close>

lemma valid_prefix_00: "valid_prefix (PrefixMatch 0 0)" by (simp add: valid_prefix_def)

definition prefix_match_to_CIDR :: "('i::len) prefix_match \<Rightarrow> ('i word \<times> nat)" where
  "prefix_match_to_CIDR pfx \<equiv> (pfxm_prefix pfx, pfxm_length pfx)"

lemma prefix_match_to_CIDR_def2: "prefix_match_to_CIDR = (\<lambda>pfx. (pfxm_prefix pfx, pfxm_length pfx))"
  unfolding prefix_match_to_CIDR_def fun_eq_iff by simp


definition "prefix_match_dtor m \<equiv> (case m of PrefixMatch p l \<Rightarrow> (p,l))"

text\<open>Some more or less random linear order on prefixes.
     Only used for serialization at the time of this writing.\<close>
instantiation prefix_match :: (len) linorder
begin
	definition "a \<le> b \<longleftrightarrow> (if pfxm_length a = pfxm_length b
                         then pfxm_prefix a \<le> pfxm_prefix b
                         else pfxm_length a > pfxm_length b)"
	definition "a < b \<longleftrightarrow> (a \<noteq> b \<and>
	                       (if pfxm_length a = pfxm_length b
	                        then pfxm_prefix a \<le> pfxm_prefix b
	                        else pfxm_length a > pfxm_length b))"
instance
by standard (auto simp: less_eq_prefix_match_def less_prefix_match_def prefix_match.expand
                  split: if_splits)
end

lemma "sorted_list_of_set
 {PrefixMatch 0 32 :: 32 prefix_match,
  PrefixMatch 42 32,
  PrefixMatch 0 0,
  PrefixMatch 0 1,
  PrefixMatch 12 31} =
    [PrefixMatch 0 32, PrefixMatch 0x2A 32, PrefixMatch 0xC 31, PrefixMatch 0 1, PrefixMatch 0 0]"
  by eval

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
  text\<open>Matching on a @{typ "'a::len prefix_match"}. Think of routing tables.\<close>
  definition prefix_match_semantics where
    "prefix_match_semantics m a \<equiv> pfxm_prefix m = (NOT pfxm_mask m) AND a"


subsection\<open>Relation between prefix and set\<close>

  definition prefix_to_wordset :: "'a::len prefix_match \<Rightarrow> 'a word set" where
    "prefix_to_wordset pfx = {pfxm_prefix pfx .. pfxm_prefix pfx OR pfxm_mask pfx}"
  
  private lemma pfx_not_empty: "valid_prefix pfx \<Longrightarrow> prefix_to_wordset pfx \<noteq> {}"
    unfolding valid_prefix_def prefix_to_wordset_def by(simp add: le_word_or2)
  
  lemma zero_prefix_match_all:
    "valid_prefix m \<Longrightarrow> pfxm_length m = 0 \<Longrightarrow> prefix_match_semantics m ip"
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
  theorem prefix_match_semantics_wordset:
    assumes "valid_prefix pfx" 
    shows "prefix_match_semantics pfx a \<longleftrightarrow> a \<in> prefix_to_wordset pfx"
    using assms
    unfolding valid_prefix_def pfxm_mask_def prefix_match_semantics_def prefix_to_wordset_def
    apply(cases pfx, rename_tac base len)
    apply(simp)
    apply(drule_tac base=base and len=len and a=a in zero_base_lsb_imp_set_eq_as_bit_operation)
    by (simp)
  
  private lemma valid_prefix_ipset_from_netmask_ipset_from_cidr:
    shows "ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) =
            ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
    using assms apply(cases pfx)
    apply(simp add: ipset_from_cidr_alt2 pfxm_mask_def)
   done
  
  lemma prefix_match_semantics_ipset_from_netmask:
    assumes "valid_prefix pfx"
    shows "prefix_match_semantics pfx a \<longleftrightarrow>
            a \<in> ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
    unfolding prefix_match_semantics_wordset[OF assms]
    unfolding valid_prefix_ipset_from_netmask_ipset_from_cidr
    unfolding prefix_to_wordset_def
    apply(subst ipset_from_cidr_base_wellforemd)
     subgoal using assms by(simp add: valid_prefix_def pfxm_mask_def)
    by(simp add: pfxm_mask_def)
    
  lemma prefix_match_semantics_ipset_from_netmask2:
    assumes "valid_prefix pfx"
    shows "prefix_match_semantics pfx (a :: 'i::len word) \<longleftrightarrow>
            a \<in> ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
   unfolding prefix_match_semantics_ipset_from_netmask[OF assms] pfxm_mask_def ipset_from_cidr_def
   by (metis (full_types) NOT_mask_shifted_lenword word_not_not)

  lemma prefix_to_wordset_ipset_from_cidr:
    assumes "valid_prefix (pfx::'a::len prefix_match)"
    shows "prefix_to_wordset pfx = ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
  proof -
    have helper3: "(x::'a::len word) OR y = x OR y AND NOT x" for x y by (simp add: word_oa_dist2)
    have prefix_match_semantics_ipset_from_netmask:
           "(prefix_to_wordset pfx) = ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
      unfolding prefix_to_wordset_def ipset_from_netmask_def Let_def
      unfolding word_bool_alg.double_compl
      proof(goal_cases)
        case 1
        have *: "pfxm_prefix pfx AND NOT pfxm_mask pfx = pfxm_prefix pfx"
          unfolding mask_eq_0_eq_x[symmetric]
          using valid_prefix_E[OF assms] word_bw_comms(1)[of "pfxm_prefix pfx"] by simp
        hence **: "pfxm_prefix pfx AND NOT pfxm_mask pfx OR pfxm_mask pfx =
                    pfxm_prefix pfx OR pfxm_mask pfx"
          by simp
        show ?case unfolding * ** ..
      qed
      have "((mask len)::'a::len word) << len_of TYPE('a) - len = ~~ mask (len_of TYPE('a) - len)"
      for len using NOT_mask_shifted_lenword by (metis word_not_not)
      from this[of "(pfxm_length pfx)"] have mask_def2_symmetric:
        "((mask (pfxm_length pfx)::'a::len word) << len_of TYPE('a) - pfxm_length pfx) =
          NOT pfxm_mask pfx"
        unfolding pfxm_mask_def by simp
  
      have ipset_from_netmask_prefix: 
        "ipset_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx) =
          ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
       unfolding ipset_from_netmask_def ipset_from_cidr_alt
       unfolding pfxm_mask_def[symmetric]
       unfolding mask_def2_symmetric
       apply(simp)
       unfolding Let_def
       using assms[unfolded valid_prefix_def]
       by (metis helper3 word_bw_comms(2))
      
      show ?thesis by (metis ipset_from_netmask_prefix local.prefix_match_semantics_ipset_from_netmask) 
  qed

  definition prefix_to_wordinterval :: "'a::len prefix_match \<Rightarrow> 'a wordinterval" where
    "prefix_to_wordinterval pfx \<equiv> WordInterval (pfxm_prefix pfx) (pfxm_prefix pfx OR pfxm_mask pfx)"
  
  lemma prefix_to_wordinterval_set_eq[simp]:
    "wordinterval_to_set (prefix_to_wordinterval pfx) = prefix_to_wordset pfx"
    unfolding prefix_to_wordinterval_def prefix_to_wordset_def by simp
  
  lemma prefix_to_wordinterval_def2:
    "prefix_to_wordinterval pfx =
      iprange_interval ((pfxm_prefix pfx), (pfxm_prefix pfx OR pfxm_mask pfx))"
    unfolding iprange_interval.simps prefix_to_wordinterval_def by simp
  corollary prefix_to_wordinterval_ipset_from_cidr: "valid_prefix pfx \<Longrightarrow>
    wordinterval_to_set (prefix_to_wordinterval pfx) =
      ipset_from_cidr (pfxm_prefix pfx) (pfxm_length pfx)"
  using prefix_to_wordset_ipset_from_cidr prefix_to_wordinterval_set_eq by auto
end


lemma prefix_never_empty: 
  fixes d:: "'a::len prefix_match"
  shows"\<not> wordinterval_empty (prefix_to_wordinterval d)"
by (simp add: le_word_or2 prefix_to_wordinterval_def)


text\<open>Getting a lowest element\<close>
  lemma ipset_from_cidr_lowest: "a \<in> ipset_from_cidr a n" 
    using ip_cidr_set_def ipset_from_cidr_eq_ip_cidr_set by blast

  (*this is why I call the previous lemma 'lowest'*)
  lemma "valid_prefix (PrefixMatch a n) \<Longrightarrow> is_lowest_element a (ipset_from_cidr a n)"
    apply(simp add: is_lowest_element_def ipset_from_cidr_lowest)
    apply(simp add: ipset_from_cidr_eq_ip_cidr_set ip_cidr_set_def)
    apply(simp add: valid_prefix_def pfxm_mask_def)
    by (metis diff_zero eq_iff mask_out_sub_mask word_and_le2 word_bw_comms(1))

end
