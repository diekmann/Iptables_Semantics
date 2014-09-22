(*  Title:      IPv4Addr.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory IPv4Addr
imports Main
  NumberWang
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

value "(2::nat) < 2^32" (*without Code_Target_Nat, this would be really slow*)


section {*Modelling IPv4 Adresses*}
  text{*An IPv4 address is basically a 32 bit unsigned integer*}
  type_synonym ipv4addr = "32 word"
 
  value "42 :: ipv4addr"

  value "(42 :: ipv4addr) \<le> 45"

  text{*Conversion between natural numbers and IPv4 adresses*}
  definition nat_of_ipv4addr :: "ipv4addr \<Rightarrow> nat" where
    "nat_of_ipv4addr a = unat a"
  definition ipv4addr_of_nat :: "nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_nat n =  of_nat n"

  lemma "((nat_of_ipv4addr (42::ipv4addr))::nat) = 42" by eval
  lemma "((ipv4addr_of_nat (42::nat))::ipv4addr) = 42" by eval

  text{*The maximum IPv4 addres*}
  definition max_ipv4_addr :: "ipv4addr" where 
    "max_ipv4_addr \<equiv> ipv4addr_of_nat ((2^32) - 1)"

  lemma max_ipv4_addr_number: "max_ipv4_addr = 4294967295"
    by eval
  lemma "max_ipv4_addr = 0b11111111111111111111111111111111"
    by(fact max_ipv4_addr_number)
  lemma max_ipv4_addr_max_word: "max_ipv4_addr = max_word"
    by(simp add: max_ipv4_addr_number max_word_def)
  lemma max_ipv4_addr_max[simp]: "\<forall>a. a \<le> max_ipv4_addr"
    by(simp add: max_ipv4_addr_max_word)
  lemma range_0_max_UNIV[simp]: "{0 .. max_ipv4_addr} = UNIV"
    by(simp add: max_ipv4_addr_max_word) fastforce

  text{*identity functions*}
  lemma nat_of_ipv4addr_ipv4addr_of_nat: "\<lbrakk> n \<le> nat_of_ipv4addr max_ipv4_addr \<rbrakk> \<Longrightarrow> nat_of_ipv4addr (ipv4addr_of_nat n) = n"
    by (metis ipv4addr_of_nat_def le_unat_uoi nat_of_ipv4addr_def)
  lemma nat_of_ipv4addr_ipv4addr_of_nat_mod: "nat_of_ipv4addr (ipv4addr_of_nat n) = n mod 2^32"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def unat_of_nat)
  lemma ipv4addr_of_nat_nat_of_ipv4addr: "ipv4addr_of_nat (nat_of_ipv4addr addr) = addr"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def)

  text{*Equality of IPv4 adresses*}
  lemma "\<lbrakk> n \<le> nat_of_ipv4addr max_ipv4_addr \<rbrakk> \<Longrightarrow> nat_of_ipv4addr (ipv4addr_of_nat n) = n"
    apply(simp add: nat_of_ipv4addr_def ipv4addr_of_nat_def)
    apply(induction n)
    apply(simp_all)
    by(unat_arith)

  lemma ipv4addr_of_nat_eq: "x = y \<Longrightarrow> ipv4addr_of_nat x = ipv4addr_of_nat y"
    by(simp add: ipv4addr_of_nat_def)

subsection{*Representing IPv4 Adresses*}
  fun ipv4addr_of_dotteddecimal :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_dotteddecimal (a,b,c,d) = ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a )"

  fun dotteddecimal_of_ipv4addr :: "ipv4addr \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
    "dotteddecimal_of_ipv4addr a = (nat_of_ipv4addr ((a >> 24) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 16) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 8) AND 0xFF), 
                                    nat_of_ipv4addr (a AND 0xff))"

  declare ipv4addr_of_dotteddecimal.simps[simp del]
  declare dotteddecimal_of_ipv4addr.simps[simp del]

  lemma "ipv4addr_of_dotteddecimal (192, 168, 0, 1) = 3232235521" by eval
  lemma "dotteddecimal_of_ipv4addr 3232235521 = (192, 168, 0, 1)" by eval

  text{*a different notation for @{term ipv4addr_of_dotteddecimal}*}
  lemma ipv4addr_of_dotteddecimal_bit: 
    "ipv4addr_of_dotteddecimal (a,b,c,d) = (ipv4addr_of_nat a << 24) + (ipv4addr_of_nat b << 16) + (ipv4addr_of_nat c << 8) + ipv4addr_of_nat d"
  proof -
    have a: "(ipv4addr_of_nat a) << 24 = ipv4addr_of_nat (a * 16777216)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n, metis Abs_fnat_hom_mult comm_semiring_1_class.normalizing_semiring_rules(7) of_nat_numeral)
    have b: "(ipv4addr_of_nat b) << 16 = ipv4addr_of_nat (b * 65536)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n, metis Abs_fnat_hom_mult comm_semiring_1_class.normalizing_semiring_rules(7) of_nat_numeral)
    have c: "(ipv4addr_of_nat c) << 8 = ipv4addr_of_nat (c * 256)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n, metis Abs_fnat_hom_mult comm_semiring_1_class.normalizing_semiring_rules(7) of_nat_numeral)
    have ipv4addr_of_nat_suc: "\<And>x. ipv4addr_of_nat (Suc x) = word_succ (ipv4addr_of_nat (x))"
      by(simp add: ipv4addr_of_nat_def, metis Abs_fnat_hom_Suc of_nat_Suc)
    { fix x y
    have "ipv4addr_of_nat x + ipv4addr_of_nat y = ipv4addr_of_nat (x+y)"
      apply(induction x arbitrary: y)
      apply(simp add: ipv4addr_of_nat_def)
      apply(simp add: ipv4addr_of_nat_suc)
      by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(22) comm_semiring_1_class.normalizing_semiring_rules(24) word_succ_p1)
    } from this a b c
    show ?thesis
    apply(simp add: ipv4addr_of_dotteddecimal.simps)
    apply(thin_tac "?x")+
    apply(rule ipv4addr_of_nat_eq)
    by presburger
  qed


  lemma size_ipv4addr: "size (x::ipv4addr) = 32" by(simp add:word_size)
  lemma ipv4addr_of_nat_shiftr_slice: "ipv4addr_of_nat a >> x = slice x (ipv4addr_of_nat a)"
    by(simp add: ipv4addr_of_nat_def shiftr_slice)
  value "(4294967296::ipv4addr) = 2^32"

    
  lemma nat_of_ipv4addr_slice_ipv4addr_of_nat: 
    "nat_of_ipv4addr (slice x (ipv4addr_of_nat a)) = (nat_of_ipv4addr (ipv4addr_of_nat a)) div 2^x"
    proof -
      have mod4294967296: "int a mod 4294967296 = int (a mod 4294967296)"
        using zmod_int by auto
      have int_pullin: "int (a mod 4294967296) div 2 ^ x = int (a mod 4294967296 div 2 ^ x)"
        using zpower_int zdiv_int by (metis of_nat_numeral ) 
    show ?thesis
      apply(simp add: shiftr_slice[symmetric])
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(simp add: mod4294967296 int_pullin)
      done
     qed
  lemma ipv4addr_and_255: "(x::ipv4addr) AND 255 = x AND mask 8"
    apply(subst pow2_mask[of 8, simplified, symmetric])
    by simp
  lemma ipv4addr_of_nat_AND_mask8: "(ipv4addr_of_nat a) AND mask 8 = (ipv4addr_of_nat (a mod 256))"
    apply(simp add: ipv4addr_of_nat_def and_mask_mod_2p)
    apply(simp add: word_of_nat) (*us this to get rid of of_nat. All thm are with word_of_int*)
    apply(simp add: uint_word_of_int)
    apply(subst mod_mod_cancel)
    apply simp
    apply(simp add: zmod_int)
    done
 
  lemma dotteddecimal_of_ipv4addr_ipv4addr_of_dotteddecimal:
  "\<lbrakk> a < 256; b < 256; c < 256; d < 256 \<rbrakk> \<Longrightarrow> dotteddecimal_of_ipv4addr (ipv4addr_of_dotteddecimal (a,b,c,d)) = (a,b,c,d)"
  proof -
    assume  "a < 256" and "b < 256" and "c < 256" and "d < 256"
    note assms= `a < 256` `b < 256` `c < 256` `d < 256` 
    hence a: "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 24) AND mask 8) = a"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
      apply simp_all
      apply(subst mod_pos_pos_trivial)
      apply simp_all
      apply(subst mod_pos_pos_trivial)
      apply simp_all
      done
    from assms have b: "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 16) AND mask 8) = b"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
      apply simp_all
      apply(subst mod_pos_pos_trivial[where b="4294967296"])
      apply simp_all
      apply(simp add: NumberWang.div65536)
      done
    from assms have c: "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 8) AND mask 8) = c"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
      apply simp_all
      apply(subst mod_pos_pos_trivial[where b="4294967296"])
      apply simp_all
      apply(simp add: NumberWang.div256)
      done
    from `d < 256` have d: "nat_of_ipv4addr (ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) AND mask 8) = d"
      apply(simp add: ipv4addr_of_nat_AND_mask8)
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def)
      apply(subgoal_tac "(d + 256 * c + 65536 * b + 16777216 * a) mod 256 = d")
      prefer 2
      apply(simp add: NumberWang.mod256)
      apply(simp)
      apply(simp add: unat_def)
      apply(simp add: uint_word_of_int)
      apply(simp add: mod_pos_pos_trivial)
      done
    from a b c d show ?thesis
      apply(simp add: ipv4addr_of_dotteddecimal.simps dotteddecimal_of_ipv4addr.simps)
      apply(simp add: ipv4addr_and_255)
      done
    qed
    

  lemma ipv4addr_of_dotteddecimal_eqE: "\<lbrakk> ipv4addr_of_dotteddecimal (a,b,c,d) = ipv4addr_of_dotteddecimal (e,f,g,h); a < 256; b < 256; c < 256; d < 256; e < 256; f < 256; g < 256; h < 256 \<rbrakk> \<Longrightarrow>
     a = e \<and> b = f \<and> c = g \<and> d = h"
     by (metis Pair_inject dotteddecimal_of_ipv4addr_ipv4addr_of_dotteddecimal)
  

  text{*previous and next ip addresses, without wrap around*}
    definition ip_next :: "ipv4addr \<Rightarrow> ipv4addr" where
      "ip_next a \<equiv> if a = max_ipv4_addr then max_ipv4_addr else a + 1"
    definition ip_prev :: "ipv4addr \<Rightarrow> ipv4addr" where
      "ip_prev a \<equiv> if a = 0 then 0 else a - 1"
  
    lemma "ip_next 2 = 3" by eval
    lemma "ip_prev 2 = 1" by eval
    lemma "ip_prev 0 = 0" by eval

subsection{*IP ranges*}
  lemma UNIV_ipv4addrset: "(UNIV \<Colon> ipv4addr set) = {0 .. max_ipv4_addr}"
    by(auto)
  lemma "(42::ipv4addr) \<in> UNIV" by eval


  (*Warning, not executable!*)
  definition ipv4range_set_from_netmask::"ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> ipv4addr set" where
    "ipv4range_set_from_netmask addr netmask \<equiv> let network_prefix = (addr AND netmask) in {network_prefix .. network_prefix OR (NOT netmask)}"


  lemma "ipv4range_set_from_netmask (ipv4addr_of_dotteddecimal (192,168,0,42)) (ipv4addr_of_dotteddecimal (255,255,0,0)) =
          {ipv4addr_of_dotteddecimal (192,168,0,0) .. ipv4addr_of_dotteddecimal (192,168,255,255)}"
   by(simp add: ipv4range_set_from_netmask_def ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)

  lemma "ipv4range_set_from_netmask (ipv4addr_of_dotteddecimal (192,168,0,42)) (ipv4addr_of_dotteddecimal (0,0,0,0)) = UNIV"
    by(simp add: UNIV_ipv4addrset ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def ipv4range_set_from_netmask_def max_ipv4_addr_max_word)
   
  
  text{*192.168.0.0/24*}
  definition ipv4range_set_from_bitmask::"ipv4addr \<Rightarrow> nat \<Rightarrow> ipv4addr set" where
    "ipv4range_set_from_bitmask addr bitmask \<equiv> ipv4range_set_from_netmask addr (of_bl ((replicate bitmask True) @ (replicate (32 - bitmask) False)))"

  lemma "(replicate 3 True) = [True, True, True]" by eval
  lemma "of_bl (replicate 3 True) = (7::ipv4addr)" by eval

  (*alternate definition*)
  lemma ipv4range_set_from_bitmask_alt1: 
    "ipv4range_set_from_bitmask addr bitmask = ipv4range_set_from_netmask addr ((mask bitmask) << (32 - bitmask))"
    apply(simp add: ipv4range_set_from_bitmask_def mask_bl)
    apply(simp add:  Word.shiftl_of_bl)
    done

  lemma "ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal (192,168,0,42)) 16 = 
          {ipv4addr_of_dotteddecimal (192,168,0,0) .. ipv4addr_of_dotteddecimal (192,168,255,255)}"
   by(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)
  lemma ipv4range_set_from_bitmask_UNIV: "ipv4range_set_from_bitmask 0 0 = UNIV"
    apply(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def)
    by (metis max_ipv4_addr_max_word range_0_max_UNIV)
  lemma ip_in_ipv4range_set_from_bitmask_UNIV: "ip \<in> (ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal (0, 0, 0, 0)) 0)"
    by(simp add: ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def ipv4range_set_from_bitmask_UNIV)

  lemma ipv4range_set_from_bitmask_0: "ipv4range_set_from_bitmask foo 0 = UNIV"
    apply(rule)
    apply(simp_all)
    apply(simp add: ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_def Let_def)
    apply(simp add: range_0_max_UNIV[symmetric] del: range_0_max_UNIV)
    apply(simp add: mask_def)
    done

  lemma ipv4range_set_from_bitmask_32: "ipv4range_set_from_bitmask foo 32 = {foo}"
    apply(rule)
    apply(simp_all)
    apply(simp_all add: ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_def Let_def)
    apply(simp_all add: mask_def)
    apply(simp_all only: max_ipv4_addr_number[symmetric] max_ipv4_addr_max_word Word.word_and_max)
    apply(simp_all add: word32_or_NOT4294967296)
    done

  lemma ipv4range_set_from_bitmask_alt: "ipv4range_set_from_bitmask pre len = {(pre AND ((mask len) << (32 - len))) .. pre OR (mask (32 - len))}"
    apply(simp only: ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_def Let_def)
    apply(subst Word.word_oa_dist)
    apply(simp only: word_or_not)
    apply(simp only: Word.word_and_max)
    apply(simp only: NOT_mask_len32)
    done



  text{*making element check executable*}
  lemma addr_in_ipv4range_set_from_netmask_code[code_unfold]: 
    "addr \<in> (ipv4range_set_from_netmask base netmask) \<longleftrightarrow> (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by(simp add: ipv4range_set_from_netmask_def Let_def)
  lemma addr_in_ipv4range_set_from_bitmask_code[code_unfold]: "addr \<in> (ipv4range_set_from_bitmask pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> pre OR (mask (32 - len))"
  unfolding ipv4range_set_from_bitmask_alt by simp

  value "ipv4addr_of_dotteddecimal (192,168,4,8) \<in> (ipv4range_set_from_bitmask (ipv4addr_of_dotteddecimal (192,168,0,42)) 16)"

  
  datatype ipv4range = IPv4Range
                ipv4addr --"start (inclusive)"
                ipv4addr --"end (inclusive)"
                | IPv4Union ipv4range ipv4range

  fun ipv4range_to_set :: "ipv4range \<Rightarrow> ipv4addr set" where
    "ipv4range_to_set (IPv4Range start end) = {start .. end}" |
    "ipv4range_to_set (IPv4Union r1 r2) = (ipv4range_to_set r1) \<union> (ipv4range_to_set r2)"

  fun ipv4range_element where
    "ipv4range_element el (IPv4Range s e) = (s \<le> el \<and> el \<le> e)" |
    "ipv4range_element el (IPv4Union r1 r2) = (ipv4range_element el r1 \<or> ipv4range_element el r2)"
  lemma ipv4range_element_set_eq[simp]: "ipv4range_element el rg = (el \<in> ipv4range_to_set rg)"
    by(induction rg rule: ipv4range_element.induct) simp_all

  fun ipv4range_union where "ipv4range_union r1 r2 = IPv4Union r1 r2"
  lemma ipv4range_union_set_eq[simp]: "ipv4range_to_set (ipv4range_union r1 r2) = ipv4range_to_set r1 \<union> ipv4range_to_set r2" by simp

  fun ipv4range_empty where
    "ipv4range_empty (IPv4Range s e) = (e < s)" |
    "ipv4range_empty (IPv4Union r1 r2) = (ipv4range_empty r1 \<and> ipv4range_empty r2)"
  lemma ipv4range_empty_set_eq[simp]: "ipv4range_empty r \<longleftrightarrow> ipv4range_to_set r = {}"
    by(induction r) auto

  fun ipv4range_optimize_empty where
    "ipv4range_optimize_empty (IPv4Union r1 r2) = (let r1o = ipv4range_optimize_empty r1 in (let r2o = ipv4range_optimize_empty r2 in (
      if ipv4range_empty r1o then r2o else (if ipv4range_empty r2o then r1o else (IPv4Union r1o r2o)))))" |
    "ipv4range_optimize_empty r = r"
  lemma ipv4range_optimize_empty_set_eq[simp]: "ipv4range_to_set (ipv4range_optimize_empty r) = ipv4range_to_set r"
    by(induction r) (simp_all add: Let_def)
  lemma ipv4range_optimize_empty_double[simp]: "ipv4range_optimize_empty (ipv4range_optimize_empty r) = ipv4range_optimize_empty r"
    apply(induction r)
    by(simp_all add: Let_def)
  fun ipv4range_empty_shallow where
    "ipv4range_empty_shallow (IPv4Range s e) = (e < s)" |
    "ipv4range_empty_shallow (IPv4Union _ _) = False"
  lemma helper_optimize_shallow: "ipv4range_empty (ipv4range_optimize_empty r) = ipv4range_empty_shallow (ipv4range_optimize_empty r)"
    by(induction r) fastforce+
  fun ipv4range_optimize_empty2 where
    "ipv4range_optimize_empty2 (IPv4Union r1 r2) = (let r1o = ipv4range_optimize_empty r1 in (let r2o = ipv4range_optimize_empty r2 in (
      if ipv4range_empty_shallow r1o then r2o else (if ipv4range_empty_shallow r2o then r1o else (IPv4Union r1o r2o)))))" |
    "ipv4range_optimize_empty2 r = r"
  lemma ipv4range_optimize_empty_code[code_unfold]: "ipv4range_optimize_empty = ipv4range_optimize_empty2"
    by (subst fun_eq_iff, clarify, rename_tac r, induct_tac r)
       (unfold ipv4range_optimize_empty.simps ipv4range_optimize_empty2.simps Let_def helper_optimize_shallow[symmetric], simp_all)

  fun ipv4range_to_list where
    "ipv4range_to_list (IPv4Union r1 r2) = ipv4range_to_list r1 @ ipv4range_to_list r2" |
    "ipv4range_to_list r = (if ipv4range_empty r then [] else [r])"

  lemma "fold (\<lambda> r s. s \<union> ipv4range_to_set r) (ipv4range_to_list rs) {} = ipv4range_to_set rs"
    apply(induction rs, simp)
    apply(subst ipv4range_to_list.simps(1))
    apply simp
    thm fold_append_concat_rev
    oops

  lemma ipv4range_to_list_set_eq: "(\<Union>set (map ipv4range_to_set (ipv4range_to_list rs))) = ipv4range_to_set rs"
  by(induction rs) simp_all

  fun list_to_ipv4range where
    "list_to_ipv4range [r] = r" |
    "list_to_ipv4range (r#rs) = (IPv4Union r (list_to_ipv4range rs))" |
    "list_to_ipv4range [] = IPv4Range 2 1"

  lemma list_to_ipv4range_set_eq: "(\<Union>set (map ipv4range_to_set rs)) = ipv4range_to_set (list_to_ipv4range rs)"
    by(induction rs rule: list_to_ipv4range.induct) simp_all
    
  fun ipv4range_linearize where "ipv4range_linearize rs = list_to_ipv4range (ipv4range_to_list rs)"
  lemma "ipv4range_to_set (ipv4range_linearize r) = ipv4range_to_set r"
    by(simp, metis list_to_ipv4range_set_eq ipv4range_to_list_set_eq)

  fun ipv4range_optimize_same where "ipv4range_optimize_same rs = list_to_ipv4range (remdups (ipv4range_to_list rs))"
  lemma ipv4range_optimize_same_set_eq[simp]: "ipv4range_to_set (ipv4range_optimize_same rs) = ipv4range_to_set rs"
   by(simp, subst list_to_ipv4range_set_eq[symmetric]) (metis image_set ipv4range_to_list_set_eq set_remdups)

  fun ipv4range_is_simple where "ipv4range_is_simple (IPv4Range _ _) = True" | "ipv4range_is_simple (IPv4Union _ _) = False"
  fun ipv4rangelist_union_free where
    "ipv4rangelist_union_free (r#rs) = (ipv4range_is_simple r \<and> ipv4rangelist_union_free rs)" |
    "ipv4rangelist_union_free [] = True"
  lemma ipv4rangelist_union_freeX: "ipv4rangelist_union_free (r # rs) \<Longrightarrow> \<exists> s e. r = IPv4Range s e"
    by (induction rs) (cases r, simp, simp)+
  lemma ipv4rangelist_union_free_append: "ipv4rangelist_union_free (a@b) = (ipv4rangelist_union_free a \<and> ipv4rangelist_union_free b)"
    by (induction a) (auto)
  lemma ipv4range_to_list_union_free: "l = ipv4range_to_list r \<Longrightarrow> ipv4rangelist_union_free l"
    by(induction r arbitrary: l) (simp_all add: ipv4rangelist_union_free_append)

  fun ipv4range_setminus :: "ipv4range \<Rightarrow> ipv4range \<Rightarrow> ipv4range" where
    "ipv4range_setminus (IPv4Range s e) (IPv4Range ms me) = (
      if s > e \<or> ms > me then IPv4Range s e else
      if me \<ge> e
        then
          IPv4Range (if ms = 0 then 1 else s) (min e (ip_prev ms))
        else if ms \<le> s
        then
          IPv4Range (max s (ip_next me)) (if me = max_ipv4_addr then 0 else e)
        else
          IPv4Union (IPv4Range (if ms = 0 then 1 else s) (ip_prev ms)) (IPv4Range (ip_next me) (if me = max_ipv4_addr then 0 else e))
        )" |
     "ipv4range_setminus (IPv4Union r1 r2) t = IPv4Union (ipv4range_setminus r1 t) (ipv4range_setminus r2 t)"|
     "ipv4range_setminus t (IPv4Union r1 r2) = ipv4range_setminus (ipv4range_setminus t r1) r2"

  lemma ipv4range_setminus_rr_set_eq[simp]: "ipv4range_to_set(ipv4range_setminus (IPv4Range s e) (IPv4Range ms me)) = 
    ipv4range_to_set (IPv4Range s e) - ipv4range_to_set (IPv4Range ms me)"
     apply(simp only: ipv4range_setminus.simps)
     apply(case_tac "e < s") 
      apply simp
     apply(case_tac "me < ms") 
      apply simp
     apply(case_tac [!] "e \<le> me")
      apply(case_tac [!] "ms = 0") 
        apply(case_tac [!] "ms \<le> s") 
            apply(case_tac [!] "me = max_ipv4_addr")
                    apply(simp_all add: ip_prev_def ip_next_def min_def max_def)
            apply(safe)
                                  apply(auto)
                          apply(uint_arith) 
                         apply(uint_arith)
                        apply(uint_arith)
                       apply(uint_arith)
                      apply(uint_arith)
                     apply(uint_arith)
                    apply(uint_arith)
                   apply(uint_arith)
                  apply(uint_arith)
                 apply(uint_arith)
                apply(uint_arith)
               apply(uint_arith)
              apply(uint_arith)
             apply(uint_arith)
            apply(uint_arith)
           apply(uint_arith)
          apply(uint_arith)
         apply(uint_arith)
        apply(uint_arith)
       apply(uint_arith)
      apply(uint_arith)
     apply(uint_arith)
   done

  lemma ipv4range_setminus_set_eq[simp]: "ipv4range_to_set (ipv4range_setminus r1 r2) = 
    ipv4range_to_set r1 - ipv4range_to_set r2"
    using ipv4range_setminus_rr_set_eq by (induction rule: ipv4range_setminus.induct) auto
  lemma ipv4range_setminus_empty_struct: "ipv4range_empty r2 \<Longrightarrow> ipv4range_setminus r1 r2 = r1"
    by(induction r1 r2 rule: ipv4range_setminus.induct) auto

  definition "ipv4range_UNIV \<equiv> IPv4Range 0 max_ipv4_addr"
  lemma ipv4range_UNIV_set_eq[simp]: "ipv4range_to_set ipv4range_UNIV = UNIV"
    unfolding ipv4range_UNIV_def by simp
    
  fun ipv4range_invert where "ipv4range_invert r = ipv4range_setminus ipv4range_UNIV r"
  lemma ipv4range_invert_set_eq[simp]: "ipv4range_to_set (ipv4range_invert r) = UNIV - ipv4range_to_set r" by(auto)

  lemma ipv4range_invert_UNIV_empty: "ipv4range_empty (ipv4range_invert ipv4range_UNIV)" by simp

  fun ipv4range_intersection where "ipv4range_intersection r1 r2 = 
    ipv4range_optimize_same (ipv4range_setminus (ipv4range_union r1 r2) (ipv4range_union (ipv4range_invert r1) (ipv4range_invert r2)))"
  lemma ipv4range_intersection_set_eq[simp]: "ipv4range_to_set (ipv4range_intersection r1 r2) = ipv4range_to_set r1 \<inter> ipv4range_to_set r2"
    unfolding ipv4range_intersection.simps ipv4range_optimize_same_set_eq by auto
  
  lemma ipv4range_setminus_intersection_empty_struct_rr: 
    "ipv4range_empty (ipv4range_intersection (IPv4Range r1s r1e) (IPv4Range r2s r2e)) \<Longrightarrow> 
    ipv4range_setminus (IPv4Range r1s r1e) (IPv4Range r2s r2e) = (IPv4Range r1s r1e)"
    apply(subst(asm) ipv4range_empty_set_eq) 
    apply(subst(asm) ipv4range_intersection_set_eq)
    apply(unfold ipv4range_to_set.simps(1))
    apply(cases "ipv4range_empty (IPv4Range r1s r1e)", case_tac [!] "ipv4range_empty (IPv4Range r2s r2e)")
       apply(unfold ipv4range_empty.simps(1))
       apply(force, force, force)
    apply(cases "r1e < r2s") 
     defer
     apply(subgoal_tac "r2e < r1s")
      defer
      apply force
     apply(simp only: ipv4range_setminus.simps)
     apply(case_tac [!] "r1e \<le> r2e", case_tac [!] "r2s \<le> r1s")
           apply(auto)
     apply(metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(24) inc_i ip_prev_def le_minus min.absorb_iff1 word_le_sub1 word_zero_le)
    apply(metis inc_le ip_next_def max.order_iff)
  done

  declare ipv4range_intersection.simps[simp del]
  declare ipv4range_setminus.simps(1)[simp del]

  lemma ipv4range_setminus_intersection_empty_struct:
    "ipv4range_empty (ipv4range_intersection r1 r2) \<Longrightarrow> 
    ipv4range_setminus r1 r2 = r1"
    by (induction r1 r2 rule: ipv4range_setminus.induct, auto simp add: ipv4range_setminus_intersection_empty_struct_rr) fastforce

  definition "ipv4range_subset r1 r2 \<equiv> ipv4range_empty (ipv4range_setminus r1 r2)"
  lemma ipv4range_subset_set_eq[simp]: "ipv4range_subset r1 r2 = (ipv4range_to_set r1 \<subseteq> ipv4range_to_set r2)"
    unfolding ipv4range_subset_def by simp

  definition ipv4range_eq where 
    "ipv4range_eq r1 r2 = (ipv4range_subset r1 r2 \<and> ipv4range_subset r2 r1)"
  lemma ipv4range_eq_set_eq: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_to_set r1 = ipv4range_to_set r2"
    unfolding ipv4range_eq_def by auto
  thm iffD1[OF ipv4range_eq_set_eq]
  declare iffD1[OF ipv4range_eq_set_eq, simp]
  lemma ipv4range_eq_comm: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_eq r2 r1"
    unfolding ipv4range_eq_def by fast
  lemma ipv4range_to_set_alt: "ipv4range_to_set r = {x. ipv4range_element x r}"
    unfolding ipv4range_element_set_eq by blast
 
  lemma ipv4range_un_empty: "ipv4range_empty r1 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r2"
    by(subst ipv4range_eq_set_eq, simp)
  lemma ipv4range_un_emty_b: "ipv4range_empty r2 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r1"
    by(subst ipv4range_eq_set_eq, simp)
  
  lemma ipv4range_Diff_triv: 
    assumes "ipv4range_empty (ipv4range_intersection a b)" shows "ipv4range_eq (ipv4range_setminus a b) a"
    using ipv4range_setminus_intersection_empty_struct[OF assms] ipv4range_eq_set_eq[of a a] by simp

  fun ipv4range_size where
    "ipv4range_size (IPv4Union a b) = ipv4range_size a + ipv4range_size b" |
    "ipv4range_size (IPv4Range s e) = (if s \<le> e then 1 else 0)"
  lemma "ipv4range_size r = length (ipv4range_to_list r)"
    by(induction r, simp_all)

  lemma [simp]: "\<exists>x::ipv4range. y \<in> ipv4range_to_set x"
  proof show "y \<in> ipv4range_to_set ipv4range_UNIV" by simp qed

  quotient_type ipv4rq = ipv4range / ipv4range_eq
    by (unfold equivp_def, simp only: fun_eq_iff, unfold ipv4range_eq_set_eq) auto 
  (* lift all the things *)
  lift_definition ipv4rq_union :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> ipv4rq" is IPv4Union unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_setminus :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> ipv4rq" is ipv4range_setminus unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_intersection :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> ipv4rq" is ipv4range_intersection unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_empty :: "ipv4rq \<Rightarrow> bool" is ipv4range_empty unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_element :: "ipv4addr \<Rightarrow> ipv4rq \<Rightarrow> bool" is ipv4range_element unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_to_set :: "ipv4rq \<Rightarrow> ipv4addr set" is ipv4range_to_set unfolding ipv4range_eq_set_eq by simp
  lift_definition ipv4rq_UNIV :: ipv4rq is ipv4range_UNIV .
  lift_definition ipv4rq_eq :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> bool" is ipv4range_eq unfolding ipv4range_eq_set_eq by simp
  lemma ipv4rq_setminus_set_eq: "ipv4rq_to_set (ipv4rq_setminus r1 r2) = ipv4rq_to_set r1 - ipv4rq_to_set r2" by transfer simp
  lemma ipv4rq_intersection_set_eq: "ipv4rq_to_set (ipv4rq_intersection r1 r2) = ipv4rq_to_set r1 \<inter> ipv4rq_to_set r2" by transfer simp
  lemma ipv4rq_empty_set_eq: "ipv4rq_empty r = (ipv4rq_to_set r = {})" by transfer simp
  lemma ipv4rq_element_set_eq: "ipv4rq_element x r = (x \<in> ipv4rq_to_set r)" by transfer simp 
  lemma ipv4rq_UNIV_set_eq: "ipv4rq_to_set ipv4rq_UNIV = UNIV" by transfer simp
  lemmas ipv4rq_eqs[simp] = ipv4rq_intersection_set_eq ipv4rq_setminus_set_eq ipv4rq_empty_set_eq ipv4rq_UNIV_set_eq

  instantiation ipv4rq :: equal
  begin
    definition "equal_ipv4rq r1 r2 = ipv4rq_eq r1 r2"
  instance 
    proof
      case goal1 thus ?case unfolding equal_ipv4rq_def by transfer simp
    qed
  end

  abbreviation ipv4rq_abbr :: "ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> ipv4rq" ("[_; _]") where
    "[s;e] \<equiv> abs_ipv4rq (IPv4Range s e)"
  abbreviation ipv4un_abbr :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> ipv4rq" ("_ \<union>\<^sub>r\<^sub>g _") where
    "r1 \<union>\<^sub>r\<^sub>g r2 == ipv4rq_union r1 r2"

  lemma rq_on_set: "ipv4rq_to_set x = ipv4rq_to_set y \<longleftrightarrow> x = y"
    by (metis Quotient_ipv4rq Quotient_rel_rep ipv4range_eq_set_eq ipv4rq_to_set.rep_eq)

  fun ipv4range_intersection2 :: "ipv4range \<Rightarrow> ipv4range \<Rightarrow> ipv4range" where
  "ipv4range_intersection2 (IPv4Union a1 a2) (IPv4Union b1 b2) = IPv4Union 
    (IPv4Union (ipv4range_intersection2 a1 b1) (ipv4range_intersection2 a1 b2))
    (IPv4Union (ipv4range_intersection2 a2 b1) (ipv4range_intersection2 a2 b2))" (* equation can be left out *) |
  "ipv4range_intersection2 r (IPv4Union r1 r2) = (IPv4Union (ipv4range_intersection2 r r1) (ipv4range_intersection2 r r2))" |
  "ipv4range_intersection2 (IPv4Union r1 r2) r = (IPv4Union (ipv4range_intersection2 r1 r) (ipv4range_intersection2 r2 r))" |
  "ipv4range_intersection2 (IPv4Range s1 e1) (IPv4Range s2 e2) = IPv4Range (max s1 s2) (min e1 e2)"
  lemma ipv4range_intersection2_set_eq[simp]: "ipv4range_to_set (ipv4range_intersection2 r1 r2) = 
    ipv4range_to_set r1 \<inter> ipv4range_to_set r2"
    by (induction rule: ipv4range_intersection2.induct) auto

  lift_definition ipv4rq_intersection2 :: "ipv4rq \<Rightarrow> ipv4rq \<Rightarrow> ipv4rq" 
    is ipv4range_intersection2 unfolding ipv4range_eq_set_eq by simp
  lemma ipv4rq_intersection2_set_eq: "ipv4rq_to_set (ipv4rq_intersection2 r1 r2) = ipv4rq_to_set r1 \<inter> ipv4rq_to_set r2" 
    by transfer simp

  lift_definition ipv4rq_optimize_empty :: "ipv4rq \<Rightarrow> ipv4rq" 
    is ipv4range_optimize_empty unfolding ipv4range_eq_set_eq by simp
  lemma ipv4rq_optimize_empty_type_id: "(ipv4rq_optimize_empty r) = r"
    by(transfer, rename_tac rt, induct_tac rt)
      (unfold ipv4range_eq_set_eq, simp add: Let_def)+

  lemma ipv4rq_int_int2_code[code_unfold]: "ipv4rq_intersection = (\<lambda>x y. ipv4rq_optimize_empty (ipv4rq_intersection2 x y))"
    unfolding fun_eq_iff
    unfolding ipv4rq_optimize_empty_type_id rq_on_set[symmetric]
    unfolding ipv4rq_intersection2_set_eq ipv4rq_intersection_set_eq
    by clarify

  lemma rule_ipv4rq_eq_set: "ipv4rq_to_set x = ipv4rq_to_set y \<Longrightarrow> x = y" 
    using ipv4range_eq_set_eq by transfer blast


  definition "is_lowest_element x S = (x \<in> S \<and> (\<forall>y\<in>S. y \<le> x \<longrightarrow> y = x))"
  lemma is_lowest_elment_alt: "(x \<in> S \<and> (\<forall>y\<in>S. x \<le> y)) = is_lowest_element x S"
    unfolding is_lowest_element_def
    oops
    

  fun ipv4range_lowest_element where
    "ipv4range_lowest_element (IPv4Range s e) = (if s \<le> e then Some s else None)" | 
    "ipv4range_lowest_element (IPv4Union A B) = (case (ipv4range_lowest_element A, ipv4range_lowest_element B) of
      (Some a, Some b) \<Rightarrow> Some (if a < b then a else b) |
      (None, Some b) \<Rightarrow> Some b |
      (Some a, None) \<Rightarrow> Some a |
      (None, None) \<Rightarrow> None)
    "
  lemma ipv4range_lowest_none_empty: "ipv4range_lowest_element r = None \<longleftrightarrow> ipv4range_empty r"
    by(induction r, simp_all, fastforce)
  lemma ipv4range_lowest_element_correct_A: "ipv4range_lowest_element r = Some x \<Longrightarrow> ipv4range_element x r \<and> (\<forall>y \<in> ipv4range_to_set r. (y \<le> x \<longrightarrow> y = x))"
    apply(induction r arbitrary: x rule: ipv4range_lowest_element.induct)
     apply(rename_tac rs re x, case_tac "rs \<le> re", auto)[1]
    apply(subst(asm) ipv4range_lowest_element.simps(2))
    apply(rename_tac A B x)
    apply(case_tac     "ipv4range_lowest_element B")
     apply(case_tac[!] "ipv4range_lowest_element A")
       apply(simp_all add: ipv4range_lowest_none_empty)[3]
    apply fastforce
  done

  lemma smallerequalgreater: "((y :: ipv4addr) \<le> s \<longrightarrow> y = s) = (y \<ge> s)" by fastforce
  lemma somecase: "x = Some y \<Longrightarrow> case x of None \<Rightarrow> a | Some z \<Rightarrow> b z = b y" by simp

  lemma ipv4range_lowest_element_set_eq: "
    \<not>ipv4range_empty r \<Longrightarrow>
    (ipv4range_lowest_element r = Some x) = (is_lowest_element x (ipv4range_to_set r))"
    unfolding is_lowest_element_def
    apply(rule iffI)
    using ipv4range_lowest_element_correct_A ipv4range_lowest_none_empty apply simp
    apply(induction r arbitrary: x rule: ipv4range_lowest_element.induct)
    apply simp 
    apply(rename_tac A B x)
    apply(case_tac     "ipv4range_lowest_element B")
     apply(case_tac[!] "ipv4range_lowest_element A")
       apply(auto)[3]
    apply(subgoal_tac "\<not> ipv4range_empty A \<and> \<not> ipv4range_empty B")
     prefer 2
     using arg_cong[where f = Not, OF ipv4range_lowest_none_empty] apply(simp, metis)
    apply(clarsimp simp add: ipv4range_lowest_none_empty)
    proof - (* TODO: be rid of *)
      fix A :: ipv4range and B :: ipv4range and xa :: "32 word" and a :: "32 word" and aa :: "32 word"
      assume a1: "\<And>x. x \<in> ipv4range_to_set B \<and> (\<forall>y\<in>ipv4range_to_set B. y \<le> x \<longrightarrow> y = x) \<Longrightarrow> a = x"
      assume a2: "ipv4range_lowest_element B = Some a"
      assume a3: "ipv4range_lowest_element A = Some aa"
      assume a4: "xa \<in> ipv4range_to_set A \<or> xa \<in> ipv4range_to_set B"
      assume a5: "\<forall>y\<in>ipv4range_to_set A \<union> ipv4range_to_set B. y \<le> xa \<longrightarrow> y = xa"
      obtain sk\<^sub>0 :: "32 word \<Rightarrow> 32 word" where f1: "\<forall>x\<^sub>0. x\<^sub>0 \<notin> ipv4range_to_set B \<or> sk\<^sub>0 x\<^sub>0 \<in> ipv4range_to_set B \<and> sk\<^sub>0 x\<^sub>0 \<le> x\<^sub>0 \<and> sk\<^sub>0 x\<^sub>0 \<noteq> x\<^sub>0 \<or> a = x\<^sub>0"
        using a1 by (metis (lifting))
      have "\<forall>x\<^sub>0. x\<^sub>0 \<notin> {uub. uub \<in> ipv4range_to_set A \<or> uub \<in> ipv4range_to_set B} \<or> \<not> x\<^sub>0 \<le> xa \<or> xa = x\<^sub>0"
        using a5 by blast
      hence f2: "\<forall>x\<^sub>0. \<not> (x\<^sub>0 \<in> ipv4range_to_set A \<or> x\<^sub>0 \<in> ipv4range_to_set B) \<or> xa = x\<^sub>0 \<or> \<not> x\<^sub>0 \<le> xa"
        by blast
      hence "xa \<notin> ipv4range_to_set B \<or> a = xa"
        using f1 by (metis (lifting))
      hence "aa = xa \<or> a = xa"
        using f2 a3 a4 by (metis (lifting) ipv4range_element_set_eq ipv4range_lowest_element_correct_A le_less_linear less_asym')
      thus "(aa < a \<longrightarrow> aa = xa) \<and> (\<not> aa < a \<longrightarrow> a = xa)"
        using a2 f2 a3 by (metis (lifting) ipv4range_element_set_eq ipv4range_lowest_element_correct_A le_less_linear less_asym')
    qed

  lift_definition ipv4rq_lowest_element :: "ipv4rq \<Rightarrow> ipv4addr option" is ipv4range_lowest_element unfolding ipv4range_eq_set_eq
  proof -
    fix r1 r2
    assume eq: "ipv4range_to_set r1 = ipv4range_to_set r2"
    show "ipv4range_lowest_element r1 = ipv4range_lowest_element r2"
    proof(cases "ipv4range_empty r1")
      case True
      moreover
      with eq have "ipv4range_empty r2" by simp
      ultimately
      have "ipv4range_lowest_element r1 = None" "ipv4range_lowest_element r2 = None" 
        using ipv4range_lowest_none_empty[symmetric] by simp_all
      then show ?thesis ..
    next
      case False
      with eq have False2: "\<not>ipv4range_empty r2" by simp
      note ipv4range_lowest_element_set_eq[OF False] ipv4range_lowest_element_set_eq[OF False2]
      with eq show ?thesis 
        by (metis not_Some_eq)
    qed
  qed

  lemma ipv4rq_lowest_element_set_eq:
   "\<not>ipv4rq_empty r \<Longrightarrow>
    (ipv4rq_lowest_element r = Some x) = (is_lowest_element x (ipv4rq_to_set r))"
    by(transfer, simp add: ipv4range_lowest_element_set_eq)

  lemma ipv4rq_lowest_in:
    assumes "\<not>ipv4rq_empty r"
    shows "ipv4rq_element (the (ipv4rq_lowest_element r)) r" 
  using assms by(transfer, metis ipv4range_lowest_element_correct_A ipv4range_lowest_none_empty option.exhaust option.sel)
  
  fun list_to_ipv4rq :: "ipv4rq list \<Rightarrow> ipv4rq" where
    "list_to_ipv4rq [] = ipv4rq_setminus ipv4rq_UNIV ipv4rq_UNIV" |
    "list_to_ipv4rq [x] = x" |
    "list_to_ipv4rq (x#xs) = ipv4rq_union x (list_to_ipv4rq xs)"
  lemma list_to_ipv4rq_set_eq[simp]: "ipv4rq_to_set (list_to_ipv4rq rs) = (\<Union>set (map ipv4rq_to_set rs))"
    apply(induction rs rule: list_to_ipv4rq.induct)
    apply(simp_all)
oops
(*TODO julius has the proof and we lost a lemma during 3-way merge*)
    
end
