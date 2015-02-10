(*  Title:      IPv4Addr.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory IPv4Addr
imports Main
  NumberWang
  Bitrange
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

  


  definition ipv4range_single :: "ipv4addr \<Rightarrow> 32 bitrange" where
    "ipv4range_single ip \<equiv> Bitrange ip ip"

  definition ipv4range_range :: "ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> 32 bitrange" where
    "ipv4range_range ip_start ip_end \<equiv> Bitrange ip_start ip_end"

  definition ipv4range_to_set :: "32 bitrange \<Rightarrow> (ipv4addr) set" where
    "ipv4range_to_set rg = bitrange_to_set rg"

  definition ipv4range_element  :: "'a::len word \<Rightarrow> 'a::len bitrange \<Rightarrow> bool" where
    "ipv4range_element el rg = bitrange_element el rg"

  definition ipv4range_union :: "32 bitrange \<Rightarrow> 32 bitrange \<Rightarrow> 32 bitrange" where 
    "ipv4range_union r1 r2 = bitrange_union r1 r2"


  definition ipv4range_empty :: "32 bitrange \<Rightarrow> bool" where
    "ipv4range_empty rg = bitrange_empty rg"


  definition ipv4range_setminus :: "32 bitrange \<Rightarrow> 32 bitrange \<Rightarrow> 32 bitrange" where
    "ipv4range_setminus r1 r2 = bitrange_setminus r1 r2"


  definition ipv4range_UNIV :: "32 bitrange" where "ipv4range_UNIV \<equiv> bitrange_UNIV"
    
  definition ipv4range_invert :: "32 bitrange \<Rightarrow> 32 bitrange" where 
    "ipv4range_invert r = ipv4range_setminus ipv4range_UNIV r"


  definition ipv4range_intersection :: "32 bitrange \<Rightarrow> 32 bitrange \<Rightarrow> 32 bitrange" where
    "ipv4range_intersection r1 r2 = bitrange_intersection r1 r2"


  definition ipv4range_subset:: "32 bitrange \<Rightarrow> 32 bitrange \<Rightarrow> bool" where
    "ipv4range_subset r1 r2 \<equiv> bitrange_subset r1 r2"


  definition ipv4range_eq :: "32 bitrange \<Rightarrow> 32 bitrange \<Rightarrow> bool" where 
    "ipv4range_eq r1 r2 = bitrange_eq r1 r2"




  lemma ipv4range_single_set_eq: "ipv4range_to_set (ipv4range_single ip) = {ip}"
    by(simp add: ipv4range_single_def ipv4range_to_set_def)
  lemma ipv4range_range_set_eq: "ipv4range_to_set (ipv4range_range ip1 ip2) = {ip1 .. ip2}"
    by(simp add: ipv4range_range_def ipv4range_to_set_def)
  
  lemma ipv4range_element_set_eq[simp]: "ipv4range_element el rg = (el \<in> ipv4range_to_set rg)"
    by(simp add: ipv4range_element_def ipv4range_to_set_def)
  lemma ipv4range_union_set_eq[simp]: "ipv4range_to_set (ipv4range_union r1 r2) = ipv4range_to_set r1 \<union> ipv4range_to_set r2"
    by(simp add: ipv4range_to_set_def ipv4range_union_def)
  lemma ipv4range_empty_set_eq[simp]: "ipv4range_empty r \<longleftrightarrow> ipv4range_to_set r = {}"
    by(simp add: ipv4range_to_set_def ipv4range_empty_def)
  lemma ipv4range_setminus_set_eq[simp]: "ipv4range_to_set (ipv4range_setminus r1 r2) = ipv4range_to_set r1 - ipv4range_to_set r2"
    by(simp add: ipv4range_setminus_def ipv4range_to_set_def)
  lemma ipv4range_UNIV_set_eq[simp]: "ipv4range_to_set ipv4range_UNIV = UNIV"
    by(simp only: ipv4range_UNIV_def ipv4range_to_set_def bitrange_UNIV_set_eq)
  lemma ipv4range_invert_set_eq[simp]: "ipv4range_to_set (ipv4range_invert r) = UNIV - ipv4range_to_set r"
    by(simp add: ipv4range_invert_def)
  lemma ipv4range_intersection_set_eq[simp]: "ipv4range_to_set (ipv4range_intersection r1 r2) = ipv4range_to_set r1 \<inter> ipv4range_to_set r2"
    by(simp add: ipv4range_intersection_def ipv4range_to_set_def)
  lemma ipv4range_subset_set_eq[simp]: "ipv4range_subset r1 r2 = (ipv4range_to_set r1 \<subseteq> ipv4range_to_set r2)"
    by(simp add: ipv4range_subset_def ipv4range_to_set_def)
  lemma ipv4range_eq_set_eq: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_to_set r1 = ipv4range_to_set r2"
    unfolding ipv4range_eq_def ipv4range_to_set_def using bitrange_eq_set_eq by blast

  declare ipv4range_range_set_eq[unfolded ipv4range_range_def, simp]
  declare ipv4range_union_set_eq[unfolded ipv4range_union_def bitrange_union.simps, simp]


  thm iffD1[OF ipv4range_eq_set_eq]
  declare iffD1[OF ipv4range_eq_set_eq, simp]
  lemma ipv4range_eq_comm: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_eq r2 r1"
    unfolding ipv4range_eq_def bitrange_eq_set_eq by blast
  lemma ipv4range_to_set_alt: "ipv4range_to_set r = {x. ipv4range_element x r}"
    unfolding ipv4range_element_set_eq by blast
 
  lemma ipv4range_un_empty: "ipv4range_empty r1 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r2"
    by(subst ipv4range_eq_set_eq, simp)
  lemma ipv4range_un_emty_b: "ipv4range_empty r2 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r1"
    by(subst ipv4range_eq_set_eq, simp)
  
  lemma ipv4range_Diff_triv: "ipv4range_empty (ipv4range_intersection a b) \<Longrightarrow> ipv4range_eq (ipv4range_setminus a b) a"
    by(simp only: bitrange_Diff_triv ipv4range_eq_def ipv4range_setminus_def ipv4range_intersection_def ipv4range_empty_def)


  definition "is_lowest_element x S = (x \<in> S \<and> (\<forall>y\<in>S. y \<le> x \<longrightarrow> y = x))"
  lemma is_lowest_elment_alt: "(x \<in> S \<and> (\<forall>y\<in>S. x \<le> y)) = is_lowest_element x S"
    unfolding is_lowest_element_def
    oops
    
  fun ipv4range_lowest_element :: "32 bitrange \<Rightarrow> ipv4addr option" where
    "ipv4range_lowest_element (Bitrange s e) = (if s \<le> e then Some s else None)" | 
    "ipv4range_lowest_element (RangeUnion A B) = (case (ipv4range_lowest_element A, ipv4range_lowest_element B) of
      (Some a, Some b) \<Rightarrow> Some (if a < b then a else b) |
      (None, Some b) \<Rightarrow> Some b |
      (Some a, None) \<Rightarrow> Some a |
      (None, None) \<Rightarrow> None)
    "
  lemma ipv4range_lowest_none_empty: "ipv4range_lowest_element r = None \<longleftrightarrow> ipv4range_empty r"
    apply(induction r)
     apply(simp_all)
    apply(force)
  done
    

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
      fix A :: "32 bitrange" and B :: "32 bitrange" and xa :: "32 word" and a :: "32 word" and aa :: "32 word"
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

   

end
