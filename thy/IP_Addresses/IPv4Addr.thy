(*  Title:      IPv4Addr.thy
    Authors:    Cornelius Diekmann, Julius Michaelis
*)
theory IPv4Addr
imports Main
  IPAddr
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

value "(2::nat) < 2^32" (*without Code_Target_Nat, this would be really slow*)


section \<open>Modelling IPv4 Adresses\<close>
  text\<open>An IPv4 address is basically a 32 bit unsigned integer\<close>
  type_synonym ipv4addr = "32 word"
 
  value "42 :: ipv4addr"

  value "(42 :: ipv4addr) \<le> 45"

  text\<open>Conversion between natural numbers and IPv4 adresses\<close>
  definition nat_of_ipv4addr :: "ipv4addr \<Rightarrow> nat" where
    "nat_of_ipv4addr a = unat a"
  definition ipv4addr_of_nat :: "nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_nat n =  of_nat n"

  lemma "((nat_of_ipv4addr (42::ipv4addr))::nat) = 42" by eval
  lemma "((ipv4addr_of_nat (42::nat))::ipv4addr) = 42" by eval

  text\<open>The maximum IPv4 addres\<close>
  definition max_ipv4_addr :: "ipv4addr" where 
    "max_ipv4_addr \<equiv> ipv4addr_of_nat ((2^32) - 1)"

  lemma max_ipv4_addr_number: "max_ipv4_addr = 4294967295"
    unfolding max_ipv4_addr_def ipv4addr_of_nat_def by(simp)
  lemma "max_ipv4_addr = 0b11111111111111111111111111111111"
    by(fact max_ipv4_addr_number)
  lemma max_ipv4_addr_max_word: "max_ipv4_addr = max_word"
    by(simp add: max_ipv4_addr_number max_word_def)
  lemma max_ipv4_addr_max[simp]: "\<forall>a. a \<le> max_ipv4_addr"
    by(simp add: max_ipv4_addr_max_word)
  lemma range_0_max_UNIV: "UNIV = {0 .. max_ipv4_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ipv4_addr_max_word) fastforce

  text\<open>identity functions\<close>
  lemma nat_of_ipv4addr_ipv4addr_of_nat: "\<lbrakk> n \<le> nat_of_ipv4addr max_ipv4_addr \<rbrakk> \<Longrightarrow> nat_of_ipv4addr (ipv4addr_of_nat n) = n"
    by (metis ipv4addr_of_nat_def le_unat_uoi nat_of_ipv4addr_def)
  lemma nat_of_ipv4addr_ipv4addr_of_nat_mod: "nat_of_ipv4addr (ipv4addr_of_nat n) = n mod 2^32"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def unat_of_nat)
  lemma ipv4addr_of_nat_nat_of_ipv4addr: "ipv4addr_of_nat (nat_of_ipv4addr addr) = addr"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def)


  text\<open>Equality of IPv4 adresses\<close>
  lemma "\<lbrakk> n \<le> nat_of_ipv4addr max_ipv4_addr \<rbrakk> \<Longrightarrow> nat_of_ipv4addr (ipv4addr_of_nat n) = n"
    apply(simp add: nat_of_ipv4addr_def ipv4addr_of_nat_def)
    apply(induction n)
     apply(simp_all)
    by(unat_arith)

  lemma ipv4addr_of_nat_eq: "x = y \<Longrightarrow> ipv4addr_of_nat x = ipv4addr_of_nat y"
    by(simp add: ipv4addr_of_nat_def)

subsection\<open>Representing IPv4 Adresses\<close>
  fun ipv4addr_of_dotdecimal :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_dotdecimal (a,b,c,d) = ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a )"

  fun dotdecimal_of_ipv4addr :: "ipv4addr \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
    "dotdecimal_of_ipv4addr a = (nat_of_ipv4addr ((a >> 24) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 16) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 8) AND 0xFF), 
                                    nat_of_ipv4addr (a AND 0xff))"

  declare ipv4addr_of_dotdecimal.simps[simp del]
  declare dotdecimal_of_ipv4addr.simps[simp del]

  lemma "ipv4addr_of_dotdecimal (192, 168, 0, 1) = 3232235521" by eval
  lemma "dotdecimal_of_ipv4addr 3232235521 = (192, 168, 0, 1)" by eval

  text\<open>a different notation for @{term ipv4addr_of_dotdecimal}\<close>
  lemma ipv4addr_of_dotdecimal_bit: 
    "ipv4addr_of_dotdecimal (a,b,c,d) = (ipv4addr_of_nat a << 24) + (ipv4addr_of_nat b << 16) + (ipv4addr_of_nat c << 8) + ipv4addr_of_nat d"
  proof -
    have a: "(ipv4addr_of_nat a) << 24 = ipv4addr_of_nat (a * 16777216)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n)
    have b: "(ipv4addr_of_nat b) << 16 = ipv4addr_of_nat (b * 65536)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n)
    have c: "(ipv4addr_of_nat c) << 8 = ipv4addr_of_nat (c * 256)"
      by(simp add: ipv4addr_of_nat_def shiftl_t2n)
    have ipv4addr_of_nat_suc: "\<And>x. ipv4addr_of_nat (Suc x) = word_succ (ipv4addr_of_nat (x))"
      by(simp add: ipv4addr_of_nat_def, metis Abs_fnat_hom_Suc of_nat_Suc)
    { fix x y
    have "ipv4addr_of_nat x + ipv4addr_of_nat y = ipv4addr_of_nat (x+y)"
      apply(induction x arbitrary: y)
       apply(simp add: ipv4addr_of_nat_def)
      apply(simp add: ipv4addr_of_nat_suc word_succ_p1)
      done
    } from this a b c
    show ?thesis
    apply(simp add: ipv4addr_of_dotdecimal.simps)
    apply(rule ipv4addr_of_nat_eq)
    by presburger
  qed


  lemma size_ipv4addr: "size (x::ipv4addr) = 32" by(simp add:word_size)
  lemma "(4294967296::ipv4addr) = 2^32" by eval

  lemma nat_of_ipv4addr_slice_ipv4addr_of_nat: 
    "nat_of_ipv4addr (slice x (ipv4addr_of_nat a)) = (nat_of_ipv4addr (ipv4addr_of_nat a)) div 2^x"
    proof -
      have mod4294967296: "int a mod 4294967296 = int (a mod 4294967296)"
        using zmod_int by auto
      (*TODO: why is this gone in 2016?*)
      have zpower_int: "\<And>m n. int m ^ n = int (m ^ n)" using of_nat_power by simp
      have int_pullin: "int (a mod 4294967296) div 2 ^ x = int (a mod 4294967296 div 2 ^ x)"
        using zpower_int zdiv_int by (metis of_nat_numeral) 
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
    by(simp add: mask_def)
  lemma ipv4addr_of_nat_AND_mask8: "(ipv4addr_of_nat a) AND mask 8 = (ipv4addr_of_nat (a mod 256))"
    apply(simp add: ipv4addr_of_nat_def and_mask_mod_2p)
    apply(simp add: word_of_nat) (*use this to get rid of of_nat. All thm are with word_of_int*)
    apply(simp add: uint_word_of_int)
    apply(subst mod_mod_cancel)
     apply simp
    apply(simp add: zmod_int)
    done
 
  lemma dotdecimal_of_ipv4addr_ipv4addr_of_dotdecimal:
  "\<lbrakk> a < 256; b < 256; c < 256; d < 256 \<rbrakk> \<Longrightarrow> dotdecimal_of_ipv4addr (ipv4addr_of_dotdecimal (a,b,c,d)) = (a,b,c,d)"
  proof -
    assume  "a < 256" and "b < 256" and "c < 256" and "d < 256"
    note assms= \<open>a < 256\<close> \<open>b < 256\<close> \<open>c < 256\<close> \<open>d < 256\<close> 
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
      apply(simp add: NumberWang.div65536[simplified]) (*we add the simplified because the WordLemmaBucket adds some additional simp rules*)
      done
      --\<open>When @{file "../Word_Lib/Word_Lemmas.thy"} is imported, some @{file "NumberWang.thy"} lemmas need the [simplified] attribute
          because WordLemmaBucket adds some simp rules. This theory should also work without Word_Lemmas\<close>
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
      apply(simp add: NumberWang.div256[simplified])
      done
    from \<open>d < 256\<close> have d: "nat_of_ipv4addr (ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) AND mask 8) = d"
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
      apply(simp add: ipv4addr_of_dotdecimal.simps dotdecimal_of_ipv4addr.simps)
      apply(simp add: ipv4addr_and_255)
      done
  qed
  
  lemma ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr: 
    "(ipv4addr_of_dotdecimal (dotdecimal_of_ipv4addr ip)) = ip"
  proof -
    have ip_and_mask8_bl_drop24: "(ip::ipv4addr) AND mask 8 = of_bl (drop 24 (to_bl ip))"
      by(simp add: Word_Lemmas.of_drop_to_bl size_ipv4addr)
  
    have List_rev_drop_geqn: "\<And>x n. length x \<ge> n \<Longrightarrow> (take n (rev x)) = rev (drop (length x - n) x)"
      by(simp add: List.rev_drop)
  
    have and_mask_bl_take: "\<And> x n. length x \<ge> n \<Longrightarrow> ((of_bl x) AND mask n) = (of_bl (rev (take n (rev (x)))))"
      apply(simp add: List_rev_drop_geqn)
      apply(simp add: Word_Lib.of_bl_drop)
      done
  
    have bit_equality: "((ip >> 24) AND 0xFF << 24) + ((ip >> 16) AND 0xFF << 16) + ((ip >> 8) AND 0xFF << 8) + (ip AND 0xFF) =
      of_bl (take 8 (to_bl ip) @ take 8 (drop 8 (to_bl ip)) @ take 8 (drop 16 (to_bl ip)) @ drop 24 (to_bl ip))"
      apply(simp add: ipv4addr_and_255)
      apply(simp add: shiftr_slice)
      apply(simp add: Word.slice_take' size_ipv4addr)
      apply(simp add: and_mask_bl_take)
      apply(simp add: List_rev_drop_geqn)
      apply(simp add: drop_take)
      apply(simp add: Word.shiftl_of_bl)
      apply(simp add: of_bl_append)
      apply(simp add: ip_and_mask8_bl_drop24)
      done
  
    have blip_split: "\<And> blip. length blip = 32 \<Longrightarrow>
      blip = (take 8 blip) @ (take 8 (drop 8 blip)) @ (take 8 (drop 16 blip)) @ (take 8 (drop 24 blip))"
      apply(case_tac blip)
      apply(simp_all)
      (*thin_tac "blip = ?x",*)
      apply(rename_tac blip,case_tac blip,simp_all)+ (*I'm so sorry for this ...*)
      done
  
    have "ipv4addr_of_dotdecimal (dotdecimal_of_ipv4addr ip) = of_bl (to_bl ip)"
      apply(subst blip_split)
       apply(simp)
      apply(simp add: ipv4addr_of_dotdecimal_bit dotdecimal_of_ipv4addr.simps)
      apply(simp add: ipv4addr_of_nat_nat_of_ipv4addr)
      apply(simp add: bit_equality)
      done
  
    thus ?thesis using Word.word_bl.Rep_inverse[symmetric] by simp
  qed


  lemma ipv4addr_of_dotdecimal_eqE: "\<lbrakk> ipv4addr_of_dotdecimal (a,b,c,d) = ipv4addr_of_dotdecimal (e,f,g,h); a < 256; b < 256; c < 256; d < 256; e < 256; f < 256; g < 256; h < 256 \<rbrakk> \<Longrightarrow>
     a = e \<and> b = f \<and> c = g \<and> d = h"
     by (metis Pair_inject dotdecimal_of_ipv4addr_ipv4addr_of_dotdecimal)


subsection\<open>IP ranges\<close>
  lemma UNIV_ipv4addrset: "(UNIV :: ipv4addr set) = {0 .. max_ipv4_addr}" by(auto)
  lemma "(42::ipv4addr) \<in> UNIV" by eval


  (*Warning, not executable!*)
  definition ipv4set_from_netmask::"ipv4addr \<Rightarrow> ipv4addr \<Rightarrow> ipv4addr set" where
    "ipv4set_from_netmask addr netmask \<equiv> ipset_from_netmask addr netmask"


  lemma "ipv4set_from_netmask (ipv4addr_of_dotdecimal (192,168,0,42)) (ipv4addr_of_dotdecimal (255,255,0,0)) =
          {ipv4addr_of_dotdecimal (192,168,0,0) .. ipv4addr_of_dotdecimal (192,168,255,255)}"
   by(simp add: ipv4set_from_netmask_def ipset_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)

  lemma "ipv4set_from_netmask (ipv4addr_of_dotdecimal (192,168,0,42)) (ipv4addr_of_dotdecimal (0,0,0,0)) = UNIV"
    by(simp add: UNIV_ipv4addrset ipset_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipv4set_from_netmask_def max_ipv4_addr_max_word)
   
  
  text\<open>192.168.0.0/24\<close>
  definition ipv4set_from_cidr::"ipv4addr \<Rightarrow> nat \<Rightarrow> ipv4addr set" where
    "ipv4set_from_cidr addr pflength \<equiv> ipset_from_cidr addr pflength"

  lemma ipv4set_from_cidr_alt: "ipv4set_from_cidr addr pflength = ipv4set_from_netmask addr ((mask pflength) << (32 - pflength))"
    by(simp add: ipv4set_from_cidr_def ipv4set_from_netmask_def ipset_from_cidr_def)

  lemma "ipv4set_from_cidr (ipv4addr_of_dotdecimal (192,168,0,42)) 16 = 
          {ipv4addr_of_dotdecimal (192,168,0,0) .. ipv4addr_of_dotdecimal (192,168,255,255)}"
   by(simp add: ipv4set_from_cidr_def ipset_from_cidr_alt mask_def  ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)

  lemma ipv4set_from_cidr_0: "ipv4set_from_cidr foo 0 = UNIV"
    by(simp add: ipv4set_from_cidr_def ipset_from_cidr_0)

  lemma "ipv4set_from_cidr 0 0 = UNIV"
    by(simp add: ipv4set_from_cidr_def ipset_from_cidr_0)
  lemma "ip \<in> (ipv4set_from_cidr (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 0)"
    by(simp add: ipv4set_from_cidr_0)

  lemma ipv4set_from_cidr_32: "ipv4set_from_cidr foo 32 = {foo}"
    by(simp add: ipv4set_from_cidr_alt ipv4set_from_netmask_def mask_def ipset_from_netmask_minusone)

  (*TODO: delete completely, use generic version*)
  lemma "ipv4set_from_cidr pre len = {(pre AND ((mask len) << (32 - len))) .. pre OR (mask (32 - len))}"
    by (simp add: ipset_from_cidr_alt ipv4set_from_cidr_def)


  text\<open>making element check executable\<close>
  lemma addr_in_ipv4set_from_netmask_code[code_unfold]: 
    "addr \<in> (ipv4set_from_netmask base netmask) \<longleftrightarrow> (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by (simp add: addr_in_ipset_from_netmask_code ipv4set_from_netmask_def)
  lemma addr_in_ipv4set_from_cidr_code[code_unfold]: "addr \<in> (ipv4set_from_cidr pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> pre OR (mask (32 - len))"
    by(simp add: ipv4set_from_cidr_def addr_in_ipset_from_cidr_code)

  value[code] "ipv4addr_of_dotdecimal (192,168,4,8) \<in> (ipv4set_from_cidr (ipv4addr_of_dotdecimal (192,168,0,42)) 16)"

  
  definition ipv4range_UNIV :: "32 wordinterval" where "ipv4range_UNIV \<equiv> wordinterval_UNIV"
  
  lemma ipv4range_UNIV_set_eq: "wordinterval_to_set ipv4range_UNIV = UNIV"
    by(simp only: ipv4range_UNIV_def wordinterval_UNIV_set_eq)
 


  thm iffD1[OF wordinterval_eq_set_eq]
  (*TODO: probably the following is a good idea?*)
  (*
  declare iffD1[OF wordinterval_eq_set_eq, cong]
  *)


  text\<open>This @{text "len_of TYPE('a)"} is 32 for IPv4 addresses.\<close>
  lemma ipv4cidr_to_interval_simps[code_unfold]: "ipcidr_to_interval ((pre::ipv4addr), len) = (
      let netmask = (mask len) << (32 - len);
          network_prefix = (pre AND netmask)
      in (network_prefix, network_prefix OR (NOT netmask)))"
  by(simp add: ipcidr_to_interval_def Let_def ipcidr_to_interval_start.simps ipcidr_to_interval_end.simps)
 
end
