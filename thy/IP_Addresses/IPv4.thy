(*  Title:      IPv4.thy
    Authors:    Cornelius Diekmann, Julius Michaelis
*)
theory IPv4
imports IP_Address
        NumberWang_IPv4
        (* include "~~/src/HOL/Library/Code_Target_Nat" if you need to work with actual numbers.*)
begin


section \<open>IPv4 Adresses\<close>
  text\<open>An IPv4 address is basically a 32 bit unsigned integer.\<close>
  type_synonym ipv4addr = "32 word"

  text\<open>Conversion between natural numbers and IPv4 adresses\<close>
  definition nat_of_ipv4addr :: "ipv4addr \<Rightarrow> nat" where
    "nat_of_ipv4addr a = unat a"
  definition ipv4addr_of_nat :: "nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_nat n =  of_nat n"

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
  lemma UNIV_ipv4addrset: "UNIV = {0 .. max_ipv4_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ipv4_addr_max_word) fastforce

  text\<open>identity functions\<close>
  lemma nat_of_ipv4addr_ipv4addr_of_nat:
    "\<lbrakk> n \<le> nat_of_ipv4addr max_ipv4_addr \<rbrakk> \<Longrightarrow> nat_of_ipv4addr (ipv4addr_of_nat n) = n"
    by (simp add: ipv4addr_of_nat_def le_unat_uoi nat_of_ipv4addr_def)
  lemma nat_of_ipv4addr_ipv4addr_of_nat_mod: "nat_of_ipv4addr (ipv4addr_of_nat n) = n mod 2^32"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def unat_of_nat)
  lemma ipv4addr_of_nat_nat_of_ipv4addr: "ipv4addr_of_nat (nat_of_ipv4addr addr) = addr"
    by(simp add: ipv4addr_of_nat_def nat_of_ipv4addr_def)

subsection\<open>Representing IPv4 Adresses (Syntax)\<close>
  fun ipv4addr_of_dotdecimal :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> ipv4addr" where
    "ipv4addr_of_dotdecimal (a,b,c,d) = ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a )"

  fun dotdecimal_of_ipv4addr :: "ipv4addr \<Rightarrow> nat \<times> nat \<times> nat \<times> nat" where
    "dotdecimal_of_ipv4addr a = (nat_of_ipv4addr ((a >> 24) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 16) AND 0xFF), 
                                    nat_of_ipv4addr ((a >> 8) AND 0xFF), 
                                    nat_of_ipv4addr (a AND 0xff))"

  declare ipv4addr_of_dotdecimal.simps[simp del]
  declare dotdecimal_of_ipv4addr.simps[simp del]

  text\<open>Examples:\<close>
  lemma "ipv4addr_of_dotdecimal (192, 168, 0, 1) = 3232235521"
    by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
    (*could be solved by eval, but needs "~~/src/HOL/Library/Code_Target_Nat"*)
  lemma "dotdecimal_of_ipv4addr 3232235521 = (192, 168, 0, 1)"
    by(simp add: dotdecimal_of_ipv4addr.simps nat_of_ipv4addr_def)

  text\<open>a different notation for @{term ipv4addr_of_dotdecimal}\<close>
  lemma ipv4addr_of_dotdecimal_bit: 
    "ipv4addr_of_dotdecimal (a,b,c,d) =
      (ipv4addr_of_nat a << 24) + (ipv4addr_of_nat b << 16) +
       (ipv4addr_of_nat c << 8) + ipv4addr_of_nat d"
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
         apply(simp add: ipv4addr_of_nat_def; fail)
        by(simp add: ipv4addr_of_nat_suc word_succ_p1)
    } from this a b c
    show ?thesis
      apply(simp add: ipv4addr_of_dotdecimal.simps)
      apply(rule arg_cong[where f=ipv4addr_of_nat])
      apply(thin_tac _)+
      by presburger
  qed

  lemma size_ipv4addr: "size (x::ipv4addr) = 32" by(simp add:word_size)
 
  lemma dotdecimal_of_ipv4addr_ipv4addr_of_dotdecimal:
  "\<lbrakk> a < 256; b < 256; c < 256; d < 256 \<rbrakk> \<Longrightarrow>
    dotdecimal_of_ipv4addr (ipv4addr_of_dotdecimal (a,b,c,d)) = (a,b,c,d)"
  proof -
    assume  "a < 256" and "b < 256" and "c < 256" and "d < 256"
    note assms= \<open>a < 256\<close> \<open>b < 256\<close> \<open>c < 256\<close> \<open>d < 256\<close> 
    hence a:  "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 24) AND mask 8) = a"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
        apply(simp; fail)
       apply(simp; fail)
      apply(simp)
      apply(subst mod_pos_pos_trivial)
        apply(simp; fail)
       apply(simp; fail)
      apply(subst mod_pos_pos_trivial)
        by simp+
    have ipv4addr_of_nat_AND_mask8: "(ipv4addr_of_nat a) AND mask 8 = (ipv4addr_of_nat (a mod 256))"
      for a
      apply(simp add: ipv4addr_of_nat_def and_mask_mod_2p)
      apply(simp add: word_of_nat) (*use this to get rid of of_nat. All thm are with word_of_int*)
      apply(simp add: uint_word_of_int)
      apply(subst mod_mod_cancel)
       apply(simp; fail)
      apply(simp add: zmod_int)
      done
    from assms have b:
      "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 16) AND mask 8) = b"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
        apply(simp; fail)
       apply(simp; fail)
      apply(subst mod_pos_pos_trivial[where b="4294967296"])
        apply(simp; fail)
       apply(simp; fail)
      apply(simp add: NumberWang_IPv4.div65536[simplified])
      (*The [simplified] is needed because Word_Lib adds some additional simp rules*)
      done
      --\<open>When @{file "../Word_Lib/Word_Lemmas.thy"} is imported,
         some @{file "Word_More.thy"} and @{file "NumberWang_IPv4.thy"} lemmas need the
         [simplified] attribute because @{text Word_Lib} adds some simp rules.
         This theory should also work without @{file "../Word_Lib/Word_Lemmas.thy"}\<close>
    from assms have c:
      "nat_of_ipv4addr ((ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) >> 8) AND mask 8) = c"
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def unat_def)
      apply(simp add: and_mask_mod_2p)
      apply(simp add: shiftr_div_2n)
      apply(simp add: uint_word_of_int)
      apply(subst mod_pos_pos_trivial)
        apply(simp; fail)
       apply(simp; fail)
      apply(subst mod_pos_pos_trivial[where b="4294967296"])
        apply(simp; fail)
       apply(simp; fail)
      apply(simp add: NumberWang_IPv4.div256[simplified])
      done
    from \<open>d < 256\<close> have d: "nat_of_ipv4addr (ipv4addr_of_nat (d + 256 * c + 65536 * b + 16777216 * a) AND mask 8) = d"
      apply(simp add: ipv4addr_of_nat_AND_mask8)
      apply(simp add: ipv4addr_of_nat_def word_of_nat)
      apply(simp add: nat_of_ipv4addr_def)
      apply(subgoal_tac "(d + 256 * c + 65536 * b + 16777216 * a) mod 256 = d")
       apply(simp add: unat_def uint_word_of_int mod_pos_pos_trivial; fail)
      apply(simp add: NumberWang_IPv4.mod256)
      done
    from a b c d show ?thesis
      apply(simp add: ipv4addr_of_dotdecimal.simps dotdecimal_of_ipv4addr.simps)
      apply(simp add: mask_def)
      done
  qed
  
  lemma ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr: 
    "(ipv4addr_of_dotdecimal (dotdecimal_of_ipv4addr ip)) = ip"
  proof -
    have ip_and_mask8_bl_drop24: "(ip::ipv4addr) AND mask 8 = of_bl (drop 24 (to_bl ip))"
      by(simp add: Word_Lemmas.of_drop_to_bl size_ipv4addr)
    have List_rev_drop_geqn: "length x \<ge> n \<Longrightarrow> (take n (rev x)) = rev (drop (length x - n) x)"
      for x :: "'a list" and n by(simp add: List.rev_drop)
    have and_mask_bl_take: "length x \<ge> n \<Longrightarrow> ((of_bl x) AND mask n) = (of_bl (rev (take n (rev (x)))))"
      for x n by(simp add: List_rev_drop_geqn of_bl_drop)
    have ipv4addr_and_255: "x AND 255 = x AND mask 8" for x :: ipv4addr
      by(simp add: mask_def)
    have bit_equality:
      "((ip >> 24) AND 0xFF << 24) + ((ip >> 16) AND 0xFF << 16) + ((ip >> 8) AND 0xFF << 8) + (ip AND 0xFF) =
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
      by(rename_tac blip,case_tac blip,simp_all)+ (*I'm so sorry for this ...*)
    have "ipv4addr_of_dotdecimal (dotdecimal_of_ipv4addr ip) = of_bl (to_bl ip)"
      apply(subst blip_split)
       apply(simp; fail)
      apply(simp add: ipv4addr_of_dotdecimal_bit dotdecimal_of_ipv4addr.simps)
      apply(simp add: ipv4addr_of_nat_nat_of_ipv4addr)
      apply(simp add: bit_equality)
      done
    thus ?thesis using Word.word_bl.Rep_inverse[symmetric] by simp
  qed

  lemma ipv4addr_of_dotdecimal_eqE:
    "\<lbrakk> ipv4addr_of_dotdecimal (a,b,c,d) = ipv4addr_of_dotdecimal (e,f,g,h);
       a < 256; b < 256; c < 256; d < 256; e < 256; f < 256; g < 256; h < 256 \<rbrakk> \<Longrightarrow>
         a = e \<and> b = f \<and> c = g \<and> d = h"
     by (metis Pair_inject dotdecimal_of_ipv4addr_ipv4addr_of_dotdecimal)

subsection\<open>IP Ranges: Examples\<close>
  lemma "(UNIV :: ipv4addr set) = {0 .. max_ipv4_addr}" by(simp add: UNIV_ipv4addrset)
  lemma "(42::ipv4addr) \<in> UNIV" by(simp)

  (*Warning, not executable!*)

  lemma "ipset_from_netmask (ipv4addr_of_dotdecimal (192,168,0,42)) (ipv4addr_of_dotdecimal (255,255,0,0)) =
          {ipv4addr_of_dotdecimal (192,168,0,0) .. ipv4addr_of_dotdecimal (192,168,255,255)}"
   by(simp add: ipset_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)

  lemma "ipset_from_netmask (ipv4addr_of_dotdecimal (192,168,0,42)) (ipv4addr_of_dotdecimal (0,0,0,0)) = UNIV"
    by(simp add: UNIV_ipv4addrset ipset_from_netmask_def ipv4addr_of_dotdecimal.simps
                 ipv4addr_of_nat_def max_ipv4_addr_max_word)
  
  text\<open>192.168.0.0/24\<close>

  lemma fixes addr :: ipv4addr
    shows "ipset_from_cidr addr pflength =
            ipset_from_netmask addr ((mask pflength) << (32 - pflength))"
    by(simp add: ipset_from_cidr_def)

  lemma "ipset_from_cidr (ipv4addr_of_dotdecimal (192,168,0,42)) 16 = 
          {ipv4addr_of_dotdecimal (192,168,0,0) .. ipv4addr_of_dotdecimal (192,168,255,255)}"
   by(simp add: ipset_from_cidr_alt mask_def  ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)

  lemma "ip \<in> (ipset_from_cidr (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 0)"
    by(simp add: ipset_from_cidr_0)

  lemma ipv4set_from_cidr_32: fixes addr :: ipv4addr
    shows "ipset_from_cidr addr 32 = {addr}"
    by(simp add: ipset_from_cidr_alt mask_def)

  lemma  fixes pre :: ipv4addr
    shows "ipset_from_cidr pre len = {(pre AND ((mask len) << (32 - len))) .. pre OR (mask (32 - len))}"
    by (simp add: ipset_from_cidr_alt ipset_from_cidr_def)

  text\<open>making element check executable\<close>
  lemma addr_in_ipv4set_from_netmask_code[code_unfold]: 
    fixes addr :: ipv4addr
    shows "addr \<in> (ipset_from_netmask base netmask) \<longleftrightarrow>
            (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by (simp add: addr_in_ipset_from_netmask_code)
  lemma addr_in_ipv4set_from_cidr_code[code_unfold]: 
    fixes addr :: ipv4addr
    shows "addr \<in> (ipset_from_cidr pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> pre OR (mask (32 - len))"
    by(simp add: addr_in_ipset_from_cidr_code)

  (*small numbers because we didn't load Code_Target_Nat. Should work by eval*)
  lemma "ipv4addr_of_dotdecimal (192,168,42,8) \<in> (ipset_from_cidr (ipv4addr_of_dotdecimal (192,168,0,0)) 16)"
    by(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipset_from_cidr_def
                    ipset_from_netmask_def mask_def)

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
