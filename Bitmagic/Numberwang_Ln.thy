theory Numberwang_Ln
imports NumberWangCebewee
begin

lemma ipv4range_bitmask_intersect: " \<not> ipv4range_set_from_bitmask b2 m2 \<subseteq> ipv4range_set_from_bitmask b1 m1 \<Longrightarrow>
       \<not> ipv4range_set_from_bitmask b1 m1 \<subseteq> ipv4range_set_from_bitmask b2 m2 \<Longrightarrow>
       ipv4range_set_from_bitmask b1 m1 \<inter> ipv4range_set_from_bitmask b2 m2 = {}"
apply(simp add: ipv4range_set_from_bitmask_eq_ip_set)
using ip_set_notsubset_empty_inter 
by presburger


lemma List_rev_drop_geqn: "length x \<ge> n \<Longrightarrow> (take n (rev x)) = rev (drop (length x - n) x)"
by(simp add: List.rev_drop)

lemma help4: "length x \<ge> n \<Longrightarrow> ((of_bl x) AND mask n) = (of_bl (rev (take n (rev (x)))))"
apply(simp add: List_rev_drop_geqn)
apply(simp add: WordLib.of_bl_drop)
done

(*TODO: move*)
lemma help1: "word_of_int (uint a mod 256) = a mod (256::ipv4addr)"
by(simp add: word_mod_def)
lemma help2: "nat_of_ipv4addr ((ip::ipv4addr) AND mask 8) = (nat_of_ipv4addr ip) mod 256"
  apply(simp add: nat_of_ipv4addr_def)
  apply(simp add: and_mask_mod_2p)
  apply(simp add: help1)
  apply(simp add: unat_mod)
  done
lemma help3: "(nat_of_ipv4addr ip mod 256) = (nat_of_ipv4addr (ip mod 256))"
  by(simp add: nat_of_ipv4addr_def unat_mod)

lemma ip_shiftr_div_consts: "(ip::ipv4addr) >> 24 = ip div (2^24)"
      "(ip::ipv4addr) >> 16 = ip div (2^16)"
      "(ip::ipv4addr) >> 8 = ip div (2^8)"
by(subst Word.word_uint_eq_iff, simp add: shiftr_div_2n uint_div)+

lemma blip_split: "length blip = 32 \<Longrightarrow> blip = (take 8 blip) @ (take 8 (drop 8 blip)) @ (take 8 (drop 16 blip)) @ (take 8 (drop 24 blip))"
apply(case_tac blip)
apply(simp_all)
apply(thin_tac "blip = ?x",rename_tac blip,case_tac blip,simp_all)+ (*I'm so sorry for this ...*)
done

lemma ip_and_mask8_bl_drop24: "(ip::ipv4addr) AND mask 8 = of_bl (drop 24 (to_bl ip))"
by(simp add: WordLemmaBucket.of_drop_to_bl size_ipv4addr)

lemma ipv4addr_of_dotteddecimal_dotteddecimal_of_ipv4addr: 
  "(ipv4addr_of_dotteddecimal (dotteddecimal_of_ipv4addr ip)) = ip"
apply(simp add: ipv4addr_of_dotteddecimal_bit dotteddecimal_of_ipv4addr.simps)
apply(simp add: ipv4addr_of_nat_nat_of_ipv4addr)
apply(simp add: ipv4addr_and_255)
apply(simp add: shiftr_slice)
apply(simp add: Word.slice_take' size_ipv4addr)
apply(simp add: help4)
apply(subgoal_tac "length (to_bl ip) = 32") prefer 2
 apply(simp)
apply(simp add: List_rev_drop_geqn)
apply(simp add: drop_take)
apply(subst(16) Word.word_bl.Rep_inverse[symmetric]) --"final  = ip"
apply(subst(9) blip_split)
apply(simp)
apply(simp add: Word.shiftl_of_bl)
apply(simp add: of_bl_append)
apply(simp add: ip_and_mask8_bl_drop24)
done



end
