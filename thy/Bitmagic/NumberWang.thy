theory NumberWang
imports Main
  "~~/src/HOL/Word/Word"
  "./l4v/lib/WordLemmaBucket" (*will things break if I include this early?*)
begin


lemma pow2_mask: "((2^x) - 1) = mask x" by (metis mask_def shiftl_1)

lemma mod256: "((d::nat) + 256 * c + 65536 * b + 16777216 * a) mod 256 = d mod 256"
  proof -
  from mod_mult_self2[where a="d + 256 * c + 65536 * b" and b="256" and c="65536 * a"] have 
    "(d + 256 * c + 65536 * b + 256 * 65536 * a) mod 256 = (d + 256 * c + 65536 * b) mod 256" by simp
  also have "\<dots>  = (d + 256 * c) mod 256" using mod_mult_self2[where a="d + 256 * c" and b="256" and c="256 * b"] by simp
  also have "\<dots> = d mod 256" using mod_mult_self2 by blast
  finally show ?thesis by presburger
  qed

lemma div65536: assumes "a < 256" "b < 256" "c < 256" "d < 256" 
    shows "nat ((int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 mod 256) = b"
  proof -
  from zdiv_mult_self[where a="int d + int (256 * c) + int (65536 * b)" and m=65536 and n="256 * (int a)"] have
    "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 =
     ((int d + int (256 * c) + int (65536 * b)) div 65536) + 256 * int a" by linarith
  also from zdiv_mult_self[where a="int d + int (256 * c)" and m="65536" and n="int b"] have
    "\<dots> = (int d + int (256 * c)) div 65536 + int b + 256 * int a" by linarith
  also from assms have "\<dots> = int b + 256 * int a" by simp
  finally have helper: "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 65536 = int b + 256 * int a" .
  from assms show ?thesis
    unfolding helper
    apply(simp)
    apply(subst mod_pos_pos_trivial)
      apply simp_all
    done
  qed

  lemma div256: assumes "a < 256" "b < 256" "c < 256" "d < 256" 
    shows "nat ((int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 mod 256) = c"
  proof -
  from zdiv_mult_self[where a="int d + int (256 * c) + int (65536 * b)" and m=256 and n="65536 * (int a)"] have
    "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 =
     ((int d + int (256 * c) + int (65536 * b)) div 256) + 65536 * int a" by linarith
  also from zdiv_mult_self[where a="int d + int (256 * c)" and m="256" and n="256 * int b"] have
    "\<dots> = (int d + int (256 * c)) div 256 + 256 * int b + 65536 * int a" by linarith
  also from zdiv_mult_self[where a="int d" and m="256" and n="int c"] have
    "\<dots> = (int d) div 256 + int c + 256 * int b + 65536 * int a" by linarith
  also from assms have "\<dots> = int c + 256 * int b + 65536 * int a" by simp
  finally have helper1: "(int d + int (256 * c) + int (65536 * b) + int (16777216 * a)) div 256 = int c + 256 * int b + 65536 * int a" .
  
  from mod_mult_self2[where a="int c + 256 * int b" and c="256 * int a" and b=256] have 
    "(int c + 256 * int b + 65536 * int a) mod 256 = (int c + 256 * int b) mod 256" by simp
  also have "\<dots> = int c mod 256" using mod_mult_self2[where a="int c" and b=256 and c="int b"] by simp
  also have "\<dots> = int c" using assms
    apply(subst mod_pos_pos_trivial)
    by(simp_all)
  finally have helper2: "(int c + 256 * int b + 65536 * int a) mod 256 = int c" .
  
  from helper1 helper2 show ?thesis by simp
  qed




(*TODO: delete*)
lemma size_mask_32word: "n < 32 ==> n < size ((mask x)::32 word)" by(simp add:word_size)


  lemma word32_or_NOT4294967296: "(foo::32 word) OR -4294967296 = foo"
    proof -
      let ?null="-4294967296::32 word"
      have "?null = 0" by simp
      from this Word.word_bool_alg.disj_zero_right
      show "foo OR ?null = foo" by metis
    qed



  (*usually: x,y = (len_of TYPE ('a)) i.e. 32 for ipv4addr*)
  lemma bitmagic_zeroLast_leq_or1Last: "(a::('a::len) word) AND (mask len << x - len) \<le> a OR mask (y - len)"
    by (meson le_word_or2 order_trans word_and_le2)


  lemma zero_base_lsb_imp_set_eq_as_bit_operation:
    fixes base ::"'a::len word"
    assumes valid_prefix: "mask (len_of TYPE('a) - len) AND base = 0"
    shows "(base = NOT mask (len_of TYPE('a) - len) AND a) \<longleftrightarrow>
           (a \<in> {base .. base OR mask (len_of TYPE('a) - len)})"
  proof
    have helper3: "x OR y = x OR y AND NOT x" for x y ::"'a::len word" by (simp add: word_oa_dist2)
    from assms show "base = NOT mask (len_of TYPE('a) - len) AND a \<Longrightarrow> a \<in> {base..base OR mask (len_of TYPE('a) - len)}"
      apply(simp add: word_and_le1)
      apply(metis helper3 le_word_or2 word_bw_comms(1) word_bw_comms(2))
    done
  next
    assume "a \<in> {base..base OR mask (len_of TYPE('a) - len)}"
    hence a: "base \<le> a \<and> a \<le> base OR mask (len_of TYPE('a) - len)" by simp
    show "base = NOT mask (len_of TYPE('a) - len) AND a"
    proof -
      have f2: "\<forall>x\<^sub>0. base AND NOT mask x\<^sub>0 \<le> a AND NOT mask x\<^sub>0"
        using a neg_mask_mono_le by blast
      have f3: "\<forall>x\<^sub>0. a AND NOT mask x\<^sub>0 \<le> (base OR mask (len_of TYPE('a) - len)) AND NOT mask x\<^sub>0"
        using a neg_mask_mono_le by blast
      have f4: "base = base AND NOT mask (len_of TYPE('a) - len)"
        using valid_prefix by (metis mask_eq_0_eq_x word_bw_comms(1))
      hence f5: "\<forall>x\<^sub>6. (base OR x\<^sub>6) AND NOT mask (len_of TYPE('a) - len) = base OR x\<^sub>6 AND NOT mask (len_of TYPE('a) - len)"
        using word_ao_dist by (metis)
      have f6: "\<forall>x\<^sub>2 x\<^sub>3. a AND NOT mask x\<^sub>2 \<le> x\<^sub>3 \<or> \<not> (base OR mask (len_of TYPE('a) - len)) AND NOT mask x\<^sub>2 \<le> x\<^sub>3"
        using f3 dual_order.trans by auto
      have "base = (base OR mask (len_of TYPE('a) - len)) AND NOT mask (len_of TYPE('a) - len)"
        using f5 by auto
      hence "base = a AND NOT mask (len_of TYPE('a) - len)"
        using f2 f4 f6 by (metis eq_iff)
      thus "base = NOT mask (len_of TYPE('a) - len) AND a"
        by (metis word_bw_comms(1))
    qed
  qed
end
