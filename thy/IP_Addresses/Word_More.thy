theory Word_More
imports Main
  "~~/src/HOL/Word/Word"
  "../Word_Lib/Word_Lemmas"
begin

section\<open>Helper Lemmas about Machine Words\<close>

  (*usually: x,y = (len_of TYPE ('a)) i.e. 32 for ipv4addr*)
  lemma bitmagic_zeroLast_leq_or1Last:
    "(a::('a::len) word) AND (mask len << x - len) \<le> a OR mask (y - len)"
    by (meson le_word_or2 order_trans word_and_le2)


  lemma zero_base_lsb_imp_set_eq_as_bit_operation:
    fixes base ::"'a::len word"
    assumes valid_prefix: "mask (len_of TYPE('a) - len) AND base = 0"
    shows "(base = NOT mask (len_of TYPE('a) - len) AND a) \<longleftrightarrow>
           (a \<in> {base .. base OR mask (len_of TYPE('a) - len)})"
  proof
    have helper3: "x OR y = x OR y AND NOT x" for x y ::"'a::len word" by (simp add: word_oa_dist2)
    from assms show "base = NOT mask (len_of TYPE('a) - len) AND a \<Longrightarrow>
                      a \<in> {base..base OR mask (len_of TYPE('a) - len)}"
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
      hence f5: "\<forall>x\<^sub>6. (base OR x\<^sub>6) AND NOT mask (len_of TYPE('a) - len) =
                        base OR x\<^sub>6 AND NOT mask (len_of TYPE('a) - len)"
        using word_ao_dist by (metis)
      have f6: "\<forall>x\<^sub>2 x\<^sub>3. a AND NOT mask x\<^sub>2 \<le> x\<^sub>3 \<or>
                        \<not> (base OR mask (len_of TYPE('a) - len)) AND NOT mask x\<^sub>2 \<le> x\<^sub>3"
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
