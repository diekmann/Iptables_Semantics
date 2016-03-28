theory NumberWang
imports Main
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Word/WordBitwise"
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




(*maybe the ugliest proof I can imagine*)
lemma size_mask_32word: "n < 32 ==> n < size ((mask x)::32 word)" by(simp add:word_size)
lemma NOT_mask_len32: "NOT ((mask len << (32 - len))::32 word) = (mask (32 - len))"
  thm Divides.semiring_div_class.mod_mult_self1_is_0[of "2 ^ (32 - len)" "(2 ^ len - 1)"]
  proof(rule Word.word_bool_alg.compl_unique)
  from Divides.semiring_div_class.mod_mult_self1_is_0[of "(2 ^ (32 - len))" "uint ((2::32 word) ^ len - 1)"]
  have mod0: "uint ((2::32 word) ^ (32 - len) * ((2::32 word) ^ len - (1::32 word))) mod 2 ^ (32 - len) = 0" (is ?mod0)
    proof(cases "len = 0")
      case True thus ?mod0 by simp
      next
      case False
        have "uint (max_word::32 word) < 4294967296" by(simp add: max_word_def)
        from False have simp1: "uint ((2::32 word) ^ (32 - len) * ((2::32 word) ^ len - 1)) = 
            uint ((2::32 word) ^ (32 - len)) * uint ((2::32 word) ^ len - 1) mod 2^32"
          by(simp add: Word.uint_word_ariths)
        have "(2::32 word) ^ (32 - len) = word_of_int ((2::int) ^ (32 - len))" by (metis word_of_int_2p)
        from False this have simp2: "uint ((2::32 word) ^ (32 - len)) = 2 ^ (32 - len)"
          apply(simp only: uint_word_of_int)
          apply(subst mod_pos_pos_trivial)
          apply(simp)
          apply(rule Power.linordered_semidom_class.power_strict_increasing)
           apply(simp_all)
          done
        show ?mod0
          apply(subst simp1)
          apply(subst Divides.semiring_div_class.mod_mod_cancel)
          apply (metis diff_le_self dvd_power_le dvd_refl)
          apply(simp add: simp2)
          done
    qed
  show "((mask len << 32 - len)::32 word) AND mask (32 - len) = 0"
    apply(simp only: and_mask_mod_2p)
    apply(simp add: shiftl_t2n)
    apply(simp add: mask_def)
    apply(subst mod0)
    apply simp
    done
  
  show "((mask len << 32 - len)::32 word) OR mask (32 - len) = max_word"
    apply word_bitwise
    (*3/8's proof 2*)
    apply (subgoal_tac "len > 32 \<or> len \<in> set (map nat (upto 0 32))")
    apply (simp add: upto_code upto_aux_rec, elim disjE)
    apply (simp add: size_mask_32word)
    apply (simp_all add: size_mask_32word) [33]
    apply (simp add: upto_code upto_aux_rec, presburger)
    done
    (*3/8's proof 1*)
    (*apply (subgoal_tac "len > 32 \<or> len \<in> {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
                                          22,23,24,25,26,27,28,29,30,31,32}")
    apply (simp only: insert_iff, elim disjE)
    apply (simp add: size_mask_32word)
    apply (simp_all add: size_mask_32word) [34]
    apply (simp only: insert_iff empty_iff HOL.simp_thms, presburger)
    done*)
    (*apply word_bitwise
    apply simp
    (*beware!!!*)
    apply(case_tac "len = 0",simp add: size_mask_32word)
    apply(case_tac "len = 1", simp add: size_mask_32word)
    apply(case_tac "len = 2", simp add: size_mask_32word)
    apply(case_tac "len = 3", simp add: size_mask_32word)
    apply(case_tac "len = 4", simp add: size_mask_32word)
    apply(case_tac "len = 5", simp add: size_mask_32word)
    apply(case_tac "len = 6", simp add: size_mask_32word)
    apply(case_tac "len = 7", simp add: size_mask_32word)
    apply(case_tac "len = 8", simp add: size_mask_32word)
    apply(case_tac "len = 9", simp add: size_mask_32word)
    apply(case_tac "len = 10", simp add: size_mask_32word)
    apply(case_tac "len = 11", simp add: size_mask_32word)
    apply(case_tac "len = 12", simp add: size_mask_32word)
    apply(case_tac "len = 13", simp add: size_mask_32word)
    apply(case_tac "len = 14", simp add: size_mask_32word)
    apply(case_tac "len = 15", simp add: size_mask_32word)
    apply(case_tac "len = 16", simp add: size_mask_32word)
    apply(case_tac "len = 17", simp add: size_mask_32word)
    apply(case_tac "len = 18", simp add: size_mask_32word)
    apply(case_tac "len = 19", simp add: size_mask_32word)
    apply(case_tac "len = 20", simp add: size_mask_32word)
    apply(case_tac "len = 21", simp add: size_mask_32word)
    apply(case_tac "len = 22", simp add: size_mask_32word)
    apply(case_tac "len = 23", simp add: size_mask_32word)
    apply(case_tac "len = 24", simp add: size_mask_32word)
    apply(case_tac "len = 25", simp add: size_mask_32word)
    apply(case_tac "len = 26", simp add: size_mask_32word)
    apply(case_tac "len = 27", simp add: size_mask_32word)
    apply(case_tac "len = 28", simp add: size_mask_32word)
    apply(case_tac "len = 29", simp add: size_mask_32word)
    apply(case_tac "len = 30", simp add: size_mask_32word)
    apply(case_tac "len = 31", simp add: size_mask_32word)
    apply(case_tac "len = 32", simp add: size_mask_32word)
    apply(case_tac "len > 32", simp add: size_mask_32word)
    by presburger*)
  qed




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
  (*
      apply word_bitwise
      apply (subgoal_tac "len > 32 \<or> len \<in> set (map nat (upto 0 32))")
      apply (simp add: upto_code upto_aux_rec, elim disjE)
      apply (simp add: size_mask_32word rev_bl_order_simps)
      apply (simp_all add: size_mask_32word rev_bl_order_simps) [33]
      apply (simp add: upto_code upto_aux_rec, presburger)
  done*)
end
