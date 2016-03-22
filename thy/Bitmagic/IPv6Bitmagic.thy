theory IPv6Bitmagic
imports 
  (*NumberWang*)
  (*WordInterval_Lists*)
  "./l4v/lib/WordLemmaBucket"
begin

(*
  lemma uint_bl_less_length: "uint (of_bl ls) < 2 ^ length ls"
    by (metis bintrunc_bintrunc_min bl_to_bin_lt2p lt2p_lem min_def of_bl_def trunc_bl2bin_len word_ubin.inverse_norm)
*)

(*TODO: add to l4v bl_to_bin_lt2p*)
thm Bool_List_Representation.bl_to_bin_lt2p
lemma bl_to_bin_lt2p_dropNot: "bl_to_bin bs < 2 ^ length (dropWhile Not bs)"
  unfolding bl_to_bin_def
  proof(induction bs)
  case(Cons b bs)
    with bl_to_bin_lt2p_aux[where w=1] show ?case by simp
  qed(simp)

(*TODO: add to l4v uint_of_bl_is_bl_to_bin*)
thm WordLib.uint_of_bl_is_bl_to_bin
lemma uint_of_bl_is_bl_to_bin_dropNot:
  "length (dropWhile Not l) \<le> len_of TYPE('a) \<Longrightarrow>
   uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans)
  apply (rule bl_to_bin_lt2p_dropNot)
  apply(simp)
  done


lemma length_takeWhile_Not_replicate_False:
  "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
  by(subst takeWhile_append2) simp+


lemma length_dropNot_bl: "length (dropWhile Not (to_bl (of_bl bs))) \<le> length bs"
 apply(subst Word.word_rep_drop)
 apply(subst List.dropWhile_eq_drop)
 apply(simp)
 apply(subst length_takeWhile_Not_replicate_False)
 apply(simp)
 done
  

  lemma 
  "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'l::len word) ls))) \<le> len_of TYPE('s) \<Longrightarrow>
   len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) 
            (to_bl ((of_bl:: bool list \<Rightarrow> 'l::len word) ls)))) =
    (of_bl:: bool list \<Rightarrow> 'l::len word) ls"
    apply(rule Word.word_uint_eqI)
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp; fail)
    apply(subst Word.to_bl_bin)
    apply(subst uint_of_bl_is_bl_to_bin_dropNot)
     apply assumption
     (*using[[unify_trace_failure]]
       apply assumption*)
    apply(simp)
    done

  lemma "length (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs))) = 
         length (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))"
    apply(fact Word.word_rotate.lbl_lbl)
    done

  (*TODO: push this somewhere! maybe to isabelle main word thy!*)
  lemma bl_drop_leading_zeros: 
        "(of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs) =
         (of_bl:: bool list \<Rightarrow> 'a::len word) bs"
  by(induction bs) simp_all


  lemma bl_length_dropNot_bound: assumes "length (dropWhile Not bs) \<le> n"
    shows "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))) \<le> n"
  proof -
    have bl_length_dropNot_twice: 
        "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs)))) =
         length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs)))"
      by(simp add: bl_drop_leading_zeros)
    from length_dropNot_bl
    have *: "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))) \<le> length (dropWhile Not bs)"
     apply(rule dual_order.trans)
     apply(subst bl_length_dropNot_twice)
     ..
    show ?thesis
    apply(rule order.trans, rule *)
    using assms by(simp)
  qed

  (*TODO: add to l4v*)
  (* casting a long word to a shorter word and casting back to the long word 
     is equal to the original long word -- if the word is small enough.
    'l is the longer word.
    's is the shorter word.
  *)
  lemma bl_cast_long_short_long_ingoreLeadingZero_generic:
  "length (dropWhile Not (to_bl w)) \<le> len_of TYPE('s) \<Longrightarrow>
   len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    (of_bl:: bool list \<Rightarrow> 'l::len word) (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) (to_bl w))) = w"
    apply(rule Word.word_uint_eqI)
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp; fail)
    apply(subst Word.to_bl_bin)
    apply(subst uint_of_bl_is_bl_to_bin_dropNot)
     apply blast
    apply(simp)
    done

  (*
   Casting between longer and shorter word.
    'l is the longer word.
    's is the shorter word.
   For example: 'l::len word is 128 word (full ipv6 address)
                's::len word is 16 word (address piece of ipv6 address in colon-text-reprsenetation)
  *)
  corollary ucast_short_ucast_long_ingoreLeadingZero:
  "length (dropWhile Not (to_bl w)) \<le> len_of TYPE('s) \<Longrightarrow>
   len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    (ucast:: 's::len word \<Rightarrow> 'l::len word) ((ucast:: 'l::len word \<Rightarrow> 's::len word) w) = w"
    apply(subst Word.ucast_bl)+
    apply(rule bl_cast_long_short_long_ingoreLeadingZero_generic)
     apply(simp_all)
    done

  (*
  corollary bl_cast_long_short_long_ingoreLeadingZero: 
  "length (dropWhile Not ls) \<le> len_of TYPE('s) \<Longrightarrow>
   len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) 
            (to_bl ((of_bl:: bool list \<Rightarrow> 'l::len word) ls)))) =
    (of_bl:: bool list \<Rightarrow> 'l::len word) ls"
    apply(rule bl_cast_long_short_long_ingoreLeadingZero_generic)
     apply(rule bl_length_dropNot_bound)
     apply blast
    apply(simp)
    done
  *)

  (*
  corollary bl_cast_long_short_long_take:
  "n \<le> len_of TYPE('s) \<Longrightarrow> len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) 
            (to_bl ((of_bl:: bool list \<Rightarrow> 'l::len word) (take n ls))))) =
    (of_bl:: bool list \<Rightarrow> 'l::len word) (take n ls)"
    proof(rule bl_cast_long_short_long_ingoreLeadingZero, goal_cases)
    case 1 
      have "length (dropWhile Not (take n ls)) \<le> min (length ls) n"
        by (metis (no_types) length_dropWhile_le length_take)
      then show "length (dropWhile Not (take n ls)) \<le> len_of (TYPE('s)::'s itself)"
        using 1(1) by linarith
    qed(simp)*)
    

  (*TODO: to l4v!*)
  lemma length_dropNot_mask:
    fixes w::"'a::len word"
    shows "length (dropWhile Not (to_bl (w AND mask n))) \<le> n"
    apply(subst Word.bl_and_mask)
    by (simp add: List.dropWhile_eq_drop length_takeWhile_Not_replicate_False)

  
  (*TODO: move those two lemmas to l4? maybe they are too specific*)
  lemma length_dropNot_mask_outer: fixes ip::"'a::len word"
    shows "len_of TYPE('a) - n' = len \<Longrightarrow> length (dropWhile Not (to_bl (ip AND (mask n << n') >> n'))) \<le> len"
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLib.shiftl_shiftr1)
     apply(simp; fail)
    apply(simp)
    apply(subst WordLib.and_mask)
    apply(simp add: word_size)
    apply(simp add: length_dropNot_mask)
    done
  lemma length_dropNot_mask_inner: fixes ip::"'a::len word"
    shows "n \<le> len_of TYPE('a) - n' \<Longrightarrow> length (dropWhile Not (to_bl (ip AND (mask n << n') >> n'))) \<le> n"
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLemmaBucket.shiftl_shiftr3)
     apply(simp; fail)
    apply(simp)
    apply(simp add: word_size)
    apply(simp add: WordLemmaBucket.mask_twice)
    apply(simp add: length_dropNot_mask)
    done


(*
 lemma Word_ucast_bl_16_128:
  "(ucast::16 word \<Rightarrow> 128 word) ((ucast::ipv6addr \<Rightarrow> 16 word) ip) =
   (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl:: bool list \<Rightarrow> 16 word) ((to_bl:: 128 word \<Rightarrow> bool list) ip)))"
    apply(subst Word.ucast_bl)+
    apply simp
    done
*)

  lemma mask_len_word: fixes w::"'a::len word"
    shows "n = (len_of TYPE('a)) \<Longrightarrow> w AND mask n = w"
    by (simp add: mask_eq_iff) 
  

  lemma mask128: "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 128"
    by(simp add: mask_def)


(*-------------- things for ipv6 syntax round trip property two ------------------*)


  (*n small, m large*)
  lemma helper_masked_ucast_generic:
    fixes b::"16 word"
    assumes "n + 16 \<le> m" and "m < 128"
    shows "((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << m) = 0"
  proof -
    have "x < 2 ^ (m - n)" if mnh2: "x < 0x10000"
      for x::"128 word"
    proof -
      from assms(1) have mnh3: "16 \<le> m - n" by fastforce
      have power_2_16_nat: "(16::nat) \<le> n \<Longrightarrow> (65535::nat) < 2 ^ n" if a:"16 \<le> n"for n
      proof -
        have power2_rule: "a \<le> b \<Longrightarrow> (2::nat)^a \<le> 2 ^ b" for a b by fastforce
        show ?thesis
         apply(subgoal_tac "65536 \<le> 2 ^ n")
          apply(subst Nat.less_eq_Suc_le)
          apply(simp; fail)
         apply(subgoal_tac "(65536::nat) = 2^16")
          prefer 2
          apply(simp; fail)
         using power2_rule \<open>16 \<le> n\<close> by presburger
      qed
      have "65536 = unat (65536::128 word)" by auto
      moreover from mnh2 have "unat x <  unat (65536::128 word)" by(rule Word.unat_mono)
      ultimately have x: "unat x < 65536" by simp
      with mnh3 have "unat x < 2 ^ (m - n)" 
        apply(rule_tac b=65535 in Orderings.order_class.order.strict_trans1)
         apply(simp_all)
        using power_2_16_nat apply blast
        done
      with assms(2) show ?thesis by(subst word_less_nat_alt) simp
    qed
    hence mnhelper2: "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2 ^ (m - n)"
      apply(subgoal_tac "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2^(len_of TYPE(16))")
       prefer 2
       apply(rule Word.of_bl_length_less)
        apply(simp_all)
      done
    have mnhelper3: "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) * 2 ^ n < 2 ^ m"
      apply(rule Word.div_lt_mult)
       apply(rule WordLemmaBucket.word_less_two_pow_divI)
         using assms by(simp_all add: mnhelper2 WordLib.p2_gt_0)

    from assms show ?thesis
      apply(subst Word.ucast_bl)+
      apply(subst Word.shiftl_of_bl)
      apply(subst Word.of_bl_append)
      apply simp
      apply(subst WordLemmaBucket.word_and_mask_shiftl)
      apply(subst WordLib.shiftr_div_2n_w)
       subgoal by(simp add: word_size; fail)
      apply(subst WordLemmaBucket.word_div_less)
       subgoal by(rule mnhelper3)
      apply simp
      done
  qed


  lemma unat_of_bl_128_16_less_helper:
    fixes b::"16 word"
    shows "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^16"
  proof -
    from Word.word_bl_Rep' have 1: "length (to_bl b) = 16" by simp
    have "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^(length (to_bl b))"
      by(fact WordLemmaBucket.unat_of_bl_length)
    with 1 show ?thesis by auto
  qed
  lemma unat_of_bl_128_16_le_helper: "unat ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl (b::16 word))) \<le> 65535"
  proof -
    from unat_of_bl_128_16_less_helper[of b] have
      "unat ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl b)) < 65536" by simp 
    from Nat.Suc_leI[OF this] show ?thesis by simp
  qed


  (*reverse*)
   lemma helper_masked_ucast_reverse_generic:
     fixes b::"16 word"
     assumes "m + 16 \<le> n" and "n \<le> 128 - 16"
     shows "((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << m) = 0"
   proof -

     have power_less_128_helper: "2 ^ n * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2 ^ len_of TYPE(128)"
       if n: "n \<le> 128 - 16" for n
     proof -
       have help_mult: "n \<le> l \<Longrightarrow> 2 ^ n * x < 2 ^ l \<longleftrightarrow> x < 2 ^ (l - n)" for x::nat and l
         by (simp add: nat_mult_power_less_eq semiring_normalization_rules(7))
       from n show ?thesis
         apply(subst help_mult)
          subgoal by (simp)
         apply(rule order_less_le_trans)
          apply(rule unat_of_bl_128_16_less_helper)
         apply(rule Power.power_increasing)
          apply(simp_all)
         done
     qed

     have *: "2 ^ m * (2 ^ (n - m) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b))) = 
              2 ^ n * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b))"
     proof(cases "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) = 0")
     case True thus ?thesis by simp
     next
     case False
      have help_mult: "x \<noteq> 0 \<Longrightarrow> b * (c * x) = a * (x::nat)  \<longleftrightarrow> b * c = a" for x a b c by simp
      from assms show ?thesis
       apply(subst help_mult[OF False])
       apply(subst Power.monoid_mult_class.power_add[symmetric])
       apply(simp)
       done
     qed

    from assms have "unat ((2 ^ n)::128 word) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ len_of TYPE(128) =
          2 ^ m * (2 ^ (n - m) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ len_of TYPE(128))"
       apply(subst Word_Miscellaneous.nat_mod_eq')
        subgoal apply(subst Aligned.unat_power_lower)
         subgoal by(simp; fail)
        subgoal by (rule power_less_128_helper) simp
        done
       apply(subst Word_Miscellaneous.nat_mod_eq')
        subgoal by(rule power_less_128_helper) simp
       apply(subst Aligned.unat_power_lower)
        apply(simp; fail)
       apply(simp only: *)
       done
     hence ex_k: "\<exists>k. unat ((2 ^ n)::128 word) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ len_of TYPE(128) = 2 ^ m * k"
       by blast

     hence aligned: "is_aligned ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b) << n) m"
       unfolding is_aligned_def
       unfolding dvd_def
       unfolding Word.shiftl_t2n
       unfolding Word.unat_word_ariths(2)
       by assumption

     from assms have of_bl_to_bl_shift_mask: "((of_bl::bool list \<Rightarrow> 128 word) (to_bl b) << n) && mask (16 + m) = 0"
      using is_aligned_mask is_aligned_shiftl by force (*sledgehammer*)

     show ?thesis
      apply(subst Word.ucast_bl)+
      apply(subst WordLemmaBucket.word_and_mask_shiftl)
      apply(subst WordLemmaBucket.aligned_shiftr_mask_shiftl)
       subgoal by (fact aligned)
      subgoal by (fact of_bl_to_bl_shift_mask)
      done
  qed

(*
  lemma ucast16_mask16: "(ucast:: 16 word \<Rightarrow> 128 word) (mask 16) = mask 16"
  proof -
     have minus1: "((- 1):: 16 word) = 0xFFFF"
       by(simp)
     thus ?thesis
       apply(simp add: ucast_def)
       apply(simp add: mask_def minus1)
       done
   qed
*)

  lemma helper_masked_ucast_equal_generic:
    fixes b::"16 word"
    assumes "n \<le> 128 - 16"
    shows "ucast (((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << n) >> n) = b"
  proof -
   have ucast_mask: "(ucast:: 16 word \<Rightarrow> 128 word) b && mask 16 = ucast b" 
    apply(subst WordLib.and_mask_eq_iff_le_mask)
    apply(subst Word.ucast_bl)
    apply(simp add: mask_def)
    thm Word.word_uint_eqI word_le_nat_alt
    apply(subst word_le_nat_alt)
    apply(simp)
    using unat_of_bl_128_16_le_helper by simp

   from assms have "ucast (((ucast:: 16 word \<Rightarrow> 128 word) b && mask (128 - n) && mask 16) && mask (128 - n)) = b"
    apply(subst WordLemmaBucket.mask_and_mask)
    apply(simp)
    apply(subst Word.word_bool_alg.conj.assoc)
    apply(subst WordLemmaBucket.mask_and_mask)
    apply(simp)
    apply(simp add: ucast_mask WordLemmaBucket.ucast_ucast_mask)
    apply(subst Word.mask_eq_iff)
    apply(rule order_less_trans)
     apply(rule Word.uint_lt)
    apply(simp; fail)
    done
   
   thus ?thesis
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLemmaBucket.shiftl_shiftr3)
     apply(simp; fail)
    apply(simp)
    apply(subst WordLemmaBucket.shiftl_shiftr3)
     apply(simp; fail)
    apply(simp add: word_size)
    apply(subst Word.word_bool_alg.conj.assoc)
    apply assumption
    done
  qed
  



end