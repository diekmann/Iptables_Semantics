theory IPv6Bitmagic
imports IPv6Addr
begin

  lemma "word_of_int (uint ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)))))  = 
          ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))"
    apply(subst word_of_int_uint)
    ..

  (*I could also use word_split to extract bits?*)
  
  lemma fixes ip::ipv6addr
    shows  "((ip >> 112) && mask 16) = (ip >> 112)"
    proof -
      have "size ip = 128" by( simp add: word_size)
      with WordLemmaBucket.shiftr_mask_eq[of ip 112] show ?thesis by simp
    qed
    
  lemma "of_bl (to_bl x) = x" by simp
 
  value "(slice 112 (0xFFFF0000000000000000000000000000::ipv6addr))::16 word"
  thm slice_shiftr

  lemma "xx && ~~ mask y >> y = ( (xx && (~~ (mask y))) >> y  )" by simp

  (*fun story: sledgehammer does not find this one!*)
  lemma mask_16_shiftl112_128word: "((mask 16 << 112)::128 word) = ~~ mask 112"
    by(simp add: mask_def)

  lemma word128_mask112: "(0xFFFF0000000000000000000000000000::ipv6addr) = (mask 16) << 112"
    by(simp add: mask_def)

  lemma
    fixes ip::ipv6addr
    shows "(ip AND 0xFFFF0000000000000000000000000000 >> 112) = slice 112 ip"
    apply(subst Word.shiftr_slice[symmetric])
    apply(subst word128_mask112)
    apply(subst mask_16_shiftl112_128word)
    apply(subst WordLemmaBucket.mask_shift)
    apply simp
    done

  lemma helpx16: 
    fixes w::"16 word"
    shows "uint ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl w)) = uint w"
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp)
    apply(simp)
    done

  lemma helpx128:
    fixes w::"128 word"
    shows "length (to_bl w) \<le> 16 \<Longrightarrow> 
           uint ((of_bl:: bool list \<Rightarrow> 16 word) (to_bl (w))) = 
           uint w "
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp)
    apply(simp)
    done

  lemma uint_bl_less_length: "uint (of_bl ls) < 2 ^ length ls"
    by (metis bintrunc_bintrunc_min bl_to_bin_lt2p lt2p_lem min_def of_bl_def trunc_bl2bin_len word_ubin.inverse_norm)

  lemma "to_bl (of_bl (False # ls)) = to_bl (of_bl ls)" oops

  value "to_bl ((of_bl [False])::ipv6addr)"
  lemma "n \<le> 16 \<Longrightarrow> length (to_bl (of_bl (take n ls))) \<le> 16"
    apply(simp)
    oops

(*copy of lemma (*uint_of_bl_is_bl_to_bin: l4v WordLib*)
  "length l\<le>len_of TYPE('a) \<Longrightarrow>
   uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans, rule bl_to_bin_lt2p)
  apply (rule order_trans, erule power_increasing)
   apply simp_all
  done*)


(*TODO: add to l4v bl_to_bin_lt2p*)
thm Bool_List_Representation.bl_to_bin_lt2p
lemma bl_to_bin_lt2p_Not: "bl_to_bin bs < (2 ^ length (dropWhile Not bs))"
  apply (unfold bl_to_bin_def)
  apply(induction bs)
   apply(simp)
  apply(simp)
  by (metis bl_to_bin_lt2p_aux one_add_one)

(*TODO: add to l4v uint_of_bl_is_bl_to_bin*)
thm WordLib.uint_of_bl_is_bl_to_bin
lemma uint_of_bl_is_bl_to_bin_Not:
  "length (dropWhile Not l) \<le> len_of TYPE('a) \<Longrightarrow>
   uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans)
  apply (rule bl_to_bin_lt2p_Not)
  apply(simp)
  done


lemma length_takeWhile_Not_replicate_False:
  "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
  by (metis in_set_replicate length_append length_replicate takeWhile_append2)


lemma length_dropWhile_Not_bl: "length (dropWhile Not (to_bl (of_bl bs))) \<le> length bs"
 apply(subst Word.word_rep_drop)
 apply(subst List.dropWhile_eq_drop)
 apply(simp)
 apply(subst length_takeWhile_Not_replicate_False)
 apply(simp)
 done
 
thm Word.word_bl_Rep'
  

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
    apply(subst uint_of_bl_is_bl_to_bin_Not)
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

  lemma bl_length_dropNot_twice: 
        "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs)))) =
         length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs)))"
    by(simp add: bl_drop_leading_zeros)

  lemma bl_length_dropNot_bound: "length (dropWhile Not bs) \<le> n \<Longrightarrow>
    length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))) \<le> n"
    thm length_dropWhile_Not_bl
    thm length_dropWhile_Not_bl[of "(dropWhile Not bs)"]
    apply(subgoal_tac "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs)))) \<le> n")
     prefer 2
     apply(rule order.trans)
      apply(rule length_dropWhile_Not_bl[of "(dropWhile Not bs)"])
     apply blast
    apply(rule order.trans)
     prefer 2
     apply(simp; fail)
    apply(rule order.trans)
     prefer 2
     thm length_dropWhile_Not_bl[of "(dropWhile Not bs)"]
     apply(rule length_dropWhile_Not_bl[of "(dropWhile Not bs)"])
    apply(subst bl_length_dropNot_twice)
    (*This is where I left off*)
    apply fastforce
    done

  (*this one should be even more generic*)
  lemma bl_cast_long_short_long_ingoreLeadingZero_generic:
  "length (dropWhile Not (to_bl w)) \<le> len_of TYPE('s) \<Longrightarrow>
   len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    (of_bl:: bool list \<Rightarrow> 'l::len word) (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) 
            (to_bl w))) = w"
    apply(rule Word.word_uint_eqI)
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp; fail)
    apply(subst Word.to_bl_bin)
    apply(subst uint_of_bl_is_bl_to_bin_Not)
     apply blast
    apply(simp)
    done

  lemma bl_cast_long_short_long_ingoreLeadingZero: 
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

  (*TODO: add to l4v*)
  (*taking only the high-order bits from a bitlist, casting to a longer word and casting back to
    a shorter type, casting to to longer type again is equal to just taking the bits and casting to
    the longer type.
    'l is the longer word. E.g. 128 bit
    's is the shorter word. E.g. 16 bit
  *)
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
    qed(simp)
    

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


  lemma and_mask_shift_helper:
    fixes ip::"'a::len word"
    shows "ip AND (mask m << n) >> n << n = ip AND (mask m << n)"
     proof - (*sledgehammered for 128 word and concrete values for m and n*)
       have f1: "\<And>w wa wb. ((w::'a::len word) && wa) && wb = w && wb && wa"
         by (simp add: word_bool_alg.conj_left_commute word_bw_comms(1))
       have "\<And>w n wa. ((w::'a::len word) && ~~ mask n) && (wa << n) = (w >> n) && wa << n"
         by (simp add: and_not_mask shiftl_over_and_dist)
       then show "ip && (mask m << n) >> n << n = ip && (mask m << n)"
         using f1 by (metis (no_types) and_not_mask word_and_mask_shiftl word_bw_comms(1))
     qed


  lemma ucast16_ucast128_masks_highest_bits112:
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask112)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done

    (*old working proof:
    apply(subst word128_mask112)
    apply(subst mask_16_shiftl112_128word)
    apply(subst WordLemmaBucket.mask_shift)
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_bl)
    apply(simp)
    apply(subst word128_mask112)+
    apply(subst WordLemmaBucket.word_and_mask_shiftl)+
    apply(subst xxx)+
    apply(subst Word.shiftr_bl)
    apply(subst Word.shiftl_bl)
    apply simp
    apply(subst Word.of_bl_append)+
    apply simp
    apply(subst Word.shiftr_bl)
    apply(simp)
    thm yaaaaaaaaaaaaaaaayaiohhgoo
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    done*)


  lemma word128_mask96: "(0xFFFF000000000000000000000000::ipv6addr) = (mask 16) << 96"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits96:
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000000000000000 >> 96)) << 96) =
         ip AND 0xFFFF000000000000000000000000"
    apply(subst word128_mask96)
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask96)+
    thm bl_cast_long_short_long_ingoreLeadingZero_generic
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done


  lemma word128_mask80: "(0xFFFF00000000000000000000::ipv6addr) = (mask 16) << 80"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits80: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF00000000000000000000 >> 80)) << 80) =
         ip AND 0xFFFF00000000000000000000"
    apply(subst word128_mask80)
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask80)+
    thm bl_cast_long_short_long_ingoreLeadingZero_generic
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done


  lemma word128_mask64: "(0xFFFF0000000000000000::ipv6addr) = (mask 16) << 64"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits64: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000 >> 64)) << 64) =
         ip AND 0xFFFF0000000000000000"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask64)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done
    

  lemma word128_mask48: "(0xFFFF000000000000::ipv6addr) = (mask 16) << 48"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits48: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000 >> 48)) << 48) =
         ip AND 0xFFFF000000000000"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask48)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done


  lemma word128_mask32: "(0xFFFF00000000::ipv6addr) = (mask 16) << 32"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits32: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF00000000 >> 32)) << 32) =
         ip AND 0xFFFF00000000"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask32)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done
    



  lemma word128_mask16: "(0xFFFF0000::ipv6addr) = (mask 16) << 16"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits16: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000 >> 16)) << 16) =
         ip AND 0xFFFF0000"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask16)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
     apply(rule length_dropNot_mask_inner)
      apply(simp_all)
    apply(simp add: and_mask_shift_helper)
    done



  lemma word128_mask0: "(0xFFFF::ipv6addr) = (mask 16)"
    by(simp add: mask_def)

  lemma ucast16_ucast128_masks_highest_bits0: 
    fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF))) =
         ip AND 0xFFFF"
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask0)+
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
    by (simp add: length_dropNot_mask)


 lemma Word_ucast_bl_16_128:
  "(ucast::16 word \<Rightarrow> ipv6addr) ((ucast::ipv6addr \<Rightarrow> 16 word) ip) =
   (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl:: bool list \<Rightarrow> 16 word) ((to_bl:: 128 word \<Rightarrow> bool list) ip)))"
    apply(subst Word.ucast_bl)+
    apply simp
    done

  lemma mask_len_word: fixes w::"'a::len word"
    shows "n = (len_of TYPE('a)) \<Longrightarrow> w AND mask n = w"
    by (simp add: mask_eq_iff) 

  lemma m48help: "(mask 4 << 4) || mask 4 = mask 8" by(simp add: mask_def)

  lemma fixes w::"8 word"
    shows "(w AND (mask 4 << 4)) || (w AND mask 4) = w"
  apply (subst word_oa_dist)
  apply simp
  apply (subst word_oa_dist2)
  apply(subst m48help)
  apply(simp add: mask_len_word)
  done

  
  lemma mask128: "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 128"
    by(simp add: mask_def)

  lemma ipv6addr_16word_pieces_compose_or:
    fixes ip::"128 word"
    shows "ip && (mask 16 << 112) ||
           ip && (mask 16 << 96) ||
           ip && (mask 16 << 80) ||
           ip && (mask 16 << 64) ||
           ip && (mask 16 << 48) ||
           ip && (mask 16 << 32) ||
           ip && (mask 16 << 16) ||
           ip && mask 16 =
           ip"
  apply(subst word_ao_dist2[symmetric])+
  apply(simp add: mask_def)
  apply(subst mask128)
  apply(rule mask_len_word)
  apply simp
  done

  text{*Correctness: round trip property one*}
  lemma ipv6preferred_to_int_int_to_ipv6preferred:
  "ipv6preferred_to_int (int_to_ipv6preferred ip) = ip"
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    apply(simp add: ucast16_ucast128_masks_highest_bits112 ucast16_ucast128_masks_highest_bits96
                    ucast16_ucast128_masks_highest_bits80 ucast16_ucast128_masks_highest_bits64
                    ucast16_ucast128_masks_highest_bits48 ucast16_ucast128_masks_highest_bits32
                    ucast16_ucast128_masks_highest_bits16 ucast16_ucast128_masks_highest_bits0)
    apply(simp add: word128_mask112 word128_mask96 word128_mask80 word128_mask64 word128_mask48
                    word128_mask32 word128_mask16 word128_mask0)
    apply(rule ipv6addr_16word_pieces_compose_or)
    done


   lemma helper_masked_ucast:
     fixes b::"16 word"
     shows "((ucast:: 16 word \<Rightarrow> 128 word) b << 96) && (mask 16 << 112) = 0"
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_of_bl)
    apply(simp)
    apply(subst Word.of_bl_append)
    apply simp
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLib.shiftr_div_2n_w)
     apply(simp add: word_size; fail)
    apply(simp)
    apply(subst WordLemmaBucket.word_div_less)
     apply(simp_all)
    apply(subgoal_tac "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2^(len_of TYPE(16))")
     prefer 2
     apply(rule Word.of_bl_length_less)
     apply(simp_all)
    apply(rule Word.div_lt_mult)
     apply(simp; fail)
    apply(simp)
    done

  (*TODO: tune proof*)
  lemma power_2_16_nat: "(16::nat) \<le> n \<Longrightarrow> (65535::nat) < 2 ^ n"
  proof -
    assume a: "(16::nat) \<le> n"
    have power2_rule: "a \<le> b \<Longrightarrow> (2::nat)^a \<le> 2 ^ b" for a b by fastforce
    show ?thesis
     apply(subgoal_tac "65536 \<le> 2 ^ n")
      apply(subst Nat.less_eq_Suc_le)
      apply(simp; fail)
     apply(subgoal_tac "(65536::nat) = 2^16")
      prefer 2
      apply(simp; fail)
     using power2_rule a by presburger
   qed
    
  (*TODO: tune! ! ! !*)
  lemma xxx: "65536 = unat (65536::128 word)" by auto
  lemma mnhelper: fixes x::"128 word"
    shows "n + 16 \<le> m \<Longrightarrow> m < 128 \<Longrightarrow> x < 0x10000 \<Longrightarrow> 16 \<le> m - n \<Longrightarrow> x < 2 ^ (m - n)"
    thm word_le_nat_alt
    apply(subst word_less_nat_alt)
    apply(simp)
    apply(subgoal_tac "unat x < 2^16")
     prefer 2
     apply simp
     defer
    apply(rule_tac b=65535 in Orderings.order_class.order.strict_trans1)
     apply(simp_all)
     using power_2_16_nat apply blast
    apply(subst xxx)
    apply(rule Word.unat_mono)
    apply(simp)
    done

   (*n small, m large*)
   lemma helper_masked_ucast_generic:
     fixes b::"16 word"
     shows"n + 16 \<le> m \<Longrightarrow> m < 128 \<Longrightarrow> ((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << m) = 0"
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_of_bl)
    apply(subst Word.of_bl_append)
    apply simp
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLib.shiftr_div_2n_w)
     apply(simp add: word_size; fail)
    apply(subst WordLemmaBucket.word_div_less)
     apply(simp_all)
    apply(subgoal_tac "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2^(len_of TYPE(16))")
     prefer 2
     apply(rule Word.of_bl_length_less)
     apply(simp_all)
    apply(rule Word.div_lt_mult)
     apply(rule WordLemmaBucket.word_less_two_pow_divI)
     apply(simp_all)
     apply(subgoal_tac "m - n \<ge> 16")
      prefer 2
      apply(simp)
      apply(rule mnhelper, simp_all)
     apply(subst WordLib.p2_gt_0)
     apply(simp)
    done

   lemma helpx: "(2::nat) ^ 80 * ((2 ^ 16 mod 2 ^ 128 * n) mod 2 ^ 128) = 
    2 ^ 96 * (n mod 2 ^ 128)" 
    apply(simp)
    apply(subst Divides.semiring_div_class.mod_mult_left_eq)
    apply simp
    oops
   lemma  "a = b \<Longrightarrow> a mod x = b mod x" by simp
   lemma "(a::nat) * (b * c) = (a * b) * c"
    by (fact Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(18))

   lemma power280helper: "(2::nat) ^ 80 = 2 ^ 80 mod 2 ^ len_of TYPE(128)" by auto
   lemma "w < c \<Longrightarrow> b * w < c \<Longrightarrow> 
    (a::nat) * (b * w mod c) = (a * b) * (w mod c)"
      apply(subst Word_Miscellaneous.nat_mod_eq')
       apply(simp)
      apply(subst Word_Miscellaneous.nat_mod_eq')
       apply simp_all
      done

   lemma  unat_of_bl_128_16_less_helper:
     fixes b::"16 word"
     shows "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^16"
   proof -
     from Word.word_bl_Rep' have 1: "length (to_bl b) = 16" by simp
     have "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^(length (to_bl b))"
       by(fact WordLemmaBucket.unat_of_bl_length)
     with 1 show ?thesis by auto
     qed
   lemma xxx: "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl (b::16 word))) < 4294967296"
     apply(rule order_less_trans)
     apply(rule unat_of_bl_128_16_less_helper)
     apply simp
     done

   (*reverse*)
   lemma 
     fixes b::"16 word"
     shows "((ucast:: 16 word \<Rightarrow> 128 word) b << 96) && (mask 16 << 80) = 0"
    apply(subst Word.ucast_bl)+

    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    thm WordLemmaBucket.rshift_sub_mask_eq
    apply(subst WordLemmaBucket.aligned_shiftr_mask_shiftl)
     apply(simp_all)
    unfolding is_aligned_def
    unfolding dvd_def
    apply(subst Word.shiftl_t2n)
    thm Word.shiftl_t2n Bool_List_Representation.shiftl_int_def
    apply(subst Word.unat_word_ariths(2))
    apply(rule_tac x="2^16 * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ len_of TYPE(128)" in exI)

    apply(subst Word_Miscellaneous.nat_mod_eq')
     apply(simp)
     apply(subst xxx)
     apply simp
     
     defer
    apply(subst Word_Miscellaneous.nat_mod_eq')
     apply(simp)
     defer
    apply simp
    (*TODO: continue here, the two subgoals should be obvous, once i can find the type*)
    

    (*apply(subst power280helper)
    thm Divides.semiring_div_class.mod_mult_left_eq[symmetric]
    apply(subst Divides.semiring_div_class.mod_mult_left_eq)
    apply(subst Divides.semiring_div_class.mod_mult_left_eq) back*)
    apply simp
    apply(subst Divides.semiring_div_class.mod_mult_left_eq) back
    
    
    
    

    (*
    thm WordLib.word_plus_and_or_coroll WordLemmaBucket.shiftl_mask_is_0 WordLemmaBucket.limited_and_eq_0
    thm word_bw_assocs word_bw_comms word_bw_lcs
    apply(rule_tac z="(of_bl (to_bl b) << 80)" in WordLemmaBucket.limited_and_eq_0)
    apply(simp_all add: limited_and_def max_word_def)
    *)

    apply(subst Word.shiftl_of_bl)
    apply(subst Word.of_bl_append)
    apply simp
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLib.shiftr_div_2n_w)
     apply(simp add: word_size; fail)

    thm WordLemmaBucket.word_div_less
    apply(subst WordLemmaBucket.word_div_less)
     apply(simp_all)
    apply(subgoal_tac "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2^(len_of TYPE(16))")
     prefer 2
     apply(rule Word.of_bl_length_less)
     apply(simp_all)
    apply(rule Word.div_lt_mult)
     apply(rule WordLemmaBucket.word_less_two_pow_divI)
     apply(simp_all)
     apply(subgoal_tac "m - n \<ge> 16")
      prefer 2
      apply(simp)
      apply(rule mnhelper, simp_all)
     apply(subst WordLib.p2_gt_0)
     apply(simp)
    done

  (*TODO: round trip property two*)
  lemma "int_to_ipv6preferred (ipv6preferred_to_int ip) = ip"
    apply(cases ip, rename_tac a b c d e f g h)
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    apply(simp add: word128_mask112 word128_mask96 word128_mask80 word128_mask64 word128_mask48
                    word128_mask32 word128_mask16 word128_mask0)
    apply(intro conjI)
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    defer
    apply(subst word_ao_dist)+
    apply(simp add: helper_masked_ucast_generic)
    oops


end