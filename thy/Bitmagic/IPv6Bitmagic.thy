theory IPv6Bitmagic
imports IPv6Addr
begin

  lemma "word_of_int (uint ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)))))  = 
          ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))"
    apply(subst word_of_int_uint)
    ..

  lemma x: "(word_of_int:: int \<Rightarrow> 'b::len0 word) (uint ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))) << (112::nat) = 
          ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))  << 112"
    apply(subst word_of_int_uint)
    ..

  (*I could also use word_split to extract bits?*)
  
  lemma word128_mask112: "(0xFFFF0000000000000000000000000000::ipv6addr) = (mask 16) << 112"
    by(simp add: mask_def)
  lemma xxx: fixes ip::ipv6addr
    shows  "((ip >> 112) && mask 16) = (ip >> 112)"
    proof -
      have "size ip = 128" by( simp add: word_size)
      with WordLemmaBucket.shiftr_mask_eq[of ip 112] show ?thesis by simp
    qed
    
  lemma "of_bl (to_bl x) = x" by simp
 
  value "(slice 112 (0xFFFF0000000000000000000000000000::ipv6addr))::16 word"
  thm slice_shiftr

  lemma "of_bl (to_bl (of_bl (to_bl x))) = x"
  proof -
   have 1: "of_bl (to_bl x) = x"
    apply(subst Word.word_bl.Rep_inverse) ..
   show "of_bl (to_bl (of_bl (to_bl x))) = x"
    apply(subst 1)
  oops

  lemma "xx && ~~ mask y >> y = ( (xx && (~~ (mask y))) >> y  )" by simp

  (*fun story: sledgehammer does not find this one!*)
  lemma mask_16_shiftl112_128word: "((mask 16 << 112)::128 word) = ~~ mask 112"
    by(simp add: mask_def)

  lemma word128_and_slice112:
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
    
    (* old proof:
    apply(rule Word.word_uint_eqI)
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp; fail)
    apply(subst Word.to_bl_bin)
    apply(subst uint_of_bl_is_bl_to_bin_Not)
     apply(subgoal_tac "length (take n ls) \<le> len_of TYPE('s)")
      prefer 2
      apply fastforce
     apply(subgoal_tac "length (dropWhile Not (to_bl (of_bl (take n ls)))) \<le> length (take n ls)")
      using dual_order.trans apply blast
     using length_dropWhile_Not_bl apply blast
    apply(simp)
    done*)

corollary yaaaaaaaaaaaaaaaayaiohhgoo: 
  "n \<le> 16 \<Longrightarrow> of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 16 word)
            (to_bl ((of_bl:: bool list \<Rightarrow> 128 word) (take n ls))))) =
    (of_bl:: bool list \<Rightarrow> 128 word) (take n ls)"
  apply(rule bl_cast_long_short_long_take)
   apply(simp_all)
  done

  (*this would be nice*)
  lemma hooo: fixes ip::ipv6addr
    shows "length ls \<le> 16 \<Longrightarrow> 
     of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 16 word)
            (to_bl ((of_bl:: bool list \<Rightarrow> 128 word) ls)))) =
    (of_bl:: bool list \<Rightarrow> 128 word) ls"
    oops




  lemma ucast16_ucast128_maks_highest_bits: fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst word128_and_slice112)
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
    apply(subst Word.slice_take)
    apply(simp)
    thm yaaaaaaaaaaaaaaaayaiohhgoo
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    done

lemma "(ip >> 112) && mask 16 << 112 >> 112 = (((ip >> 112) && mask 16) << 112) >> 112" by simp

  lemma "size ((ip::ipv6addr) >> 112) = 128" by(simp add: word_size)

  (*TODO: to l4v!*)
  lemma length_dropNot_mask:
    fixes w::"'a::len word"
    shows "length (dropWhile Not (to_bl (w AND mask n))) \<le> n"
    apply(subst Word.bl_and_mask)
    by (simp add: List.dropWhile_eq_drop length_takeWhile_Not_replicate_False)

  (*this for arbitrary 112 and probably: for arbitrary 16*)
  lemma fixes ip::ipv6addr
    shows "length (dropWhile Not (to_bl (ip AND (mask 16 << 112) >> 112))) \<le> 16"
    apply(subst WordLemmaBucket.word_and_mask_shiftl)
    apply(subst WordLib.shiftl_shiftr1)
     apply(simp; fail)
    apply(simp)
    apply(subst WordLib.and_mask)
    apply(simp add: word_size)
    apply(simp add: length_dropNot_mask)
    done

  (*the same without slice to generalize to the other cases*)
  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst word128_mask112)
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask112)+
    thm bl_cast_long_short_long_ingoreLeadingZero_generic
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply(simp_all)

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
    oops

  lemma word128_mask96: "(0xFFFF000000000000000000000000::ipv6addr) = (mask 16) << 96"
    by(simp add: mask_def)

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000000000000000 >> 96)) << 96) =
         ip AND 0xFFFF000000000000000000000000"
    apply(subst word128_mask96)
    apply(subst Word.ucast_bl)+
    apply(subst word128_mask96)+
    thm bl_cast_long_short_long_ingoreLeadingZero_generic
    apply(subst bl_cast_long_short_long_ingoreLeadingZero_generic)
      apply simp_all
      (*TODO: continue here!*)
    oops


  lemma "ip \<le> 2^(len_of TYPE(16)) \<Longrightarrow> (ucast::16 word \<Rightarrow> 128 word) ((ucast::128 word \<Rightarrow> 16 word) ip) = ip"
    apply(simp add: ucast_def)
    oops
    
    

 lemma Word_ucast_bl_16_128:
  "(ucast::16 word \<Rightarrow> ipv6addr) ((ucast::ipv6addr \<Rightarrow> 16 word) ip) =
   (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl:: bool list \<Rightarrow> 16 word) ((to_bl:: 128 word \<Rightarrow> bool list) ip)))"
    apply(subst Word.ucast_bl)+
    apply simp
    done

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (slice 112 ip)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst Word_ucast_bl_16_128)
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
    apply(subst Word.slice_take)+
    apply(simp)
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    oops

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    using ucast16_ucast128_maks_highest_bits by simp
    (*proof -
      have "(word_of_int::int \<Rightarrow> 128 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))) << (112::nat) =
           ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat) << (112::nat)"
      by simp
      show "(word_of_int :: int \<Rightarrow> 128 word) (uint 
          ((word_of_int :: int \<Rightarrow> 16 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))) << (112::nat) =
    ip && (0xFFFF0000000000000000000000000000::128 word)"
        apply(simp)
        done
    apply(simp add: ucast_def)
    apply(subst x)
    thm word_of_int_uint
    thm Word.word_of_int_uint[of "ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)"]
    apply(subst Word.word_of_int_uint[of "ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)"])
    apply simp
    apply(simp add: Word.word_of_int_uint)
    oops*)

  (*TODO: round trip property one*)
  lemma "ipv6preferred_to_int (int_to_ipv6preferred ip) = ip"
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    apply(simp add: ucast16_ucast128_maks_highest_bits)
    oops
    

  (*TODO: round trip property two*)
  lemma "int_to_ipv6preferred (ipv6preferred_to_int ip) = ip"
    apply(cases ip, rename_tac a b c d e f g h)
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    oops


end