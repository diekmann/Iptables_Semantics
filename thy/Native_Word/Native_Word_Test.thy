(*  Title:      Native_Word_Test.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* Test cases *}

theory Native_Word_Test imports
  Uint32 Uint16 Uint8 Uint Native_Cast
  "~~/src/HOL/Library/Code_Test"
begin

section {* Tests for @{typ uint32} *}

context begin notation sshiftr_uint32 (infixl ">>>" 55)

definition test_uint32 where
  "test_uint32 \<longleftrightarrow>
  (([ 0x100000001, -1, -4294967291, 0xFFFFFFFF, 0x12345678
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + (- 6), 0xFFFFFFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , set_bit 5 32 True, set_bit 5 32 False, set_bit (- 5) 32 True, set_bit (- 5) 32 False
    , 1 << 2, -1 << 3, 1 << 32, 1 << 0
    , 100 >> 3, -100 >> 3, 100 >> 32, -100 >> 32
    , 100 >>> 3, -100 >>> 3, 100 >>> 32, -100 >>> 32] :: uint32 list)
   =
    [ 1, 4294967295, 5, 4294967295, 305419896
    , 18
    , 126
    , 108
    , 4294967205
    , 11, 1, 4294967295, 4294967285, 0
    , 2, 4294967294
    , 15, 4294967281, 20, 1891143032
    , 1, 1431655763, 0, 0
    , 2, 2, 4294967291, 5 
    , 21, 4294967295, 4, 4294967289
    , 5, 5, 4294967291, 4294967291
    , 4, 4294967288, 0, 1
    , 12, 536870899, 0, 0
    , 12, 4294967283, 0, 4294967295]) \<and>
  ([ (0x5 :: uint32) = 0x5, (0x5 :: uint32) = 0x6
   , (0x5 :: uint32) < 0x5, (0x5 :: uint32) < 0x6, (-5 :: uint32) < 6, (6 :: uint32) < -5
   , (0x5 :: uint32) \<le> 0x5, (0x5 :: uint32) \<le> 0x4, (-5 :: uint32) \<le> 6, (6 :: uint32) \<le> -5 
   , (0x7FFFFFFF :: uint32) < 0x80000000, (0xFFFFFFFF :: uint32) < 0, (0x80000000 :: uint32) < 0x7FFFFFFF
   , (0x7FFFFFFF :: uint32) !! 0, (0x7FFFFFFF :: uint32) !! 31, (0x80000000 :: uint32) !! 31, (0x80000000 :: uint32) !! 32
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint32 0, integer_of_uint32 0x7FFFFFFF, integer_of_uint32 0x80000000, integer_of_uint32 0xAAAAAAAA]
  =
   [0, 0x7FFFFFFF, 0x80000000, 0xAAAAAAAA])"

end

export_code test_uint32 checking SML Haskell? OCaml? Scala

notepad begin
have test_uint32 by eval
have test_uint32 by code_simp
have test_uint32 by normalization
end

definition test_uint32' :: uint32 
where "test_uint32' = 0 + 10 - 14 * 3 div 6 mod 3 << 3 >> 2"
ML {* val 0wx12 = @{code test_uint32'} *}

lemma "x AND y = x OR (y :: uint32)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: uint32) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
by transfer simp

lemma "(f :: uint32 \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

section {* Tests for @{typ uint16} *}

context begin notation sshiftr_uint16 (infixl ">>>" 55)

definition test_uint16 where
  "test_uint16 \<longleftrightarrow>
  (([ 0x10001, -1, -65535, 0xFFFF, 0x1234
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0xFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x1234 * 0x8765
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , set_bit 5 32 True, set_bit 5 32 False, set_bit (- 5) 32 True, set_bit (- 5) 32 False
    , 1 << 2, -1 << 3, 1 << 16, 1 << 0
    , 100 >> 3, -100 >> 3, 100 >> 16, -100 >> 16
    , 100 >>> 3, -100 >>> 3, 100 >>> 16, -100 >>> 16] :: uint16 list)
   =
    [ 1, 65535, 1, 65535, 4660
    , 18
    , 126
    , 108
    , 65445
    , 11, 1, 65535, 65525, 0
    , 2, 65534
    , 15, 65521, 20, 39556
    , 1, 21843, 0, 0
    , 2, 2, 65531, 5
    , 21, 65535, 4, 65529
    , 5, 5, 65531, 65531
    , 4, 65528, 0, 1
    , 12, 8179, 0, 0
    , 12, 65523, 0, 65535]) \<and>
  ([ (0x5 :: uint16) = 0x5, (0x5 :: uint16) = 0x6
   , (0x5 :: uint16) < 0x5, (0x5 :: uint16) < 0x6, (-5 :: uint16) < 6, (6 :: uint16) < -5
   , (0x5 :: uint16) \<le> 0x5, (0x5 :: uint16) \<le> 0x4, (-5 :: uint16) \<le> 6, (6 :: uint16) \<le> -5 
   , (0x7FFF :: uint16) < 0x8000, (0xFFFF :: uint16) < 0, (0x8000 :: uint16) < 0x7FFF
   , (0x7FFF :: uint16) !! 0, (0x7FFF :: uint16) !! 15, (0x8000 :: uint16) !! 15, (0x8000 :: uint16) !! 16
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint16 0, integer_of_uint16 0x7FFF, integer_of_uint16 0x8000, integer_of_uint16 0xAAAA]
  =
   [0, 0x7FFF, 0x8000, 0xAAAA])"
end

export_code test_uint16 checking Haskell? Scala
export_code test_uint16 in SML_word

notepad begin
have test_uint16 by code_simp
have test_uint16 by normalization
end

lemma "(x :: uint16) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
by transfer simp

lemma "(f :: uint16 \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

section {* Tests for @{typ uint8} *}

context begin notation sshiftr_uint8(infixl ">>>" 55)
definition test_uint8 where
  "test_uint8 \<longleftrightarrow> 
  (([ 0x101, -1, -255, 0xFF, 0x12
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0xFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x12 * 0x87
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , set_bit 5 32 True, set_bit 5 32 False, set_bit (- 5) 32 True, set_bit (- 5) 32 False
    , 1 << 2, -1 << 3, 1 << 8, 1 << 0
    , 100 >> 3, -100 >> 3, 100 >> 8, -100 >> 8
    , 100 >>> 3, -100 >>> 3, 100 >>> 8, -100 >>> 8] :: uint8 list)
   =
    [ 1, 255, 1, 255, 18
    , 18
    , 126
    , 108
    , 165
    , 11, 1, 255, 245, 0
    , 2, 254
    , 15, 241, 20, 126
    , 1, 83, 0, 0
    , 2, 2, 251, 5
    , 21, 255, 4, 249
    , 5, 5, 251, 251
    , 4, 248, 0, 1
    , 12, 19, 0, 0
    , 12, 243, 0, 255]) \<and>
  ([ (0x5 :: uint8) = 0x5, (0x5 :: uint8) = 0x6
   , (0x5 :: uint8) < 0x5, (0x5 :: uint8) < 0x6, (-5 :: uint8) < 6, (6 :: uint8) < -5
   , (0x5 :: uint8) \<le> 0x5, (0x5 :: uint8) \<le> 0x4, (-5 :: uint8) \<le> 6, (6 :: uint8) \<le> -5 
   , (0x7F :: uint8) < 0x80, (0xFF :: uint8) < 0, (0x80 :: uint8) < 0x7F
   , (0x7F :: uint8) !! 0, (0x7F :: uint8) !! 7, (0x80 :: uint8) !! 7, (0x80 :: uint8) !! 8
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint8 0, integer_of_uint8 0x7F, integer_of_uint8 0x80, integer_of_uint8 0xAA]
  =
   [0, 0x7F, 0x80, 0xAA])"
end

export_code test_uint8 checking SML Haskell? Scala

notepad begin
have test_uint8 by eval
have test_uint8 by code_simp
have test_uint8 by normalization
end
ML_val {* val true = @{code test_uint8} *}

definition test_uint8' :: uint8
where "test_uint8' = 0 + 10 - 14 * 3 div 6 mod 3 << 3 >> 2"
ML {* val 0wx12 = @{code test_uint8'} *}

lemma "x AND y = x OR (y :: uint8)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: uint8) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
by transfer simp

lemma "(f :: uint8 \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

section {* Tests for @{typ "uint"} *}

context begin notation sshiftr_uint (infixl ">>>" 55)
definition "test_uint \<equiv> let 
  test_list1 = (let
      HS = uint_of_int ((2^(dflt_size - 1)))
    in
      ([ HS+HS+1, -1, -HS - HS + 5, HS + (HS - 1), 0x12
      , 0x5A AND 0x36
      , 0x5A OR 0x36
      , 0x5A XOR 0x36
      , NOT 0x5A
      , 5 + 6, -5 + 6, -6 + 5, -5 + -6, HS + (HS - 1) + 1
      , 5 - 3, 3 - 5
      , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321]
    @ (if dflt_size > 4 then
      [ 5 div 3, -5 div 3, -5 div -3, 5 div -3
      , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
      , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
      , set_bit 5 dflt_size True, set_bit 5 dflt_size False, set_bit (- 5) dflt_size True, set_bit (- 5) dflt_size False
      , 1 << 2, -1 << 3, 1 << dflt_size, 1 << 0
      , 31 >> 3, -1 >> 3, 31 >> dflt_size, -1 >> dflt_size
      , 15 >>> 2, -1 >>> 3, 15 >>> dflt_size, -1 >>> dflt_size]
    else []) :: uint list));
  
  test_list2 = (let 
      S=wivs_shift 
    in 
      ([ 1, -1, -S + 5, S - 1, 0x12
      , 0x5A AND 0x36
      , 0x5A OR 0x36
      , 0x5A XOR 0x36
      , NOT 0x5A
      , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0
      , 5 - 3, 3 - 5
      , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321]
    @ (if dflt_size > 4 then
      [ 5 div 3, (S - 5) div 3, (S - 5) div (S - 3), 5 div (S - 3)
      , 5 mod 3, (S - 5) mod 3, (S - 5) mod (S - 3), 5 mod (S - 3)
      , set_bit 5 4 True, -1, set_bit 5 0 False, -7
      , 5, 5, -5, -5
      , 4, -8, 0, 1
      , 3, (S >> 3) - 1, 0, 0
      , 3, (S>>1) + (S >> 1) - 1, 0, -1] 
    else []) :: int list));

  test_list_c1 = (let
      HS = uint_of_int ((2^(dflt_size - 1)))
    in
  [  (0x5 :: uint) = 0x5, (0x5 :: uint) = 0x6
   , (0x5 :: uint) < 0x5, (0x5 :: uint) < 0x6, (-5 :: uint) < 6, (6 :: uint) < -5
   , (0x5 :: uint) \<le> 0x5, (0x5 :: uint) \<le> 0x4, (-5 :: uint) \<le> 6, (6 :: uint) \<le> -5 
   , (HS - 1) < HS, (HS + HS - 1) < 0, HS < HS - 1
   , (HS - 1) !! 0, (HS - 1 :: uint) !! (dflt_size - 1), (HS :: uint) !! (dflt_size - 1), (HS :: uint) !! dflt_size
   ]);

  test_list_c2 =
   [ True, False
   , False, dflt_size\<ge>2, dflt_size=3, dflt_size\<noteq>3
   , True, False, dflt_size=3, dflt_size\<noteq>3
   , True, False, False
   , dflt_size\<noteq>1, False, True, False
   ]
in
  test_list1 = map uint_of_int test_list2
\<and> test_list_c1 = test_list_c2"
end

export_code test_uint checking SML Haskell? OCaml? Scala

lemma "test_uint"
quickcheck[exhaustive, expect=no_counterexample]
oops -- "FIXME: prove correctness of test by reflective means (not yet supported)"

lemma "x AND y = x OR (y :: uint)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: uint) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
by transfer simp

lemma "(f :: uint \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

section {* Tests for casts *}

definition test_casts :: bool
where "test_casts \<longleftrightarrow>
  map uint8_of_char [CHR ''a'', Char Nibble0 Nibble0, Char NibbleF NibbleF] = [97, 0, 255] \<and>
  map char_of_uint8 [65, 0, 255] = [CHR ''A'', Char Nibble0 Nibble0, Char NibbleF NibbleF] \<and>
  map uint8_of_uint32 [10, 0, 0xFE, 0xFFFFFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint32_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF]"

definition test_casts' :: bool
where "test_casts' \<longleftrightarrow>
  map uint8_of_uint16 [10, 0, 0xFE, 0xFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint16_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF] \<and>
  map uint16_of_uint32 [10, 0, 0xFFFE, 0xFFFFFFFF] = [10, 0, 0xFFFE, 0xFFFF] \<and>
  map uint32_of_uint16 [10, 0, 0xFFFF] = [10, 0, 0xFFFF]"

export_code test_casts checking SML Haskell? Scala
export_code test_casts' checking Haskell? Scala

notepad begin
have test_casts by eval
have test_casts by normalization
have test_casts by code_simp
have test_casts' by normalization
have test_casts' by code_simp
end
ML {* val true = @{code test_casts} *}

end
