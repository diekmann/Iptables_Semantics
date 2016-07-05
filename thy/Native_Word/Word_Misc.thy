(*  Title:      Word_Misc.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* More about words *}

theory Word_Misc imports
  "~~/src/HOL/Word/Word"
  More_Bits_Int
begin

text {*
  The separate code target @{text SML_word} collects setups for the
  code generator that PolyML does not provide.
*}

setup {* Code_Target.add_derived_target ("SML_word", [(Code_ML.target_SML, I)]) *}

code_identifier code_module Word_Misc \<rightharpoonup>
  (SML) Word and (Haskell) Word and (OCaml) Word and (Scala) Word

context
includes integer.lifting
begin
lift_definition word_of_integer :: "integer \<Rightarrow> 'a :: len0 word" is word_of_int .

lemma word_of_integer_code [code]: "word_of_integer n = word_of_int (int_of_integer n)"
by(simp add: word_of_integer.rep_eq)
end

lemma shiftr_zero_size: "size x \<le> n \<Longrightarrow> x >> n = (0 :: 'a :: len0 word)"
by(rule word_eqI)(auto simp add: nth_shiftr dest: test_bit_size)

lemma mask_full [simp]: "mask (len_of TYPE('a :: len)) = (-1 :: 'a word)"
by(simp add: mask_def word_pow_0)

lemma set_bit_beyond: fixes x :: "'a :: len0 word" shows
  "size x \<le> n \<Longrightarrow> set_bit x n b = x"
by(auto intro: word_eqI simp add: test_bit_set_gen word_size)

lemma word_of_int_code [code abstract]:
  "uint (word_of_int x :: 'a word) = x AND bin_mask (len_of TYPE('a :: len0))"
by(simp add: uint_word_of_int and_bin_mask_conv_mod)


context begin interpretation lifting_syntax .

lemma shiftl_transfer [transfer_rule]:
  "(pcr_word ===> op = ===> pcr_word) op << op <<"
by(auto intro!: rel_funI word_eqI simp add: word.pcr_cr_eq cr_word_def word_size nth_shiftl)

end

lemma set_bits_K_False [simp]: "set_bits (\<lambda>_. False) = (0 :: 'a :: len0 word)"
by(rule word_eqI)(simp add: test_bit.eq_norm)

lemma test_bit_1' [simp]: "(1 :: 'a :: len0 word) !! n \<longleftrightarrow> 0 < len_of TYPE('a) \<and> n = 0"
by(cases n)(simp_all only: one_word_def test_bit_wi bin_nth.simps, simp_all)

lemma mask_0 [simp]: "mask 0 = 0"
by(simp add: Word.mask_def)

lemma shiftl0 [simp]: "x << 0 = (x :: 'a :: len0 word)"
by (metis shiftl_rev shiftr_x_0 word_rev_gal)

lemma mask_1: "mask 1 = 1"
by(simp add: mask_def)

lemma mask_Suc_0: "mask (Suc 0) = 1"
by(simp add: mask_def)

lemma mask_numeral: "mask (numeral n) = 2 * mask (pred_numeral n) + 1"
unfolding mask_def by transfer(simp, simp add: shiftl_int_def)

lemma bin_last_bintrunc: "bin_last (bintrunc l n) = (l > 0 \<and> bin_last n)"
by(cases l) simp_all

lemma word_and_1:
  fixes n :: "_ word"
  shows "n AND 1 = (if n !! 0 then 1 else 0)"
by transfer(rule bin_rl_eqI, simp_all add: bin_rest_trunc bin_last_bintrunc)

lemma bintrunc_shiftl: "bintrunc n (m << i) = bintrunc (n - i) m << i"
proof(induct i arbitrary: n)
  case (Suc i)
  thus ?case by(cases n) simp_all
qed simp

lemma uint_shiftl: "uint (n << i) = bintrunc (size n) (uint n << i)"
unfolding word_size by transfer(simp add: bintrunc_shiftl)

context fixes f :: "nat \<Rightarrow> bool" begin

fun set_bits_aux :: "'a word \<Rightarrow> nat \<Rightarrow> 'a :: len0 word"
where
  "set_bits_aux w 0 = w"
| "set_bits_aux w (Suc n) = set_bits_aux ((w << 1) OR (if f n then 1 else 0)) n"

lemma set_bits_aux_conv: "set_bits_aux w n = (w << n) OR (set_bits f AND mask n)"
apply(induct w n rule: set_bits_aux.induct)
apply(auto 4 3 intro: word_eqI simp add: word_ao_nth nth_shiftl test_bit.eq_norm word_size not_less less_Suc_eq)
done

corollary set_bits_conv_set_bits_aux:
  "set_bits f = (set_bits_aux 0 (len_of TYPE('a)) :: 'a :: len word)"
by(simp add: set_bits_aux_conv)

end

lemma word_test_bit_set_bits: "(BITS n. f n :: 'a :: len0 word) !! n \<longleftrightarrow> n < len_of TYPE('a) \<and> f n"
by(auto simp add: word_set_bits_def test_bit_bl word_bl.Abs_inverse word_size)

lemma word_of_int_conv_set_bits: "word_of_int i = (BITS n. i !! n)"
by(rule word_eqI)(simp add: word_test_bit_set_bits)

text {*
  Division on @{typ "'a word"} is unsigned, but Scala and OCaml only have signed division and modulus.
*}
definition word_sdiv :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixl "sdiv" 70)
where [code]:
  "x sdiv y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0) \<noteq> (y' < 0);
        result = abs x' div abs y'
    in word_of_int (if negative then -result else result))"

definition word_smod :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixl "smod" 70)
where [code]:
  "x smod y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0);
        result = abs x' mod abs y'
    in word_of_int (if negative then -result else result))"

lemma sdiv_smod_id: "(a sdiv b) * b + (a smod b) = a"
proof -
  note [simp] = word_sdiv_def word_smod_def
  have F5: "\<forall>u::'a word. - (- u) = u" by (metis word_sint.Rep_inverse' minus_minus wi_hom_neg)
  have F7: "\<forall>v u::'a word. u + v = v + u" by(metis add.left_commute add_0_right)
  have F8: "\<forall>(w::'a word) (v::int) u::int. word_of_int u + word_of_int v * w = word_of_int (u + v * sint w)"
    by (metis word_sint.Rep_inverse wi_hom_syms(1) wi_hom_syms(3))
  have "\<exists>u. u = - sint b \<and> word_of_int (sint a mod u + - (- u * (sint a div u))) = a"
    using F5 by (metis minus_minus word_sint.Rep_inverse' mult_minus_left add.commute zmod_zdiv_equality)
  hence "word_of_int (sint a mod - sint b + - (sint b * (sint a div - sint b))) = a" by (metis equation_minus_iff)
  hence "word_of_int (sint a mod - sint b) + word_of_int (- (sint a div - sint b)) * b = a"
    using F8 by(metis mult.commute mult_minus_left)
  hence eq: "word_of_int (- (sint a div - sint b)) * b + word_of_int (sint a mod - sint b) = a" using F7 by metis

  show ?thesis
  proof(cases "sint a < 0")
    case True note a = this
    show ?thesis
    proof(cases "sint b < 0")
      case True
      with a show ?thesis
        by simp (metis F7 F8 eq minus_equation_iff minus_mult_minus semiring_div_class.mod_div_equality')
    next
      case False
      from eq have "word_of_int (- (- sint a div sint b)) * b + word_of_int (- (- sint a mod sint b)) = a"
        by (metis div_minus_right mod_minus_right)
      with a False show ?thesis by simp
    qed
  next
    case False note a = this
    show ?thesis
    proof(cases "sint b < 0")
      case True
      with a eq show ?thesis by simp
    next
      case False with a show ?thesis
        by simp (metis wi_hom_add wi_hom_mult add.commute mult.commute word_sint.Rep_inverse add.commute zmod_zdiv_equality)
    qed
  qed
qed

lemma nat_div_eq_Suc_0_iff: "n div m = Suc 0 \<longleftrightarrow> n \<ge> m \<and> n < 2 * (m :: nat)"
  apply (auto simp add: sdl)
  using not_less apply fastforce
  apply (metis One_nat_def Suc_1 div_eq_0_iff lessI neq0_conv td_gal_lt)
  done

lemma word_div_lt_eq_0:
  fixes x :: "'a :: len word"
  shows "x < y \<Longrightarrow> x div y = 0"
by(simp only: word_div_def zero_word_def uint_nat zdiv_int[symmetric] transfer_int_nat_numerals(1) word_less_def div_less)

lemma Suc_0_lt_2p_len_of: "Suc 0 < 2 ^ len_of TYPE('a :: len)"
by (metis One_nat_def len_gt_0 one_less_numeral_iff one_less_power semiring_norm(76))

lemma unat_p2: "n < len_of TYPE('a :: len) \<Longrightarrow> unat (2 ^ n :: 'a word) = 2 ^ n"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  then obtain n' where "len_of TYPE('a) = Suc n'" by(cases "len_of TYPE('a)") simp_all
  with Suc show ?case by(simp add: unat_word_ariths bintrunc_mod2p int_mod_eq')
qed

lemma div_half_nat:
  fixes x y :: nat
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = 2 * (x div 2 div y); r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  let ?q = "2 * (x div 2 div y)"
  have q: "?q = x div y - x div y mod 2"
    by(metis div_mult2_eq mult.commute mult_div_cancel)
  let ?r = "x - ?q * y"
  have r: "?r = x mod y + x div y mod 2 * y"
    by(simp add: q diff_mult_distrib div_mod_equality')(metis diff_diff_cancel mod_less_eq_dividend mod_mult2_eq add.commute mult.commute)

  show ?thesis
  proof(cases "y \<le> x - ?q * y")
    case True
    hence "x div y mod 2 \<noteq> 0" unfolding r
      by(metis Divides.mod_div_equality' True assms diff_is_0_eq div_le_mono mod_by_0 mod_div_trivial mod_self mod_simps(1) mult_div_cancel q)
    hence "x div y = ?q + 1" unfolding q
      by(metis le_add_diff_inverse mod_2_not_eq_zero_eq_one_nat mod_less_eq_dividend add.commute)
    moreover hence "x mod y = ?r - y"
      by simp(metis Divides.mod_div_equality' diff_commute diff_diff_left mult_Suc)
    ultimately show ?thesis using True by(simp add: Let_def)
  next
    case False
    hence "x div y mod 2 = 0" unfolding r
      by(simp add: not_le)(metis Nat.add_0_right assms div_less div_mult_self2 mod_div_trivial mult.commute)
    hence "x div y = ?q" unfolding q by simp
    moreover hence "x mod y = ?r" by (metis mod_div_equality')
    ultimately show ?thesis using False by(simp add: Let_def)
  qed
qed

lemma div_half_word:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows "(x div y, x mod y) = (let q = (x >> 1) div y << 1; r = x - q * y in if y \<le> r then (q + 1, r - y) else (q, r))"
proof -
  obtain n where n: "x = of_nat n" "n < 2 ^ len_of TYPE('a)" by(cases x)
  obtain m where m: "y = of_nat m" "m < 2 ^ len_of TYPE('a)" by(cases y)
  let ?q = "(x >> 1) div y << 1"
  let ?q' = "2 * (n div 2 div m)"
  have "n div 2 div m < 2 ^ len_of TYPE('a)" using n by (metis of_nat_inverse unat_lt2p uno_simps(2))
  hence q: "?q = of_nat ?q'" using n m
    apply(simp add: shiftr_def shiftr1_def bin_rest_def uint_nat unat_of_nat shiftl_def shiftl1_def Bit_def word_div_def word_of_nat)
by (metis of_nat_inverse of_nat_numeral uno_simps(2) word_of_nat zdiv_int of_nat_mult)

  from assms have "m \<noteq> 0" using m by -(rule notI, simp)

  from n have "2 * (n div 2 div m) < 2 ^ len_of TYPE('a)"
    by(metis mult.commute div_mult2_eq mult_div_cancel less_imp_diff_less of_nat_inverse unat_lt2p uno_simps(2))
  moreover
  have "2 * (n div 2 div m) * m < 2 ^ len_of TYPE('a)" using n unfolding div_mult2_eq[symmetric]
    by(subst (2) mult.commute)(simp add: div_mod_equality' diff_mult_distrib mult_div_cancel div_mult2_eq)
  moreover have "2 * (n div 2 div m) * m \<le> n"
    by(metis div_mult2_eq div_mult_le mult.assoc mult.commute)
  ultimately
  have r: "x - ?q * y = of_nat (n - ?q' * m)"
    and "y \<le> x - ?q * y \<Longrightarrow> of_nat (n - ?q' * m) - y = of_nat (n - ?q' * m - m)"
    using n m unfolding q
    by(simp_all add: word_sub_wi word_mult_def uint_nat unat_of_nat of_nat_mult [symmetric] word_of_nat[symmetric] zdiff_int word_le_nat_alt del: of_nat_mult)
  thus ?thesis using n m div_half_nat[OF `m \<noteq> 0`, of n] unfolding q
    by(simp add: word_le_nat_alt word_div_def word_mod_def uint_nat unat_of_nat zmod_int[symmetric] zdiv_int[symmetric] word_of_nat[symmetric])(simp add: Let_def split del: split_if split: split_if_asm)
qed


lemma word_div_eq_1_iff: "n div m = 1 \<longleftrightarrow> n \<ge> m \<and> unat n < 2 * unat (m :: 'a :: len word)"
apply(simp only: word_arith_nat_defs word_le_nat_alt nat_div_eq_Suc_0_iff[symmetric])
apply(rule word_unat.Abs_inject)
 apply(simp only: unat_div[symmetric] word_unat.Rep)
apply(simp add: unats_def Suc_0_lt_2p_len_of)
done

text {*
  This algorithm implements unsigned division in terms of signed division.
  Taken from Hacker's Delight.
*}

lemma divmod_via_sdivmod:
  fixes x y :: "'a :: len word"
  assumes "y \<noteq> 0"
  shows
  "(x div y, x mod y) =
  (if 1 << (len_of TYPE('a) - 1) \<le> y then if x < y then (0, x) else (1, x - y)
   else let q = ((x >> 1) sdiv y) << 1;
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
proof(cases "1 << (len_of TYPE('a) - 1) \<le> y")
  case True
  note y = this
  show ?thesis
  proof(cases "x < y")
    case True
    hence "x mod y = x"
      by(cases x)(cases y, simp add: word_mod_def uint_nat unat_of_nat zmod_int[symmetric] word_of_nat[symmetric] mod_less word_less_nat_alt)
    thus ?thesis using True y by(simp add: word_div_lt_eq_0)
  next
    case False
    obtain n where n: "y = of_nat n" "n < 2 ^ len_of TYPE('a)" by(cases y)
    have "unat x < 2 ^ len_of TYPE('a)" by(rule unat_lt2p)
    also have "\<dots> = 2 * 2 ^ (len_of TYPE('a) - 1)"
      by(metis Suc_pred len_gt_0 power_Suc One_nat_def)
    also have "\<dots> \<le> 2 * n" using y n
      by(simp add: word_le_nat_alt unat_of_nat unat_p2)
    finally have div: "x div of_nat n = 1" using False n
      by(simp add: word_div_eq_1_iff not_less word_le_nat_alt unat_of_nat)
    moreover have "x mod y = x - x div y * y"
      by (metis add_diff_cancel2 word_mod_div_equality)
    with div n have "x mod y = x - y" by simp
    ultimately show ?thesis using False y n by simp
  qed
next
  case False
  note y = this
  obtain n where n: "x = of_nat n" "n < 2 ^ len_of TYPE('a)" by(cases x)
  hence "int n div 2 + 2 ^ (len_of TYPE('a) - Suc 0) < 2 ^ len_of TYPE('a)"
    by(cases "len_of TYPE('a)")(simp_all, simp only: int_numeral[symmetric] zdiv_int[symmetric] of_nat_power [symmetric])
  with y n have "sint (x >> 1) = uint (x >> 1)"
    by(simp add: sint_uint sbintrunc_mod2p shiftr_div_2n)(simp add: int_mod_eq' uint_nat unat_of_nat)
  moreover have "uint y + 2 ^ (len_of TYPE('a) - Suc 0) < 2 ^ len_of TYPE('a)" using y
    by(cases "len_of TYPE('a)")(simp_all add: not_le, metis lessI word_2p_lem word_less_def word_size)
  hence "sint y = uint y" by(simp add: sint_uint sbintrunc_mod2p int_mod_eq')
  ultimately show ?thesis using y
    by(subst div_half_word[OF assms])(simp add: word_sdiv_def uint_div[symmetric])
qed

lemma word_of_int_via_signed:
  fixes mask
  assumes mask_def: "mask = bin_mask (len_of TYPE('a))"
  and shift_def: "shift = 1 << len_of TYPE('a)"
  and index_def: "index = len_of TYPE('a) - 1"
  and overflow_def:"overflow = 1 << (len_of TYPE('a) - 1)"
  and least_def: "least = - overflow"
  shows
  "(word_of_int i :: 'a :: len word) =
   (let i' = i AND mask
    in if i' !! index then
         if i' - shift < least \<or> overflow \<le> i' - shift then arbitrary1 i' else word_of_int (i' - shift)
       else if i' < least \<or> overflow \<le> i' then arbitrary2 i' else word_of_int i')"
proof -
  def i' \<equiv> "i AND mask"
  have "shift = mask + 1" unfolding assms by(simp add: bin_mask_p1_conv_shift)
  hence "i' < shift" by(simp add: mask_def i'_def int_and_le)
  show ?thesis
  proof(cases "i' !! index")
    case True
    hence unf: "i' = overflow OR i'" unfolding assms i'_def
      by(auto intro!: bin_eqI simp add: bin_nth_ops)
    have "overflow \<le> i'" by(subst unf)(rule le_int_or, simp add: bin_sign_and assms i'_def)
    hence "i' - shift < least \<longleftrightarrow> False" unfolding assms
      by(cases "len_of TYPE('a)")(simp_all add: not_less Bit_def)
    moreover
    have "overflow \<le> i' - shift \<longleftrightarrow> False" using `i' < shift` unfolding assms
      by(cases "len_of TYPE('a)")(auto simp add: not_le Bit_def elim: less_le_trans)
    moreover
    have "word_of_int (i' - shift) = (word_of_int i :: 'a word)" using `i' < shift`
      by(auto intro!: word_eqI simp add: i'_def shift_def mask_def bin_nth_ops bin_nth_minus_p2 bin_sign_and)
    ultimately show ?thesis using True by(simp add: Let_def i'_def)
  next
    case False
    hence "i' = i AND bin_mask (len_of TYPE('a) - 1)" unfolding assms i'_def
      by(clarsimp simp add: i'_def bin_nth_ops intro!: bin_eqI)(cases "len_of TYPE('a)", auto simp add: less_Suc_eq)
    also have "\<dots> \<le> bin_mask (len_of TYPE('a) - 1)" by(rule int_and_le) simp
    also have "\<dots> < overflow" unfolding overflow_def
      by(simp add: bin_mask_p1_conv_shift[symmetric])
    also
    have "least \<le> 0" unfolding least_def overflow_def by simp
    have "0 \<le> i'" by(simp add: i'_def mask_def bin_mask_ge0)
    hence "least \<le> i'" using `least \<le> 0` by simp
    moreover
    have "word_of_int i' = (word_of_int i :: 'a word)"
      by(rule word_eqI)(auto simp add: i'_def bin_nth_ops mask_def)
    ultimately show ?thesis using False by(simp add: Let_def i'_def)
  qed
qed

lemma word_and_mask_or_conv_and_mask:
  "n !! index \<Longrightarrow> (n AND mask index) OR (1 << index) = n AND mask (index + 1)"
by(rule word_eqI)(auto simp add: word_ao_nth word_size nth_shiftl simp del: shiftl_1)

lemma uint_and_mask_or_full:
  fixes n :: "'a :: len word"
  assumes "n !! (len_of TYPE('a) - 1)"
  and "mask1 = mask (len_of TYPE('a) - 1)"
  and "mask2 = 1 << len_of TYPE('a) - 1"
  shows "uint (n AND mask1) OR mask2 = uint n"
proof -
  have "mask2 = uint (1 << len_of TYPE('a) - 1 :: 'a word)" using assms
    by(simp add: uint_shiftl word_size bintrunc_shiftl del: shiftl_1)(metis One_nat_def Suc_diff_Suc bintrunc_minus bintrunc_shiftl diff_self_eq_0 len_gt_0 len_num1 lessI uint_1 uint_word_arith_bintrs(8))
  hence "uint (n AND mask1) OR mask2 = uint (n AND mask1 OR (1 << len_of TYPE('a) - 1 :: 'a word))"
    by(simp add: uint_or)
  also have "\<dots> = uint (n AND mask (len_of TYPE('a) - 1 + 1))"
    using assms by(simp only: word_and_mask_or_conv_and_mask)
  also have "\<dots> = uint n" by simp
  finally show ?thesis .
qed

section {* Quickcheck conversion functions *}

notation scomp (infixl "\<circ>\<rightarrow>" 60)

definition qc_random_cnv ::
  "(natural \<Rightarrow> 'a::term_of) \<Rightarrow> natural \<Rightarrow> Random.seed
    \<Rightarrow> ('a \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
  where "qc_random_cnv a_of_natural i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
       let n = a_of_natural k
       in (n, \<lambda>_. Code_Evaluation.term_of n)))"

no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

definition qc_exhaustive_cnv :: "(natural \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_exhaustive_cnv a_of_natural f d =
   Quickcheck_Exhaustive.exhaustive (%x. f (a_of_natural x)) d"

definition qc_full_exhaustive_cnv ::
  "(natural \<Rightarrow> ('a::term_of)) \<Rightarrow> ('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "qc_full_exhaustive_cnv a_of_natural f d = Quickcheck_Exhaustive.full_exhaustive
  (%(x, xt). f (a_of_natural x, %_. Code_Evaluation.term_of (a_of_natural x))) d"

declare [[quickcheck_narrowing_ghc_options = "-XTypeSynonymInstances"]]

definition qc_narrowing_drawn_from :: "'a list \<Rightarrow> integer \<Rightarrow> _"
where
  "qc_narrowing_drawn_from xs =
   foldr Quickcheck_Narrowing.sum (map Quickcheck_Narrowing.cons (butlast xs)) (Quickcheck_Narrowing.cons (last xs))"

locale quickcheck_narrowing_samples =
  fixes a_of_integer :: "integer \<Rightarrow> 'a \<times> 'a :: {partial_term_of, term_of}"
  and zero :: "'a"
  and tr :: "typerep"
begin

function narrowing_samples :: "integer \<Rightarrow> 'a list"
where
  "narrowing_samples i =
   (if i > 0 then let (a, a') = a_of_integer i in narrowing_samples (i - 1) @ [a, a'] else [zero])"
by pat_completeness auto
termination including integer.lifting
proof(relation "measure nat_of_integer")
  fix i :: integer
  assume "0 < i"
  thus "(i - 1, i) \<in> measure nat_of_integer"
    by simp(transfer, simp)
qed simp

definition partial_term_of_sample :: "integer \<Rightarrow> 'a"
where
  "partial_term_of_sample i =
  (if i < 0 then undefined
   else if i = 0 then zero
   else if i mod 2 = 0 then snd (a_of_integer (i div 2))
   else fst (a_of_integer (i div 2 + 1)))"

lemma partial_term_of_code:
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_variable p t) \<equiv>
    Code_Evaluation.Free (STR ''_'') tr"
  "partial_term_of (ty :: 'a itself) (Quickcheck_Narrowing.Narrowing_constructor i []) \<equiv>
   Code_Evaluation.term_of (partial_term_of_sample i)"
by (rule partial_term_of_anything)+

end

lemmas [code] =
  quickcheck_narrowing_samples.narrowing_samples.simps
  quickcheck_narrowing_samples.partial_term_of_sample_def

end
