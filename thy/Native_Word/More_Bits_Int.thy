(*  Title:      Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* More bit operations on integers *}

theory More_Bits_Int
imports
  "~~/src/HOL/Word/Bits_Bit"
  "~~/src/HOL/Word/Bool_List_Representation"
begin

lemma last_rev' [simp]: "last (rev xs) = hd xs"
by(cases xs)(simp add: last_def hd_def, simp)

lemma butlast_rev [simp]: "butlast (rev xs) = rev (tl xs)"
by(cases xs) simp_all

lemma tl_upt [simp]: "tl [n..<m] = [Suc n..<m]"
by(cases "n < m")(simp_all add: upt_conv_Cons)

lemma nat_LEAST_True [simp]: "(LEAST _ :: nat. True) = 0"
by(auto intro: Least_equality)

lemma nat_less_numeral_unfold: fixes n :: nat shows
  "n < numeral w \<longleftrightarrow> n = pred_numeral w \<or> n < pred_numeral w"
by(auto simp add: numeral_eq_Suc)

section {* Lemmas about bit operations on @{typ int} *}

lemma twice_conv_BIT: "2 * x = x BIT False"
by(rule bin_rl_eqI)(simp_all, simp_all add: bin_rest_def bin_last_def)

lemma not_int_cmp_0 [simp]:
  fixes i :: int shows
  "0 < NOT i \<longleftrightarrow> i < -1"
  "0 \<le> NOT i \<longleftrightarrow> i < 0"
  "NOT i < 0 \<longleftrightarrow> i \<ge> 0"
  "NOT i \<le> 0 \<longleftrightarrow> i \<ge> -1"
by(simp_all add: int_not_def) arith+

lemma bbw_ao_dist2: "(x :: int) AND (y OR z) = x AND y OR x AND z"
by(metis int_and_comm bbw_ao_dist)

lemmas int_and_ac = bbw_lcs(1) int_and_comm int_and_assoc

lemma bit_nand_same [simp]: fixes x :: bit shows "x AND NOT x = 0"
by(cases x) simp_all

lemma int_nand_same [simp]: fixes x :: int shows "x AND NOT x = 0"
by(induct x y\<equiv>"NOT x" rule: bitAND_int.induct)(subst bitAND_int.simps, clarsimp)

lemma int_nand_same_middle: fixes x :: int shows "x AND y AND NOT x = 0"
by (metis bbw_lcs(1) int_and_0 int_nand_same)

lemma and_xor_dist: fixes x :: int shows
  "x AND (y XOR z) = (x AND y) XOR (x AND z)"
by(simp add: int_xor_def bbw_ao_dist2 bbw_ao_dist bbw_not_dist int_and_ac int_nand_same_middle)

lemma BIT_lt0 [simp]: "x BIT b < 0 \<longleftrightarrow> x < 0"
by(cases b)(auto simp add: Bit_def)

lemma BIT_ge0 [simp]: "x BIT b \<ge> 0 \<longleftrightarrow> x \<ge> 0"
by(cases b)(auto simp add: Bit_def)

lemma [simp]: 
  shows bin_rest_lt0: "bin_rest i < 0 \<longleftrightarrow> i < 0"
  and  bin_rest_ge_0: "bin_rest i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(auto simp add: bin_rest_def)

lemma bin_rest_gt_0 [simp]: "bin_rest x > 0 \<longleftrightarrow> x > 1"
by(simp add: bin_rest_def add1_zle_eq pos_imp_zdiv_pos_iff) (metis add1_zle_eq one_add_one)

lemma int_and_lt0 [simp]: fixes x y :: int shows
  "x AND y < 0 \<longleftrightarrow> x < 0 \<and> y < 0"
by(induct x y rule: bitAND_int.induct)(subst bitAND_int.simps, simp)

lemma int_and_ge0 [simp]: fixes x y :: int shows 
  "x AND y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<or> y \<ge> 0"
by (metis int_and_lt0 linorder_not_less)

lemma int_and_1: fixes x :: int shows "x AND 1 = x mod 2"
by(subst bitAND_int.simps)(simp add: Bit_def bin_last_def zmod_minus1)

lemma int_1_and: fixes x :: int shows "1 AND x = x mod 2"
by(subst int_and_comm)(simp add: int_and_1)

lemma int_or_lt0 [simp]: fixes x y :: int shows 
  "x OR y < 0 \<longleftrightarrow> x < 0 \<or> y < 0"
by(simp add: int_or_def)

lemma int_xor_lt0 [simp]: fixes x y :: int shows
  "x XOR y < 0 \<longleftrightarrow> ((x < 0) \<noteq> (y < 0))"
by(auto simp add: int_xor_def)

lemma int_xor_ge0 [simp]: fixes x y :: int shows
  "x XOR y \<ge> 0 \<longleftrightarrow> ((x \<ge> 0) \<longleftrightarrow> (y \<ge> 0))"
by (metis int_xor_lt0 linorder_not_le)

lemma bin_last_conv_AND:
  "bin_last i \<longleftrightarrow> i AND 1 \<noteq> 0"
proof -
  obtain x b where "i = x BIT b" by(cases i rule: bin_exhaust)
  hence "i AND 1 = 0 BIT b"
    by(simp add: BIT_special_simps(2)[symmetric] del: BIT_special_simps(2))
  thus ?thesis using `i = x BIT b` by(cases b) simp_all
qed

lemma bitval_bin_last:
  "of_bool (bin_last i) = i AND 1"
proof -
  obtain x b where "i = x BIT b" by(cases i rule: bin_exhaust)
  hence "i AND 1 = 0 BIT b"
    by(simp add: BIT_special_simps(2)[symmetric] del: BIT_special_simps(2))
  thus ?thesis by(cases b)(simp_all add: bin_last_conv_AND)
qed

lemma bl_to_bin_BIT:
  "bl_to_bin bs BIT b = bl_to_bin (bs @ [b])"
by(simp add: bl_to_bin_append)

lemma bin_last_bl_to_bin: "bin_last (bl_to_bin bs) \<longleftrightarrow> bs \<noteq> [] \<and> last bs"
by(cases "bs = []")(auto simp add: bl_to_bin_def last_bin_last'[where w=0])

lemma bin_rest_bl_to_bin: "bin_rest (bl_to_bin bs) = bl_to_bin (butlast bs)"
by(cases "bs = []")(simp_all add: bl_to_bin_def butlast_rest_bl2bin_aux)

lemma bin_nth_numeral_unfold:
  "bin_nth (numeral (num.Bit0 x)) n \<longleftrightarrow> n > 0 \<and> bin_nth (numeral x) (n - 1)"
  "bin_nth (numeral (num.Bit1 x)) n \<longleftrightarrow> (n > 0 \<longrightarrow> bin_nth (numeral x) (n - 1))"
by(case_tac [!] n) simp_all

lemma bin_sign_and:
  "bin_sign (i AND j) = - (bin_sign i * bin_sign j)"
by(simp add: bin_sign_def)

lemma minus_BIT_0: fixes x y :: int shows "x BIT b - y BIT False = (x - y) BIT b"
by(simp add: Bit_def)





primrec bin_mask :: "nat \<Rightarrow> int" 
where
  "bin_mask 0 = 0"
| "bin_mask (Suc n) = bin_mask n BIT True"

lemma bin_mask_conv_pow2:
  "bin_mask n = 2 ^ n - 1"
by(induct n)(simp_all add: Bit_def)

lemma bin_mask_ge0: "bin_mask n \<ge> 0"
by(induct n) simp_all

lemma and_bin_mask_conv_mod: "x AND bin_mask n = x mod 2 ^ n"
proof(induction n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  obtain x' b where "x = x' BIT b" by(cases x rule: bin_exhaust)
  with Suc show ?case by(cases b)(simp_all, simp_all add: Bit_def p1mod22k)
qed

lemma bin_mask_numeral: 
  "bin_mask (numeral n) = bin_mask (pred_numeral n) BIT True"
by(simp add: numeral_eq_Suc)

lemma bin_nth_mask [simp]: "bin_nth (bin_mask n) i \<longleftrightarrow> i < n"
proof(induction n arbitrary: i)
  case (Suc n)
  thus ?case by(cases i) simp_all
qed simp

lemma bin_sign_mask [simp]: "bin_sign (bin_mask n) = 0"
by(induct n) simp_all

section {* Symbolic bit operations on numerals and @{typ int}s *}

lemma int_not_neg_numeral: "NOT (- numeral n) = (Num.sub n num.One :: int)"
by(simp add: int_not_def)

lemma sub_inc_One: "Num.sub (Num.inc n) num.One = numeral n"
by (metis add_diff_cancel diff_minus_eq_add diff_numeral_special(2) diff_numeral_special(6))

lemma inc_BitM: "Num.inc (Num.BitM n) = num.Bit0 n"
by(simp add: BitM_plus_one[symmetric] add_One)

lemma int_neg_numeral_pOne_conv_not: "- numeral (n + num.One) = (NOT (numeral n) :: int)"
by(simp add: int_not_def)

fun bitOR_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitOR_num num.One num.One = num.One"
| "bitOR_num num.One (num.Bit0 n) = num.Bit1 n"
| "bitOR_num num.One (num.Bit1 n) = num.Bit1 n"
| "bitOR_num (num.Bit0 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit0 m) (num.Bit0 n) = num.Bit0 (bitOR_num m n)"
| "bitOR_num (num.Bit0 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit1 m) (num.Bit0 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"

fun bitAND_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitAND_num num.One num.One = Some num.One"
| "bitAND_num num.One (num.Bit0 n) = None"
| "bitAND_num num.One (num.Bit1 n) = Some num.One"
| "bitAND_num (num.Bit0 m) num.One = None"
| "bitAND_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) num.One = Some num.One"
| "bitAND_num (num.Bit1 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) (num.Bit1 n) = (case bitAND_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"

fun bitXOR_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitXOR_num num.One num.One = None"
| "bitXOR_num num.One (num.Bit0 n) = Some (num.Bit1 n)"
| "bitXOR_num num.One (num.Bit1 n) = Some (num.Bit0 n)"
| "bitXOR_num (num.Bit0 m) num.One = Some (num.Bit1 m)"
| "bitXOR_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitXOR_num m n)"
| "bitXOR_num (num.Bit0 m) (num.Bit1 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitXOR_num (num.Bit1 m) (num.Bit0 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitXOR_num m n)"

fun bitORN_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitORN_num num.One num.One = num.One"
| "bitORN_num num.One (num.Bit0 m) = num.Bit1 m"
| "bitORN_num num.One (num.Bit1 m) = num.Bit1 m"
| "bitORN_num (num.Bit0 n) num.One = num.Bit0 num.One"
| "bitORN_num (num.Bit0 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit0 n) (num.Bit1 m) = num.Bit0 (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) num.One = num.One"
| "bitORN_num (num.Bit1 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) (num.Bit1 m) = Num.BitM (bitORN_num n m)"

fun bitANDN_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitANDN_num num.One num.One = None"
| "bitANDN_num num.One (num.Bit0 n) = Some num.One"
| "bitANDN_num num.One (num.Bit1 n) = None"
| "bitANDN_num (num.Bit0 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit1 m) (num.Bit0 n) = (case bitANDN_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"
| "bitANDN_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"

lemma int_numeral_bitOR_num: "numeral n OR numeral m = (numeral (bitOR_num n m) :: int)"
by(induct n m rule: bitOR_num.induct) simp_all

lemma int_numeral_bitAND_num: "numeral n AND numeral m = (case bitAND_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct n m rule: bitAND_num.induct)(simp_all split: option.split)

lemma int_numeral_bitXOR_num:
  "numeral m XOR numeral n = (case bitXOR_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct m n rule: bitXOR_num.induct)(simp_all split: option.split)

lemma int_or_not_bitORN_num:
  "numeral n OR NOT (numeral m) = (- numeral (bitORN_num n m) :: int)"
by(induct n m rule: bitORN_num.induct)(simp_all add: Num.add_One BitM_inc)

lemma int_and_not_bitANDN_num:
  "numeral n AND NOT (numeral m) = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct n m rule: bitANDN_num.induct)(simp_all add: Num.add_One BitM_inc split: option.split)

lemma int_not_and_bitANDN_num:
  "NOT (numeral m) AND numeral n = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(simp add: int_and_not_bitANDN_num[symmetric] int_and_comm)

lemma Bit_code [code]:
  "0 BIT b = of_bool b"
  "Int.Pos n BIT False = Int.Pos (num.Bit0 n)"
  "Int.Pos n BIT True = Int.Pos (num.Bit1 n)"
  "Int.Neg n BIT False = Int.Neg (num.Bit0 n)"
  "Int.Neg n BIT True = Int.Neg (Num.BitM n)"
by(cases b)(simp_all)

lemma bin_last_code [code]: 
  "bin_last 0 \<longleftrightarrow> False"
  "bin_last (Int.Pos num.One) \<longleftrightarrow> True"
  "bin_last (Int.Pos (num.Bit0 n)) \<longleftrightarrow> False"
  "bin_last (Int.Pos (num.Bit1 n)) \<longleftrightarrow> True"
  "bin_last (Int.Neg num.One) \<longleftrightarrow> True"
  "bin_last (Int.Neg (num.Bit0 n)) \<longleftrightarrow> False"
  "bin_last (Int.Neg (num.Bit1 n)) \<longleftrightarrow> True"
by(simp_all)

lemma bin_nth_code [code]:
  "bin_nth 0                 n = False"
  "bin_nth (Int.Neg num.One) n = True"
  "bin_nth (Int.Pos num.One)      0 = True"
  "bin_nth (Int.Pos (num.Bit0 m)) 0 = False"
  "bin_nth (Int.Pos (num.Bit1 m)) 0 = True"
  "bin_nth (Int.Neg (num.Bit0 m)) 0 = False"
  "bin_nth (Int.Neg (num.Bit1 m)) 0 = True"
  "bin_nth (Int.Pos num.One)      (Suc n) = False"
  "bin_nth (Int.Pos (num.Bit0 m)) (Suc n) = bin_nth (Int.Pos m) n"
  "bin_nth (Int.Pos (num.Bit1 m)) (Suc n) = bin_nth (Int.Pos m) n"
  "bin_nth (Int.Neg (num.Bit0 m)) (Suc n) = bin_nth (Int.Neg m) n"
  "bin_nth (Int.Neg (num.Bit1 m)) (Suc n) = bin_nth (Int.Neg (Num.inc m)) n"
by(simp_all add: Num.add_One)

lemma int_not_code [code]:
  "NOT (0 :: int) = -1"
  "NOT (Int.Pos n) = Int.Neg (Num.inc n)"
  "NOT (Int.Neg n) = Num.sub n num.One"
by(simp_all add: Num.add_One int_not_def)

lemma int_and_code [code]: fixes i j :: int shows
  "0 AND j = 0"
  "i AND 0 = 0"
  "Int.Pos n AND Int.Pos m = (case bitAND_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n AND Int.Neg m = NOT (Num.sub n num.One OR Num.sub m num.One)"
  "Int.Pos n AND Int.Neg num.One = Int.Pos n"
  "Int.Pos n AND Int.Neg (num.Bit0 m) = Num.sub (bitORN_num (Num.BitM m) n) num.One"
  "Int.Pos n AND Int.Neg (num.Bit1 m) = Num.sub (bitORN_num (num.Bit0 m) n) num.One"
  "Int.Neg num.One AND Int.Pos m = Int.Pos m"
  "Int.Neg (num.Bit0 n) AND Int.Pos m = Num.sub (bitORN_num (Num.BitM n) m) num.One"
  "Int.Neg (num.Bit1 n) AND Int.Pos m = Num.sub (bitORN_num (num.Bit0 n) m) num.One"
apply(fold int_not_neg_numeral)
apply(simp_all add: int_numeral_bitAND_num int_or_not_bitORN_num[symmetric] bbw_not_dist Num.add_One int_not_neg_numeral sub_inc_One inc_BitM cong: option.case_cong)
apply(simp_all add: int_and_comm)
apply(metis int_not_neg_numeral int_not_not)
done

lemma int_or_code [code]: fixes i j :: int shows
  "0 OR j = j"
  "i OR 0 = i"
  "Int.Pos n OR Int.Pos m = Int.Pos (bitOR_num n m)"
  "Int.Neg n OR Int.Neg m = NOT (Num.sub n num.One AND Num.sub m num.One)"
  "Int.Pos n OR Int.Neg num.One = Int.Neg num.One"
  "Int.Pos n OR Int.Neg (num.Bit0 m) = (case bitANDN_num (Num.BitM m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Pos n OR Int.Neg (num.Bit1 m) = (case bitANDN_num (num.Bit0 m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg num.One OR Int.Pos m = Int.Neg num.One"
  "Int.Neg (num.Bit0 n) OR Int.Pos m = (case bitANDN_num (Num.BitM n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg (num.Bit1 n) OR Int.Pos m = (case bitANDN_num (num.Bit0 n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
apply(simp_all add: int_numeral_bitOR_num)
apply(simp_all add: int_or_def int_not_neg_numeral int_and_comm int_not_and_bitANDN_num del: int_not_simps(4) split: option.split)
apply(simp_all add: Num.add_One)
done

lemma int_xor_code [code]: fixes i j :: int shows
  "0 XOR j = j"
  "i XOR 0 = i"
  "Int.Pos n XOR Int.Pos m = (case bitXOR_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n XOR Int.Neg m = Num.sub n num.One XOR Num.sub m num.One"
  "Int.Neg n XOR Int.Pos m = NOT (Num.sub n num.One XOR Int.Pos m)"
  "Int.Pos n XOR Int.Neg m = NOT (Int.Pos n XOR Num.sub m num.One)"
by(fold int_not_neg_numeral)(simp_all add: int_numeral_bitXOR_num int_xor_not cong: option.case_cong)


section {* More on bits and bitss operations *}

inductive wf_set_bits_int :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" 
  for f :: "nat \<Rightarrow> bool"
where
  zeros: "\<forall>n' \<ge> n. \<not> f n' \<Longrightarrow> wf_set_bits_int f"
| ones: "\<forall>n' \<ge> n. f n' \<Longrightarrow> wf_set_bits_int f"

lemma wf_set_bits_int_simps: "wf_set_bits_int f \<longleftrightarrow> (\<exists>n. (\<forall>n'\<ge>n. \<not> f n') \<or> (\<forall>n'\<ge>n. f n'))"
by(auto simp add: wf_set_bits_int.simps)

lemma wf_set_bits_int_const [simp]: "wf_set_bits_int (\<lambda>_. b)"
by(cases b)(auto intro: wf_set_bits_int.intros)

lemma wf_set_bits_int_fun_upd [simp]: 
  "wf_set_bits_int (f(n := b)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain n'
    where "(\<forall>n''\<ge>n'. \<not> (f(n := b)) n'') \<or> (\<forall>n''\<ge>n'. (f(n := b)) n'')"
    by(auto simp add: wf_set_bits_int_simps)
  hence "(\<forall>n''\<ge>max (Suc n) n'. \<not> f n'') \<or> (\<forall>n''\<ge>max (Suc n) n'. f n'')" by auto
  thus ?rhs by(auto simp only: wf_set_bits_int_simps)
next
  assume ?rhs
  then obtain n' where "(\<forall>n''\<ge>n'. \<not> f n'') \<or> (\<forall>n''\<ge>n'. f n'')" (is "?wf f n'")
    by(auto simp add: wf_set_bits_int_simps)
  hence "?wf (f(n := b)) (max (Suc n) n')" by auto
  thus ?lhs by(auto simp only: wf_set_bits_int_simps)
qed

lemma wf_set_bits_int_Suc [simp]:
  "wf_set_bits_int (\<lambda>n. f (Suc n)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
by(auto simp add: wf_set_bits_int_simps intro: le_SucI dest: Suc_le_D)


lemma int_lsb_BIT [simp]: fixes x :: int shows
  "lsb (x BIT b) \<longleftrightarrow> b"
by(simp add: lsb_int_def)

lemma bin_last_conv_lsb: "bin_last = lsb"
by(clarsimp simp add: lsb_int_def fun_eq_iff)

lemma int_lsb_numeral [simp]:
  "lsb (0 :: int) = False"
  "lsb (1 :: int) = True"
  "lsb (Numeral1 :: int) = True"
  "lsb (- 1 :: int) = True"
  "lsb (- Numeral1 :: int) = True"
  "lsb (numeral (num.Bit0 w) :: int) = False"
  "lsb (numeral (num.Bit1 w) :: int) = True"
  "lsb (- numeral (num.Bit0 w) :: int) = False"
  "lsb (- numeral (num.Bit1 w) :: int) = True"
by(simp_all add: lsb_int_def)

lemma int_lsb_code [code]:
  "lsb (0 :: int) = False"
  "lsb (Int.Pos num.One) = True"
  "lsb (Int.Pos (num.Bit0 w)) = False"
  "lsb (Int.Pos (num.Bit1 w)) = True"
  "lsb (Int.Neg num.One) = True"
  "lsb (Int.Neg (num.Bit0 w)) = False"
  "lsb (Int.Neg (num.Bit1 w)) = True"
by simp_all

lemma int_set_bit_0 [simp]: fixes x :: int shows
  "set_bit x 0 b = bin_rest x BIT b"
by(auto simp add: set_bit_int_def intro: bin_rl_eqI)

lemma int_set_bit_Suc: fixes x :: int shows
  "set_bit x (Suc n) b = set_bit (bin_rest x) n b BIT bin_last x"
by(auto simp add: set_bit_int_def twice_conv_BIT intro: bin_rl_eqI)

lemma bin_last_set_bit:
  "bin_last (set_bit x n b) = (if n > 0 then bin_last x else b)"
by(cases n)(simp_all add: int_set_bit_Suc)

lemma bin_rest_set_bit: 
  "bin_rest (set_bit x n b) = (if n > 0 then set_bit (bin_rest x) (n - 1) b else bin_rest x)"
by(cases n)(simp_all add: int_set_bit_Suc)

lemma int_set_bit_numeral: fixes x :: int shows
  "set_bit x (numeral w) b = set_bit (bin_rest x) (pred_numeral w) b BIT bin_last x"
by(simp add: set_bit_int_def)

lemmas int_set_bit_numerals [simp] =
  int_set_bit_numeral[where x="numeral w'"] 
  int_set_bit_numeral[where x="- numeral w'"]
  int_set_bit_numeral[where x="Numeral1"]
  int_set_bit_numeral[where x="1"]
  int_set_bit_numeral[where x="0"]
  int_set_bit_Suc[where x="numeral w'"]
  int_set_bit_Suc[where x="- numeral w'"]
  int_set_bit_Suc[where x="Numeral1"]
  int_set_bit_Suc[where x="1"]
  int_set_bit_Suc[where x="0"]
  for w'

lemma int_shiftl_BIT: fixes x :: int
  shows int_shiftl0 [simp]: "x << 0 = x"
  and int_shiftl_Suc [simp]: "x << Suc n = (x << n) BIT False"
by(auto simp add: shiftl_int_def Bit_def)

lemma int_0_shiftl [simp]: "0 << n = (0 :: int)"
by(induct n) simp_all

lemma bin_last_shiftl: "bin_last (x << n) \<longleftrightarrow> n = 0 \<and> bin_last x"
by(cases n)(simp_all)

lemma bin_rest_shiftl: "bin_rest (x << n) = (if n > 0 then x << (n - 1) else bin_rest x)"
by(cases n)(simp_all)

lemma bin_nth_shiftl [simp]: "bin_nth (x << n) m \<longleftrightarrow> n \<le> m \<and> bin_nth x (m - n)"
proof(induct n arbitrary: x m)
  case (Suc n)
  thus ?case by(cases m) simp_all
qed simp

lemma int_shiftr_BIT [simp]: fixes x :: int
  shows int_shiftr0: "x >> 0 = x"
  and int_shiftr_Suc: "x BIT b >> Suc n = x >> n"
proof -
  show "x >> 0 = x" by (simp add: shiftr_int_def)
  show "x BIT b >> Suc n = x >> n" by (cases b)
   (simp_all add: shiftr_int_def Bit_def add.commute pos_zdiv_mult_2)
qed

lemma bin_last_shiftr: "bin_last (x >> n) \<longleftrightarrow> x !! n"
proof(induct n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) simp
qed

lemma bin_rest_shiftr [simp]: "bin_rest (x >> n) = x >> Suc n"
proof(induct n arbitrary: x)
  case 0
  thus ?case by(cases x rule: bin_exhaust) auto
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) auto
qed

lemma bin_nth_shiftr [simp]: "bin_nth (x >> n) m = bin_nth x (n + m)"
proof(induct n arbitrary: x m)
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) simp_all
qed simp

lemma bin_nth_conv_AND:
  fixes x :: int shows 
  "bin_nth x n \<longleftrightarrow> x AND (1 << n) \<noteq> 0"
proof(induct n arbitrary: x)
  case 0 
  thus ?case by(simp add: int_and_1 bin_last_def)
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust)(simp_all add: bin_nth_ops Bit_eq_0_iff)
qed

lemma int_shiftl_numeral [simp]: 
  "(numeral w :: int) << numeral w' = numeral (num.Bit0 w) << pred_numeral w'"
  "(- numeral w :: int) << numeral w' = - numeral (num.Bit0 w) << pred_numeral w'"
by(simp_all add: numeral_eq_Suc Bit_def shiftl_int_def)
  (metis add_One mult_inc semiring_norm(11) semiring_norm(13) semiring_norm(2) semiring_norm(6) semiring_norm(87))+

lemma int_shiftl_code [code]:
  "i << 0 = i"
  "i << Suc n = Int.dup i << n"
by(simp_all add: shiftl_int_def)

lemma int_shiftl_One_numeral [simp]: "(1 :: int) << numeral w = 2 << pred_numeral w"
by(metis int_shiftl_numeral numeral_One)

lemma shiftl_ge_0 [simp]: fixes i :: int shows "i << n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(induct n) simp_all

lemma shiftl_lt_0 [simp]: fixes i :: int shows "i << n < 0 \<longleftrightarrow> i < 0"
by (metis not_le shiftl_ge_0)

lemma int_shiftl_test_bit: "(n << i :: int) !! m \<longleftrightarrow> m \<ge> i \<and> n !! (m - i)"
proof(induction i)
  case (Suc n)
  thus ?case by(cases m) simp_all
qed simp

lemma bin_mask_p1_conv_shift: "bin_mask n + 1 = 1 << n"
by(induct n) simp_all

lemma int_0shiftr [simp]: "(0 :: int) >> x = 0"
by(simp add: shiftr_int_def)

lemma int_minus1_shiftr [simp]: "(-1 :: int) >> x = -1"
by(simp add: shiftr_int_def div_eq_minus1)

lemma int_shiftr_ge_0 [simp]: fixes i :: int shows "i >> n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
proof(induct n arbitrary: i)
  case (Suc n)
  thus ?case by(cases i rule: bin_exhaust) simp_all
qed simp

lemma int_shiftr_lt_0 [simp]: fixes i :: int shows "i >> n < 0 \<longleftrightarrow> i < 0"
by (metis int_shiftr_ge_0 not_less)

lemma uminus_Bit_eq:
  "- k BIT b = (- k - of_bool b) BIT b"
  by (cases b) (simp_all add: Bit_def)

lemma int_shiftr_numeral [simp]:
  "(1 :: int) >> numeral w' = 0"
  "(numeral num.One :: int) >> numeral w' = 0"
  "(numeral (num.Bit0 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(numeral (num.Bit1 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(- numeral (num.Bit0 w) :: int) >> numeral w' = - numeral w >> pred_numeral w'"
  "(- numeral (num.Bit1 w) :: int) >> numeral w' = - numeral (Num.inc w) >> pred_numeral w'"
  by (simp_all only: numeral_One expand_BIT numeral_eq_Suc int_shiftr_Suc BIT_special_simps(2)[symmetric] int_0shiftr add_One uminus_Bit_eq)
    (simp_all add: add_One)

lemma int_shiftr_numeral_Suc0 [simp]:
  "(1 :: int) >> Suc 0 = 0"
  "(numeral num.One :: int) >> Suc 0 = 0"
  "(numeral (num.Bit0 w) :: int) >> Suc 0 = numeral w"
  "(numeral (num.Bit1 w) :: int) >> Suc 0 = numeral w"
  "(- numeral (num.Bit0 w) :: int) >> Suc 0 = - numeral w"
  "(- numeral (num.Bit1 w) :: int) >> Suc 0 = - numeral (Num.inc w)"
by(simp_all only: One_nat_def[symmetric] numeral_One[symmetric] int_shiftr_numeral pred_numeral_simps int_shiftr0)

lemma int_shiftr_code [code]: fixes i :: int shows
  "i >> 0 = i"
  "0 >> Suc n = (0 :: int)"
  "Int.Pos num.One >> Suc n = 0"
  "Int.Pos (num.Bit0 m) >> Suc n = Int.Pos m >> n"
  "Int.Pos (num.Bit1 m) >> Suc n = Int.Pos m >> n"
  "Int.Neg num.One >> Suc n = -1"
  "Int.Neg (num.Bit0 m) >> Suc n = Int.Neg m >> n"
  "Int.Neg (num.Bit1 m) >> Suc n = Int.Neg (Num.inc m) >> n"
  by (simp_all only: int_shiftr_Suc BIT_special_simps(2)[symmetric] int_shiftr0 int_0shiftr numeral_One int_minus1_shiftr Int.Pos_def Int.Neg_def expand_BIT int_shiftr_Suc Num.add_One uminus_Bit_eq)
    (simp_all add: add_One)

lemma bin_nth_minus_p2:
  assumes sign: "bin_sign x = 0"
  and y: "y = 1 << n"
  and m: "m < n"
  and x: "x < y"
  shows "bin_nth (x - y) m = bin_nth x m"
using sign m x unfolding y
proof(induction m arbitrary: x y n)
  case 0
  thus ?case
    by(simp add: bin_last_def shiftl_int_def) (metis (hide_lams, no_types) mod_diff_right_eq mod_self neq0_conv numeral_One power_eq_0_iff power_mod diff_zero zero_neq_numeral)
next
  case (Suc m)
  from `Suc m < n` obtain n' where [simp]: "n = Suc n'" by(cases n) auto
  obtain x' b where [simp]: "x = x' BIT b" by(cases x rule: bin_exhaust)
  from `bin_sign x = 0` have "bin_sign x' = 0" by simp
  moreover from `x < 1 << n` have "x' < 1 << n'"
    by(cases b)(simp_all add: Bit_def shiftl_int_def)
  moreover have "(2 * x' + of_bool b - 2 * 2 ^ n') div 2 = x' + (- (2 ^ n') + of_bool b div 2)"
    by(simp only: add_diff_eq[symmetric] add.commute div_mult_self2[OF zero_neq_numeral[symmetric]])
  ultimately show ?case using Suc.IH[of x' n'] Suc.prems
    by(cases b)(simp_all add: Bit_def bin_rest_def shiftl_int_def)
qed

lemma bin_clr_conv_NAND:
  "bin_sc n False i = i AND NOT (1 << n)"
by(induct n arbitrary: i)(auto intro: bin_rl_eqI)

lemma bin_set_conv_OR:
  "bin_sc n True i = i OR (1 << n)"
by(induct n arbitrary: i)(auto intro: bin_rl_eqI)

lemma fixes i :: int 
  shows int_set_bit_True_conv_OR [code]: "set_bit i n True = i OR (1 << n)"
  and int_set_bit_False_conv_NAND [code]: "set_bit i n False = i AND NOT (1 << n)"
  and int_set_bit_conv_ops: "set_bit i n b = (if b then i OR (1 << n) else i AND NOT (1 << n))"
by(simp_all add: set_bit_int_def bin_set_conv_OR bin_clr_conv_NAND)

lemma int_set_bits_K_True [simp]: "(BITS _. True) = (-1 :: int)"
by(auto simp add: set_bits_int_def bin_last_bl_to_bin)

lemma int_set_bits_K_False [simp]: "(BITS _. False) = (0 :: int)"
by(auto simp add: set_bits_int_def)

lemma int_set_bits_unfold_BIT:
  assumes "wf_set_bits_int f"
  shows "set_bits f = set_bits (f \<circ> Suc) BIT f 0"
using assms
proof cases
  case (zeros n)
  show ?thesis
  proof(cases "\<forall>n. \<not> f n")
    case True
    hence "f = (\<lambda>_. False)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "f n'" by blast
    with zeros have "(LEAST n. \<forall>n'\<ge>n. \<not> f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. \<not> f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. \<not> f n') = (\<lambda>n. \<forall>n'\<ge>n. \<not> f (Suc n'))" by(auto dest: Suc_le_D)
    also from zeros have "\<forall>n'\<ge>n. \<not> f (Suc n')" by auto
    ultimately show ?thesis using zeros
      by(simp (no_asm_simp) add: set_bits_int_def exI split del: split_if)(rule bin_rl_eqI, auto simp add: bin_last_bl_to_bin hd_map bin_rest_bl_to_bin map_tl[symmetric] map_map[symmetric] map_Suc_upt simp del: map_map)
  qed
next
  case (ones n)
  show ?thesis
  proof(cases "\<forall>n. f n")
    case True
    hence "f = (\<lambda>_. True)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "\<not> f n'" by blast
    with ones have "(LEAST n. \<forall>n'\<ge>n. f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. f n') = (\<lambda>n. \<forall>n'\<ge>n. f (Suc n'))" by(auto dest: Suc_le_D)
    also from ones have "\<forall>n'\<ge>n. f (Suc n')" by auto
    moreover from ones have "(\<exists>n. \<forall>n'\<ge>n. \<not> f n') = False"
      by(auto intro!: exI[where x="max n m" for n m] simp add: max_def split: split_if_asm)
    moreover hence "(\<exists>n. \<forall>n'\<ge>n. \<not> f (Suc n')) = False"
      by(auto elim: allE[where x="Suc n" for n] dest: Suc_le_D)
    ultimately show ?thesis using ones
      by(simp (no_asm_simp) add: set_bits_int_def exI split del: split_if)(auto simp add: Let_def bin_last_bl_to_bin hd_map bin_rest_bl_to_bin map_tl[symmetric] map_map[symmetric] map_Suc_upt simp del: map_map)
  qed
qed

lemma bin_last_set_bits [simp]:
  "wf_set_bits_int f \<Longrightarrow> bin_last (set_bits f) = f 0"
by(subst int_set_bits_unfold_BIT) simp_all

lemma bin_rest_set_bits [simp]:
  "wf_set_bits_int f \<Longrightarrow> bin_rest (set_bits f) = set_bits (f \<circ> Suc)"
by(subst int_set_bits_unfold_BIT) simp_all

lemma bin_nth_set_bits [simp]:
  "wf_set_bits_int f \<Longrightarrow> bin_nth (set_bits f) m = f m"
proof(induction m arbitrary: f)
  case 0 
  thus ?case by simp
next
  case Suc
  from Suc.IH[of "\<lambda>n. f (Suc n)"] Suc.prems show ?case
    by(simp add: o_def)
qed

lemma set_bits_code [code]: 
  "set_bits = Code.abort (STR ''set_bits is unsupported on type int'') (\<lambda>_. set_bits :: _ \<Rightarrow> int)"
by simp

lemma msb_conv_bin_sign: "msb x \<longleftrightarrow> bin_sign x = -1"
by(simp add: bin_sign_def not_le msb_int_def)

lemma msb_BIT [simp]: "msb (x BIT b) = msb x"
by(simp add: msb_int_def)

lemma msb_bin_rest [simp]: "msb (bin_rest x) = msb x"
by(simp add: msb_int_def)

lemma int_msb_and [simp]: "msb ((x :: int) AND y) \<longleftrightarrow> msb x \<and> msb y"
by(simp add: msb_int_def)

lemma int_msb_or [simp]: "msb ((x :: int) OR y) \<longleftrightarrow> msb x \<or> msb y"
by(simp add: msb_int_def)

lemma int_msb_xor [simp]: "msb ((x :: int) XOR y) \<longleftrightarrow> msb x \<noteq> msb y"
by(simp add: msb_int_def)

lemma int_msb_not [simp]: "msb (NOT (x :: int)) \<longleftrightarrow> \<not> msb x"
by(simp add: msb_int_def not_less)

lemma msb_shiftl [simp]: "msb ((x :: int) << n) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_shiftr [simp]: "msb ((x :: int) >> r) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_bin_sc [simp]: "msb (bin_sc n b x) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign)

lemma msb_set_bit [simp]: "msb (set_bit (x :: int) n b) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign set_bit_int_def)

lemma msb_0 [simp]: "msb (0 :: int) = False"
by(simp add: msb_int_def)

lemma msb_1 [simp]: "msb (1 :: int) = False"
by(simp add: msb_int_def)

lemma msb_numeral [simp]:
  "msb (numeral n :: int) = False"
  "msb (- numeral n :: int) = True"
by(simp_all add: msb_int_def)

section {* Bit list operations implemented by bitwise operations *}

lemma bin_rest_code [code]: "bin_rest i = i >> 1"
by(simp add: bin_rest_def shiftr_int_def)

lemma sbintrunc_code [code]:
  "sbintrunc n bin =
  (let bin' = bin AND bin_mask (n + 1)
   in if bin' !! n then bin' - (2 << n) else bin')"
proof(induct n arbitrary: bin)
  case 0 thus ?case
    by (simp add: bitval_bin_last [symmetric])
next
  case (Suc n)
  thus ?case by(cases bin rule: bin_exhaust)(simp add: Let_def minus_BIT_0)
qed

text {* 
  Use this function to convert numeral @{typ integer}s quickly into @{typ int}s.
  By default, it works only for symbolic evaluation; normally generated code raises
  an exception at run-time. If theory @{text Code_Target_Bits_Int} is imported, 
  it works again, because then @{typ int} is implemented in terms of @{typ integer}
  even for symbolic evaluation.
*}

definition int_of_integer_symbolic :: "integer \<Rightarrow> int"
where "int_of_integer_symbolic = int_of_integer"

lemma int_of_integer_symbolic_aux_code [code nbe]:
  "int_of_integer_symbolic 0 = 0"
  "int_of_integer_symbolic (Code_Numeral.Pos n) = Int.Pos n"
  "int_of_integer_symbolic (Code_Numeral.Neg n) = Int.Neg n"
by(simp_all add: int_of_integer_symbolic_def)

code_identifier
  code_module More_Bits_Int \<rightharpoonup>
  (SML) Bit_Int and (OCaml) Bit_Int and (Haskell) Bit_Int and (Scala) Bit_Int
| code_module Bits_Int \<rightharpoonup>
  (SML) Bit_Int and (OCaml) Bit_Int and (Haskell) Bit_Int and (Scala) Bit_Int
| code_module Bits \<rightharpoonup>
  (SML) Bit_Int and (OCaml) Bit_Int and (Haskell) Bit_Int and (Scala) Bit_Int

end
