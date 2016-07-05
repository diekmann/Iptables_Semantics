(*  Title:      Bits_Integer.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* Bit operations for target language integers *}

theory Bits_Integer imports
  More_Bits_Int
begin

lemmas [transfer_rule] =
  identity_quotient
  fun_quotient
  Quotient_integer[folded integer.pcr_cr_eq]

lemma undefined_transfer:
  assumes "Quotient R Abs Rep T"
  shows "T (Rep undefined) undefined"
using assms unfolding Quotient_alt_def by blast

bundle undefined_transfer = undefined_transfer[transfer_rule]

section {* More lemmas about @{typ integer}s *}

context
includes integer.lifting
begin

lemma bitval_integer_transfer [transfer_rule]:
  "(rel_fun op = pcr_integer) of_bool of_bool"
by(auto simp add: of_bool_def integer.pcr_cr_eq cr_integer_def split: bit.split)

lemma integer_of_nat_less_0_conv [simp]: "\<not> integer_of_nat n < 0"
by(transfer) simp

lemma int_of_integer_pow: "int_of_integer (x ^ n) = int_of_integer x ^ n"
by(induct n) simp_all

lemma pow_integer_transfer [transfer_rule]:
  "(rel_fun pcr_integer (rel_fun op = pcr_integer)) op ^ op ^"
by(auto 4 3 simp add: integer.pcr_cr_eq cr_integer_def int_of_integer_pow)

lemma sub1_lt_0_iff [simp]: "Code_Numeral.sub n num.One < 0 \<longleftrightarrow> False"
by(cases n)(simp_all add: Code_Numeral.sub_code)

lemma nat_of_integer_numeral [simp]: "nat_of_integer (numeral n) = numeral n"
by transfer simp

lemma nat_of_integer_sub1_conv_pred_numeral [simp]:
  "nat_of_integer (Code_Numeral.sub n num.One) = pred_numeral n"
by(cases n)(simp_all add: Code_Numeral.sub_code)

lemma nat_of_integer_1 [simp]: "nat_of_integer 1 = 1"
by transfer simp

lemma dup_1 [simp]: "Code_Numeral.dup 1 = 2"
by transfer simp

section {* Bit operations on @{typ integer} *}

text {* Bit operations on @{typ integer} are the same as on @{typ int} *}

lift_definition bin_rest_integer :: "integer \<Rightarrow> integer" is bin_rest .
lift_definition bin_last_integer :: "integer \<Rightarrow> bool" is bin_last .
lift_definition Bit_integer :: "integer \<Rightarrow> bool \<Rightarrow> integer" is Bit .

end

instantiation integer :: bitss begin
context includes integer.lifting begin

lift_definition bitAND_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitAND" .
lift_definition bitOR_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitOR" .
lift_definition bitXOR_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitXOR" .
lift_definition bitNOT_integer :: "integer \<Rightarrow> integer" is "bitNOT" .

lift_definition test_bit_integer :: "integer \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition lsb_integer :: "integer \<Rightarrow> bool" is lsb .
lift_definition set_bit_integer :: "integer \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> integer" is set_bit .
lift_definition set_bits_integer :: "(nat \<Rightarrow> bool) \<Rightarrow> integer" is set_bits .
lift_definition shiftl_integer :: "integer \<Rightarrow> nat \<Rightarrow> integer" is shiftl .
lift_definition shiftr_integer :: "integer \<Rightarrow> nat \<Rightarrow> integer" is shiftr .

lift_definition msb_integer :: "integer \<Rightarrow> bool" is msb .
instance ..
end
end

abbreviation (input) wf_set_bits_integer
where "wf_set_bits_integer \<equiv> wf_set_bits_int"

section {* Target language implementations *}

text {* 
  Unfortunately, this is not straightforward,
  because these API functions have different signatures and preconditions on the parameters:

  \begin{description}
  \item[Standard ML] Shifts in IntInf are given as word, but not IntInf.
  \item[Haskell] In the Data.Bits.Bits type class, shifts and bit indices are given as Int rather than Integer.
  \item[OCaml] AND, XOR and OR in Big\_int accept only positive integers.
  \end{description}

  Additional constants take only parameters of type @{typ integer} rather than @{typ nat}
  and check the preconditions as far as possible (e.g., being non-negative) in a portable way.
  Manual implementations inside code\_printing perform the remaining range checks and convert 
  these @{typ integer}s into the right type.

  For normalisation by evaluation, we derive custom code equations, because NBE
  does not know these code\_printing serialisations and would otherwise loop.
*}

code_identifier code_module Bits_Integer \<rightharpoonup>
  (SML) Bit_Int and (OCaml) Bit_Int and (Haskell) Bit_Int and (Scala) Bit_Int

code_printing code_module Bits_Integer \<rightharpoonup> (SML)
{*structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)*}
code_reserved SML Bits_Integer

code_printing code_module Data_Bits \<rightharpoonup> (Haskell)
{*import qualified Data.Bits;

{-
  The ...Bounded functions assume that the Integer argument for the shift 
  or bit index fits into an Int, is non-negative and (for types of fixed bit width)
  less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitUnbounded x b
  | b <= toInteger (Prelude.maxBound :: Int) = Data.Bits.testBit x (fromInteger b)
  | otherwise = error ("Bit index too large: " ++ show b)
;

testBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitBounded x b = Data.Bits.testBit x (fromInteger b);

setBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitUnbounded x n b
  | n <= toInteger (Prelude.maxBound :: Int) = 
    if b then Data.Bits.setBit x (fromInteger n) else Data.Bits.clearBit x (fromInteger n)
  | otherwise = error ("Bit index too large: " ++ show n)
;

setBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x (fromInteger n);
setBitBounded x n False = Data.Bits.clearBit x (fromInteger n);

shiftlUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftL x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftlBounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlBounded x n = Data.Bits.shiftL x (fromInteger n);

shiftrUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftrUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftR x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Integer -> a;
shiftrBounded x n = Data.Bits.shiftR x (fromInteger n);*}

  and -- {* @{theory Quickcheck_Narrowing} maps @{typ integer} to 
            Haskell's Prelude.Int type instead of Integer. For compatibility
            with the Haskell target, we nevertheless provide bounded and 
            unbounded functions. *}
  (Haskell_Quickcheck)
{*import qualified Data.Bits;

{-
  The functions assume that the Int argument for the shift or bit index is 
  non-negative and (for types of fixed bit width) less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitUnbounded = Data.Bits.testBit;

testBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitBounded = Data.Bits.testBit;

setBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitUnbounded x n True = Data.Bits.setBit x n;
setBitUnbounded x n False = Data.Bits.clearBit x n;

setBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x n;
setBitBounded x n False = Data.Bits.clearBit x n;

shiftlUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlUnbounded = Data.Bits.shiftL;

shiftlBounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlBounded = Data.Bits.shiftL;

shiftrUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftrUnbounded = Data.Bits.shiftR;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Prelude.Int -> a;
shiftrBounded = Data.Bits.shiftR;*}
code_reserved Haskell Data_Bits

code_printing code_module Bits_Integer \<rightharpoonup> (OCaml)
{*module Bits_Integer : sig
  val and_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val or_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftl : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftr : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val test_bit : Big_int.big_int -> Big_int.big_int -> bool
end = struct

let and_pninteger bi1 bi2 =
  Big_int.and_big_int bi1
    (Big_int.xor_big_int
      (Big_int.pred_big_int
        (Big_int.shift_left_big_int Big_int.unit_big_int
           (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
      (Big_int.pred_big_int (Big_int.minus_big_int bi2)));;

let or_pninteger bi1 bi2 =
  Big_int.pred_big_int (Big_int.minus_big_int
    (Big_int.and_big_int
      (Big_int.xor_big_int
         (Big_int.pred_big_int
           (Big_int.shift_left_big_int Big_int.unit_big_int
              (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                   (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
         bi1)
      (Big_int.pred_big_int (Big_int.minus_big_int bi2))));;

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Big_int.shift_left_big_int x (Big_int.int_of_big_int n);;

let shiftr x n = Big_int.shift_right_big_int x (Big_int.int_of_big_int n);;

let test_bit x n = 
  Big_int.eq_big_int 
    (Big_int.extract_big_int x (Big_int.int_of_big_int n) 1) 
    Big_int.unit_big_int

end;; (*struct Bits_Integer*)*}
code_reserved OCaml Bits_Integer

code_printing code_module Bits_Integer \<rightharpoonup> (Scala)
{*object Bits_Integer {

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt) 
  else
    sys.error("Bit index too large: " + n.toString)

} /* object Bits_Integer */*}

code_printing
  constant "bitAND :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.andb ((_),/ (_))" and
  (Haskell) "((Data'_Bits..&.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..&.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 3 "&"
| constant "bitOR :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.orb ((_),/ (_))" and
  (Haskell) "((Data'_Bits..|.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..|.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 1 "|"
| constant "bitXOR :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.xorb ((_),/ (_))" and
  (Haskell) "(Data'_Bits.xor :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.xor :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 2 "^"
| constant "bitNOT :: integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.notb" and
  (Haskell) "(Data'_Bits.complement :: Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.complement :: Prelude.Int -> Prelude.Int)" and
  (Scala) "_.unary'_~"

code_printing constant bin_rest_integer \<rightharpoonup>
  (SML) "IntInf.div ((_), 2)" and
  (Haskell) "(Data'_Bits.shiftrUnbounded _ 1 :: Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded _ 1 :: Prelude.Int)" and
  (Scala) "_ >> 1" and
  (OCaml) "Big'_int.shift'_right'_big'_int _ 1"

context
includes integer.lifting
begin

lemma bitNOT_integer_code [code]:
  fixes i :: integer shows
  "NOT i = - i - 1"
by transfer(simp add: int_not_def)

lemma bin_rest_integer_code [code nbe]:
  "bin_rest_integer i = i div 2"
by transfer(simp add: bin_rest_def)

lemma bin_last_integer_code [code]:
  "bin_last_integer i \<longleftrightarrow> i AND 1 \<noteq> 0"
by transfer(rule bin_last_conv_AND)

lemma bin_last_integer_nbe [code nbe]:
  "bin_last_integer i \<longleftrightarrow> i mod 2 \<noteq> 0"
by transfer(simp add: bin_last_def)

lemma bitval_bin_last_integer [code_unfold]:
  "of_bool (bin_last_integer i) = i AND 1"
by transfer(rule bitval_bin_last)

end

definition integer_test_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool"
where [code del]: "integer_test_bit x n = (if n < 0 then undefined x n else x !! nat_of_integer n)"

lemma test_bit_integer_code [code]:
  "x !! n \<longleftrightarrow> integer_test_bit x (integer_of_nat n)"
by(simp add: integer_test_bit_def)

lemma integer_test_bit_code [code]:
  "integer_test_bit x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_test_bit 0 0 = False"
  "integer_test_bit 0 (Code_Numeral.Pos n) = False"
  "integer_test_bit (Code_Numeral.Pos num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Pos num.One)      (Code_Numeral.Pos n') = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Neg num.One)      (Code_Numeral.Pos n') = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg (n + num.One)) (Code_Numeral.sub n' num.One)"
by(simp_all add: integer_test_bit_def test_bit_integer_def)

code_printing constant integer_test_bit \<rightharpoonup>
  (SML) "Bits'_Integer.test'_bit" and
  (Haskell) "(Data'_Bits.testBitUnbounded :: Integer -> Integer -> Bool)" and
  (Haskell_Quickcheck) "(Data'_Bits.testBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool)" and
  (OCaml) "Bits'_Integer.test'_bit" and
  (Scala) "Bits'_Integer.testBit"

context
includes integer.lifting
begin

lemma lsb_integer_code [code]:
  fixes x :: integer shows
  "lsb x = x !! 0"
by transfer(simp add: lsb_int_def)

definition integer_set_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> integer"
where [code del]: "integer_set_bit x n b = (if n < 0 then undefined x n b else set_bit x (nat_of_integer n) b)"

lemma set_bit_integer_code [code]:
  "set_bit x i b = integer_set_bit x (integer_of_nat i) b"
by(simp add: integer_set_bit_def)

lemma set_bit_integer_conv_masks: 
  fixes x :: integer shows
  "set_bit x i b = (if b then x OR (1 << i) else x AND NOT (1 << i))"
by transfer(simp add: int_set_bit_conv_ops)

end

code_printing constant integer_set_bit \<rightharpoonup>
  (SML) "Bits'_Integer.set'_bit" and
  (Haskell) "(Data'_Bits.setBitUnbounded :: Integer -> Integer -> Bool -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.setBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool -> Prelude.Int)" and
  (Scala) "Bits'_Integer.setBit"

text {* 
  OCaml.Big\_int does not have a method for changing an individual bit, so we emulate that with masks.
  We prefer an Isabelle implementation, because this then takes care of the signs for AND and OR.
*}
lemma integer_set_bit_code [code]:
  "integer_set_bit x n b =
  (if n < 0 then undefined x n b else
   if b then x OR (1 << nat_of_integer n)
   else x AND NOT (1 << nat_of_integer n))"
by(auto simp add: integer_set_bit_def set_bit_integer_conv_masks)

lemma set_bits_code [code]:
  "set_bits = Code.abort (STR ''set_bits is unsupported on type integer'') (\<lambda>_. set_bits :: _ \<Rightarrow> integer)"
by simp

definition integer_shiftl :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftl x n = (if n < 0 then undefined x n else x << nat_of_integer n)"

lemma shiftl_integer_code [code]: 
  fixes x :: integer shows
  "x << n = integer_shiftl x (integer_of_nat n)"
by(auto simp add: integer_shiftl_def)

context
includes integer.lifting
begin

lemma shiftl_integer_conv_mult_pow2:
  fixes x :: integer shows
  "x << n = x * 2 ^ n"
by transfer(simp add: shiftl_int_def)

lemma integer_shiftl_code [code]:
  "integer_shiftl x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftl x 0 = x"
  "integer_shiftl x (Code_Numeral.Pos n) = integer_shiftl (Code_Numeral.dup x) (Code_Numeral.sub n num.One)"
  "integer_shiftl 0 (Code_Numeral.Pos n) = 0"
  by (simp_all add: integer_shiftl_def shiftl_integer_def shiftl_int_def numeral_eq_Suc)
    (transfer, simp)

end

code_printing constant integer_shiftl \<rightharpoonup>
  (SML) "Bits'_Integer.shiftl" and
  (Haskell) "(Data'_Bits.shiftlUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftlUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (OCaml) "Bits'_Integer.shiftl" and
  (Scala) "Bits'_Integer.shiftl"

definition integer_shiftr :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftr x n = (if n < 0 then undefined x n else x >> nat_of_integer n)"

lemma shiftr_integer_conv_div_pow2: 
  includes integer.lifting fixes x :: integer shows
  "x >> n = x div 2 ^ n"
by transfer(simp add: shiftr_int_def)

lemma shiftr_integer_code [code]:
  fixes x :: integer shows
  "x >> n = integer_shiftr x (integer_of_nat n)"
by(auto simp add: integer_shiftr_def)

code_printing constant integer_shiftr \<rightharpoonup>
  (SML) "Bits'_Integer.shiftr" and
  (Haskell) "(Data'_Bits.shiftrUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (OCaml) "Bits'_Integer.shiftr" and
  (Scala) "Bits'_Integer.shiftr"

lemma integer_shiftr_code [code]:
  "integer_shiftr x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftr x 0 = x"
  "integer_shiftr 0 (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos num.One) (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos (num.Bit0 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Pos (num.Bit1 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg num.One) (Code_Numeral.Pos n) = -1"
  "integer_shiftr (Code_Numeral.Neg (num.Bit0 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Neg n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg (num.Bit1 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Neg (Num.inc n')) (Code_Numeral.sub n num.One)"
by(simp_all add: integer_shiftr_def shiftr_integer_def)

context
includes integer.lifting
begin

lemma Bit_integer_code [code]:
  "Bit_integer i False = i << 1"
  "Bit_integer i True = (i << 1) + 1"
by(transfer, simp add: Bit_def shiftl_int_def)+

lemma msb_integer_code [code]:
  "msb (x :: integer) \<longleftrightarrow> x < 0"
by transfer(simp add: msb_int_def)

subsection {* OCaml implementation for @{text "AND"}, @{text "OR"}, and @{text "XOR"} *}

definition and_pint :: "int \<Rightarrow> int \<Rightarrow> int" where
  "and_pint i j = 
  (if i < 0 \<or> j < 0 then int_of_integer (undefined (integer_of_int i) (integer_of_int j))
   else i AND j)"

definition or_pint :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "or_pint i j = 
   (if i < 0 \<or> j < 0 then int_of_integer (undefined (integer_of_int i) (integer_of_int j))
    else i OR j)"

definition xor_pint :: "int \<Rightarrow> int \<Rightarrow> int" where
  "xor_pint i j = 
  (if i < 0 \<or> j < 0 then int_of_integer (undefined (integer_of_int i) (integer_of_int j))
   else i XOR j)"

lift_definition and_pinteger :: "integer \<Rightarrow> integer \<Rightarrow> integer" is and_pint .
lift_definition or_pinteger :: "integer \<Rightarrow> integer \<Rightarrow> integer" is or_pint .
lift_definition xor_pinteger :: "integer \<Rightarrow> integer \<Rightarrow> integer" is xor_pint .

end

code_printing
  constant and_pinteger \<rightharpoonup> (OCaml) "Big'_int.and'_big'_int"
| constant or_pinteger  \<rightharpoonup> (OCaml) "Big'_int.or'_big'_int"
| constant xor_pinteger \<rightharpoonup> (OCaml) "Big'_int.xor'_big'_int"

context
includes integer.lifting natural.lifting
begin

lemma and_pinteger_unfold: 
  "and_pinteger i j = (if i < 0 \<or> j < 0 then undefined i j else i AND j)"
including undefined_transfer by transfer(simp add: and_pint_def)

lemma or_pinteger_unfold:
  "or_pinteger i j = (if i < 0 \<or> j < 0 then undefined i j else i OR j)"
including undefined_transfer by transfer(simp add: or_pint_def)

lemma xor_pinteger_unfold:
  "xor_pinteger i j = (if i < 0 \<or> j < 0 then undefined i j else i XOR j)"
including undefined_transfer by transfer(simp add: xor_pint_def)

lemma xor_OCaml_code [code]:
  fixes i :: integer shows
  "i XOR j =
  (if i < 0 then 
     if j < 0 then
        xor_pinteger (NOT i) (NOT j)
     else
        NOT (xor_pinteger (NOT i) j)
   else if j < 0 then
     NOT (xor_pinteger i (NOT j))
   else xor_pinteger i j)"
by transfer(simp add: int_xor_not xor_pint_def)

lemma and_pinteger_code [code]:
  "and_pinteger (Code_Numeral.Neg n) j = undefined (Code_Numeral.Neg n) j"
  "and_pinteger i (Code_Numeral.Neg n) = undefined i (Code_Numeral.Neg n)"
  "and_pinteger 0 0 = 0"
  "and_pinteger (Code_Numeral.Pos n) 0 = 0"
  "and_pinteger 0 (Code_Numeral.Pos n) = 0"
  "and_pinteger (Code_Numeral.Pos m) (Code_Numeral.Pos n) = (case bitAND_num m n of None \<Rightarrow> 0 | Some n' \<Rightarrow> Code_Numeral.Pos n')"
including undefined_transfer by(transfer, simp add: and_pint_def Bit_def int_and_code[unfolded Int.Pos_def])+

lemma or_pinteger_code [code]:
  "or_pinteger (Code_Numeral.Neg n) j = undefined (Code_Numeral.Neg n) j"
  "or_pinteger i (Code_Numeral.Neg n) = undefined i (Code_Numeral.Neg n)"
  "or_pinteger 0 0 = 0"
  "or_pinteger (Code_Numeral.Pos n) 0 = (Code_Numeral.Pos n)"
  "or_pinteger 0 (Code_Numeral.Pos n) = (Code_Numeral.Pos n)"
  "or_pinteger (Code_Numeral.Pos m) (Code_Numeral.Pos n) = Code_Numeral.Pos (bitOR_num m n)"
including undefined_transfer by(transfer, simp add: or_pint_def Bit_def int_or_code[unfolded Int.Pos_def])+

lemma xor_pinteger_code [code]:
  "xor_pinteger (Code_Numeral.Neg n) j = undefined (Code_Numeral.Neg n) j"
  "xor_pinteger i (Code_Numeral.Neg n) = undefined i (Code_Numeral.Neg n)"
  "xor_pinteger 0 0 = 0"
  "xor_pinteger (Code_Numeral.Pos n) 0 = (Code_Numeral.Pos n)"
  "xor_pinteger 0 (Code_Numeral.Pos n) = (Code_Numeral.Pos n)"
  "xor_pinteger (Code_Numeral.Pos n) (Code_Numeral.Pos m) = (case bitXOR_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Code_Numeral.Pos n')"
including undefined_transfer by(transfer, simp add: xor_pint_def Bit_def int_xor_code[unfolded Int.Pos_def])+

text {* 
  If one argument is positive and the other negative, AND and OR
  cannot be expressed with XOR/NOT and only positive arguments.
  To handle this case, we define @{term "and_pninteger"} and @{term "or_pninteger"}
  and implement them manually in the code\_include Bits\_Integer.
  The following proves that the implementation is correct.
*}

definition and_pnint :: "int \<Rightarrow> int \<Rightarrow> int" where
  "and_pnint i j = 
   (if i \<ge> 0 \<and> j < 0 then i AND j
    else int_of_integer (undefined (integer_of_int i) (integer_of_int j)))"

definition or_pnint :: "int \<Rightarrow> int \<Rightarrow> int" where
  "or_pnint i j = 
   (if i \<ge> 0 \<and> j < 0 then i OR j
    else int_of_integer (undefined (integer_of_int i) (integer_of_int j)))"

fun log2 :: "int => nat" where
  "log2 i = (if i < 0 then undefined else if i = 0 then 0 else log2 (i div 2) + 1)"

lift_definition and_pninteger :: "integer \<Rightarrow> integer \<Rightarrow> integer" is and_pnint .
lift_definition or_pninteger :: "integer \<Rightarrow> integer \<Rightarrow> integer" is or_pnint .
lift_definition log2_integer :: "integer \<Rightarrow> natural" is log2 .
lift_definition bin_mask_integer :: "natural \<Rightarrow> integer" is bin_mask .

end

code_printing 
  constant and_pninteger \<rightharpoonup> (OCaml) "Bits'_Integer.and'_pninteger"
| constant or_pninteger  \<rightharpoonup> (OCaml) "Bits'_Integer.or'_pninteger"

context
includes integer.lifting natural.lifting
begin

lemma and_pninteger_unfold:
  "and_pninteger i j = (if i \<ge> 0 \<and> j < 0 then i AND j else undefined i j)"
including undefined_transfer by transfer(simp add: and_pnint_def)

lemma and_pninteger_code [code]:
  "and_pninteger (Code_Numeral.Neg n) j = undefined (Code_Numeral.Neg n) j"
  "and_pninteger i 0 = undefined i (0 :: integer)"
  "and_pninteger i (Code_Numeral.Pos n) = undefined i (Code_Numeral.Pos n)"
  "and_pninteger 0 (Code_Numeral.Neg n) = 0"
  "and_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg num.One) = Code_Numeral.Pos n"
  "and_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg (num.Bit0 m)) = Code_Numeral.sub (bitORN_num (Num.BitM m) n) num.One"
  "and_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg (num.Bit1 m)) = Code_Numeral.sub (bitORN_num (num.Bit0 m) n) num.One"
including undefined_transfer by(transfer, simp add: and_pnint_def Bit_def int_and_code[unfolded Int.Pos_def Int.Neg_def])+

lemma or_pninteger_unfold:
  "or_pninteger i j = (if i \<ge> 0 \<and> j < 0 then i OR j else undefined i j)"
including undefined_transfer by transfer(simp add: or_pnint_def)

lemma or_pninteger_code [code]:
  "or_pninteger (Code_Numeral.Neg n) j = undefined (Code_Numeral.Neg n) j"
  "or_pninteger i 0 = undefined i (0 :: integer)"
  "or_pninteger i (Code_Numeral.Pos n) = undefined i (Code_Numeral.Pos n)"
  "or_pninteger 0 (Code_Numeral.Neg n) = Code_Numeral.Neg n"

  "or_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg num.One) = -1"
  "or_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg (num.Bit0 m)) = (case bitANDN_num (Num.BitM m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Code_Numeral.Neg (Num.inc n'))"
  "or_pninteger (Code_Numeral.Pos n) (Code_Numeral.Neg (num.Bit1 m)) = (case bitANDN_num (num.Bit0 m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Code_Numeral.Neg (Num.inc n'))"
including undefined_transfer by(transfer, simp add: or_pnint_def Bit_def int_or_code[unfolded Int.Pos_def Int.Neg_def])+

lemma integer_and_OCaml_code [code]:
  "i AND j = 
  (if i \<ge> 0 then
     if j \<ge> 0 then
       and_pinteger i j
     else and_pninteger i j
   else if j < 0 then
     NOT (or_pinteger (NOT i) (NOT j))
   else and_pninteger j i)"
by transfer(simp add: and_pnint_def and_pint_def or_pint_def bbw_not_dist int_and_comm)

lemma integer_or_OCaml_code [code]:
  "i OR j = 
  (if i \<ge> 0 then
     if j \<ge> 0 then
       or_pinteger i j
     else or_pninteger i j
   else if j < 0 then
     NOT (and_pinteger (NOT i) (NOT j))
   else or_pninteger j i)"
by transfer(simp add: or_pnint_def and_pint_def or_pint_def bbw_not_dist int_or_comm)

lemma integer_or_unfold:
  fixes x y :: integer shows
  "x OR y = NOT (NOT x AND NOT y)"
by(transfer)(simp add: int_or_def)

lemma bitAND_integer_unfold:
  "x AND y =
   (if x = 0 then 0
    else if x = -1 then y
    else Bit_integer (bin_rest_integer x AND bin_rest_integer y) (bin_last_integer x \<and> bin_last_integer y))"
by transfer(rule bitAND_int.simps)

lemma log2_simps [simp]:
  "log2 0 = 0"
  "log2 1 = 1"
  "n < 0 \<Longrightarrow> log2 n = undefined"
by(simp_all)

declare log2.simps [simp del]

lemma log2_le_plus1: "0 \<le> i \<Longrightarrow> log2 i \<le> log2 (i + 1)"
proof(induct i rule: log2.induct)
  case (1 i) 
  moreover have "i mod 2 = 0 \<or> i mod 2 = 1" by arith
  ultimately show ?case by(subst (1 2) log2.simps)(auto, simp_all add: zdiv_zadd1_eq)
qed

lemma log2_mono: 
  assumes x: "0 \<le> x" and xy: "x \<le> y"
  shows "log2 x \<le> log2 y"
using xy
proof(induct n\<equiv>"nat (y - x)" arbitrary: y)
  case 0 thus ?case by simp
next
  case (Suc n)
  from `Suc n = nat (y - x)` Suc.prems
  have "n = nat (y - 1 - x)" "x \<le> y - 1" by simp_all
  hence "log2 x \<le> log2 (y - 1)" by(rule Suc)
  also have "\<dots> \<le> log2 y" using log2_le_plus1[of "y - 1"] x `x \<le> y - 1` by simp
  finally show ?case .
qed

lemma log2_eq_0 [simp]:
  "i \<ge> 0 \<Longrightarrow> log2 i = 0 \<longleftrightarrow> i = 0"
by(subst log2.simps) force

lemma pow2_log2_gt: "i \<ge> 0 \<Longrightarrow> i < 2 ^ log2 i"
proof(induct i rule: log2.induct)
  case (1 i)
  hence IH: "i div 2 < 2 ^ log2 (i div 2)"
    by (metis (full_types) div_pos_pos_trivial order_less_imp_not_less order_less_le_trans pos_imp_zdiv_nonneg_iff zero_less_numeral zero_less_power)
  show ?case
  proof(cases "i = 0")
    case True thus ?thesis by simp
  next
    case False with `0 \<le> i` have "i > 0" by simp
    thus ?thesis using IH by(subst log2.simps)(simp add: nat_add_distrib)
  qed
qed

lemma log2_bin_rest [simp]: "i > 0 \<Longrightarrow> log2 (bin_rest i) = log2 i - 1"
by(subst (2) log2.simps)(simp add: bin_rest_def)

lemma bin_mask_XOR_conv_and_not: "\<lbrakk> n \<ge> log2 i; i \<ge> 0 \<rbrakk> \<Longrightarrow> bin_mask n XOR i = bin_mask n AND NOT i"
proof(induct n arbitrary: i)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc(1)[of "bin_rest i"] `0 \<le> i` Suc(2)
  show ?case by(cases "i = 0")(auto intro: bin_rl_eqI)
qed

lemma int_and_mask: "\<lbrakk> n \<ge> log2 i; i \<ge> 0 \<rbrakk> \<Longrightarrow> i AND bin_mask n = i"
proof(induct n arbitrary: i)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc(1)[of "bin_rest i"] `0 \<le> i` Suc(2)
  show ?case by(cases "i = 0")(auto intro: bin_rl_eqI)
qed


lemma and_pnint:
  assumes x: "x \<ge> 0" and y: "y < 0" 
  and kx: "k \<ge> log2 x" and ky: "k \<ge> log2 (- y)"
  shows "and_pnint x y = and_pint x (xor_pint (bin_mask k) (- y - 1))"
proof -
  from y have "log2 (- y - 1) \<le> log2 (- y)" by(auto intro: log2_mono)
  with ky have "log2 (NOT y) \<le> k" by(simp add: int_not_def)
  moreover from y have "0 \<le> NOT y" by(simp add: int_not_def)
  ultimately have "bin_mask k XOR NOT y = bin_mask k AND NOT NOT y"
    by(rule bin_mask_XOR_conv_and_not)
  moreover
  have "x AND y = (x AND bin_mask k) AND y" using kx x
    by(rule arg_cong[OF int_and_mask, symmetric])
  ultimately show ?thesis using x y bin_mask_ge0[of "k"]
    unfolding and_pnint_def and_pint_def
    by(simp add: int_and_assoc int_not_def xor_pint_def)
qed

lemma and_pninteger:  -- {* justification for OCaml implementation of @{term andpnint} *}
  "\<lbrakk> x \<ge> 0; y < 0; k \<ge> log2_integer x; k \<ge> log2_integer (- y) \<rbrakk> 
  \<Longrightarrow> and_pninteger x y = and_pinteger x (xor_pinteger (bin_mask_integer k) (- y - 1))"
by transfer(rule and_pnint)


lemma or_pnint:
  assumes x: "x \<ge> 0" and y: "y < 0" 
  and kx: "k \<ge> log2 x" and ky: "k \<ge> log2 (- y)"
  shows "or_pnint x y = - (and_pint (xor_pint (bin_mask k) x) (- y - 1)) - 1"
proof -
  from y have "log2 (- y - 1) \<le> log2 (- y)" by(auto intro: log2_mono)
  with ky have "log2 (NOT y) \<le> k" by(simp add: int_not_def)
  moreover from y have "0 \<le> NOT y" by(simp add: int_not_def)
  ultimately have "bin_mask k XOR NOT y = bin_mask k AND NOT NOT y"
    by(rule bin_mask_XOR_conv_and_not)
  moreover have "bin_mask k XOR x \<ge> 0" using x bin_mask_ge0[of k] by simp
  ultimately show ?thesis using x y kx `log2 (NOT y) \<le> k` `0 \<le> NOT y`
    by(simp add: or_pnint_def int_or_def and_pint_def int_not_def xor_pint_def bin_mask_XOR_conv_and_not int_and_assoc)
      (subst bbw_lcs(1), subst (3) int_and_comm, simp add: int_and_mask)
qed

lemma or_pinteger: -- {* justification for OCaml implementation of @{term or_pnint} *}
  "\<lbrakk>  x \<ge> 0; y < 0; k \<ge> log2_integer x; k \<ge> log2_integer (- y) \<rbrakk>
  \<Longrightarrow> or_pninteger x y = - (and_pinteger (xor_pinteger (bin_mask_integer k) x) (- y - 1)) - 1"
by(transfer)(rule or_pnint)

end

hide_const (open)
  log2 and_pint and_pnint or_pint or_pnint xor_pint
  log2_integer bin_mask_integer and_pinteger and_pninteger or_pinteger or_pninteger xor_pinteger

section {* Test code generator setup *}

definition bit_integer_test :: "bool" where
  "bit_integer_test =
  (([ -1 AND 3, 1 AND -3, 3 AND 5, -3 AND (- 5)
    , -3 OR 1, 1 OR -3, 3 OR 5, -3 OR (- 5)
    , NOT 1, NOT (- 3)
    , -1 XOR 3, 1 XOR (- 3), 3 XOR 5, -5 XOR (- 3)
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , 1 << 2, -1 << 3
    , 100 >> 3, -100 >> 3] :: integer list)
  = [ 3, 1, 1, -7
    , -3, -3, 7, -1
    , -2, 2
    , -4, -4, 6, 6
    , 21, -1, 4, -7
    , 4, -8
    , 12, -13] \<and>
    [ (5 :: integer) !! 4, (5 :: integer) !! 2, (-5 :: integer) !! 4, (-5 :: integer) !! 2
    , lsb (5 :: integer), lsb (4 :: integer), lsb (-1 :: integer), lsb (-2 :: integer), 
      msb (5 :: integer), msb (0 :: integer), msb (-1 :: integer), msb (-2 :: integer)]
  = [ False, True, True, False,
      True, False, True, False,
      False, False, True, True])"

export_code bit_integer_test checking SML Haskell? Haskell_Quickcheck? OCaml? Scala

notepad begin
have bit_integer_test by eval
have bit_integer_test by normalization
have bit_integer_test by code_simp
end
ML_val {* val true = @{code bit_integer_test} *}

lemma "x AND y = x OR (y :: integer)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: integer) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
oops

lemma "(f :: integer \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

hide_const bit_integer_test
hide_fact bit_integer_test_def

end
