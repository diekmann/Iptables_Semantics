(*  Title:      Uint32.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter {* Unsigned words of 32 bits *}

theory Uint32 imports
  Word_Misc
  Bits_Integer
begin

declare prod.Quotient[transfer_rule]

section {* Type definition and primitive operations *}

typedef uint32 = "UNIV :: 32 word set" .. 

setup_lifting type_definition_uint32

text {* Use an abstract type for code generation to disable pattern matching on @{term Abs_uint32}. *}
declare Rep_uint32_inverse[code abstype]

declare Quotient_uint32[transfer_rule]

instantiation uint32 :: "{neg_numeral, Divides.div, comm_monoid_mult, comm_ring}" begin
lift_definition zero_uint32 :: uint32 is "0 :: 32 word" .
lift_definition one_uint32 :: uint32 is "1" .
lift_definition plus_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "op + :: 32 word \<Rightarrow> _" .
lift_definition minus_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "op -" .
lift_definition uminus_uint32 :: "uint32 \<Rightarrow> uint32" is uminus .
lift_definition times_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "op *" .
lift_definition divide_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "op div" .
lift_definition mod_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "op mod" .
instance by standard (transfer, simp add: algebra_simps)+
end

instantiation uint32 :: linorder begin
lift_definition less_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> bool" is "op <" .
lift_definition less_eq_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> bool" is "op \<le>" .
instance by standard (transfer, simp add: less_le_not_le linear)+
end

lemmas [code] = less_uint32.rep_eq less_eq_uint32.rep_eq

instantiation uint32 :: bitss begin
lift_definition bitNOT_uint32 :: "uint32 \<Rightarrow> uint32" is bitNOT .
lift_definition bitAND_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is bitAND .
lift_definition bitOR_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is bitOR .
lift_definition bitXOR_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is bitXOR .
lift_definition test_bit_uint32 :: "uint32 \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition set_bit_uint32 :: "uint32 \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint32" is set_bit .
lift_definition set_bits_uint32 :: "(nat \<Rightarrow> bool) \<Rightarrow> uint32" is "set_bits" .
lift_definition lsb_uint32 :: "uint32 \<Rightarrow> bool" is lsb .
lift_definition shiftl_uint32 :: "uint32 \<Rightarrow> nat \<Rightarrow> uint32" is shiftl .
lift_definition shiftr_uint32 :: "uint32 \<Rightarrow> nat \<Rightarrow> uint32" is shiftr .
lift_definition msb_uint32 :: "uint32 \<Rightarrow> bool" is msb .
instance ..
end

lemmas [code] = test_bit_uint32.rep_eq lsb_uint32.rep_eq msb_uint32.rep_eq

instantiation uint32 :: equal begin
lift_definition equal_uint32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> bool" is "equal_class.equal" .
instance by standard (transfer, simp add: equal_eq)
end

lemmas [code] = equal_uint32.rep_eq

instantiation uint32 :: size begin
lift_definition size_uint32 :: "uint32 \<Rightarrow> nat" is "size" .
instance ..
end

lemmas [code] = size_uint32.rep_eq

lift_definition sshiftr_uint32 :: "uint32 \<Rightarrow> nat \<Rightarrow> uint32" (infixl ">>>" 55) is sshiftr .

lift_definition uint32_of_int :: "int \<Rightarrow> uint32" is "word_of_int" .

definition uint32_of_nat :: "nat \<Rightarrow> uint32"
where "uint32_of_nat = uint32_of_int \<circ> int"

lift_definition int_of_uint32 :: "uint32 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint32 :: "uint32 \<Rightarrow> nat" is "unat" .

definition integer_of_uint32 :: "uint32 \<Rightarrow> integer"
where "integer_of_uint32 = integer_of_int o int_of_uint32"

lemma bitval_integer_transfer [transfer_rule]:
  "(rel_fun op = pcr_integer) of_bool of_bool"
by(auto simp add: of_bool_def integer.pcr_cr_eq cr_integer_def split: bit.split)

text {* Use pretty numerals from integer for pretty printing *}

context includes integer.lifting begin

lift_definition Uint32 :: "integer \<Rightarrow> uint32" is "word_of_int" .

lemma Rep_uint32_numeral [simp]: "Rep_uint32 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint32_def Abs_uint32_inverse numeral.simps plus_uint32_def)

lemma numeral_uint32_transfer [transfer_rule]:
  "(rel_fun op = cr_uint32) numeral numeral"
by(auto simp add: cr_uint32_def)

lemma numeral_uint32 [code_unfold]: "numeral n = Uint32 (numeral n)"
by transfer simp

lemma Rep_uint32_neg_numeral [simp]: "Rep_uint32 (- numeral n) = - numeral n"
by(simp only: uminus_uint32_def)(simp add: Abs_uint32_inverse)

lemma neg_numeral_uint32 [code_unfold]: "- numeral n = Uint32 (- numeral n)"
by transfer(simp add: cr_uint32_def)

end

lemma Abs_uint32_numeral [code_post]: "Abs_uint32 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint32_def numeral.simps plus_uint32_def Abs_uint32_inverse)

lemma Abs_uint32_0 [code_post]: "Abs_uint32 0 = 0"
by(simp add: zero_uint32_def)

lemma Abs_uint32_1 [code_post]: "Abs_uint32 1 = 1"
by(simp add: one_uint32_def)

section {* Code setup *}

code_printing code_module Uint32 \<rightharpoonup> (SML)
{*(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)*}
code_reserved SML Uint32

code_printing code_module Uint32 \<rightharpoonup> (Haskell)
{*import qualified Data.Word;
import qualified Data.Int;

type Int32 = Data.Int.Int32;

type Word32 = Data.Word.Word32;*}
code_reserved Haskell Uint32

text {*
  OCaml and Scala provide only signed 32bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
*}
code_printing code_module "Uint32" \<rightharpoonup> (OCaml)
{*module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Big_int.big_int -> bool -> int32
  val shiftl : int32 -> Big_int.big_int -> int32
  val shiftr : int32 -> Big_int.big_int -> int32
  val shiftr_signed : int32 -> Big_int.big_int -> int32
  val test_bit : int32 -> Big_int.big_int -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Big_int.int_of_big_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Big_int.int_of_big_int n);;

let shiftr x n = Int32.shift_right_logical x (Big_int.int_of_big_int n);;

let shiftr_signed x n = Int32.shift_right x (Big_int.int_of_big_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Big_int.int_of_big_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)*}
code_reserved OCaml Uint32

code_printing code_module Uint32 \<rightharpoonup> (Scala)
{*object Uint32 {

def less(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Int, n: BigInt, b: Boolean) : Int =
  if (b)
    x | (1 << n.intValue)
  else
    x & (1 << n.intValue).unary_~

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint32 */*}
code_reserved Scala Uint32

text {*
  OCaml's conversion from Big\_int to int32 demands that the value fits int a signed 32-bit integer.
  The following justifies the implementation.
*}

definition Uint32_signed :: "integer \<Rightarrow> uint32" 
where "Uint32_signed i = (if i < -(0x80000000) \<or> i \<ge> 0x80000000 then undefined Uint32 i else Uint32 i)"

lemma Uint32_code [code]:
  "Uint32 i = 
  (let i' = i AND 0xFFFFFFFF
   in if i' !! 31 then Uint32_signed (i' - 0x100000000) else Uint32_signed i')"
including undefined_transfer integer.lifting unfolding Uint32_signed_def
by transfer(rule word_of_int_via_signed, simp_all add: bin_mask_numeral)

lemma Uint32_signed_code [code abstract]:
  "Rep_uint32 (Uint32_signed i) = 
  (if i < -(0x80000000) \<or> i \<ge> 0x80000000 then Rep_uint32 (undefined Uint32 i) else word_of_int (int_of_integer_symbolic i))"
unfolding Uint32_signed_def Uint32_def int_of_integer_symbolic_def word_of_integer_def
by(simp add: Abs_uint32_inverse)

text {* 
  Avoid @{term Abs_uint32} in generated code, use @{term Rep_uint32'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint32}.

  The new destructor @{term Rep_uint32'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint32} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint32} 
  ([code abstract] equations for @{typ uint32} may use @{term Rep_uint32} because
  these instances will be folded away.)

  To convert @{typ "32 word"} values into @{typ uint32}, use @{term "Abs_uint32'"}.
*}

definition Rep_uint32' where [simp]: "Rep_uint32' = Rep_uint32"

lemma Rep_uint32'_transfer [transfer_rule]:
  "rel_fun cr_uint32 op = (\<lambda>x. x) Rep_uint32'"
unfolding Rep_uint32'_def by(rule uint32.rep_transfer)

lemma Rep_uint32'_code [code]: "Rep_uint32' x = (BITS n. x !! n)"
by transfer simp

lift_definition Abs_uint32' :: "32 word \<Rightarrow> uint32" is "\<lambda>x :: 32 word. x" .

lemma Abs_uint32'_code [code]:
  "Abs_uint32' x = Uint32 (integer_of_int (uint x))"
including integer.lifting by transfer simp

lemma [code, code del]: "term_of_class.term_of = (term_of_class.term_of :: uint32 \<Rightarrow> _)" ..

lemma term_of_uint32_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" 
  shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint32.Abs_uint32'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]]], TR (STR ''Uint32.uint32'') []]))
       (term_of_class.term_of (Rep_uint32' x))"
by(simp add: term_of_anything)

code_printing
  type_constructor uint32 \<rightharpoonup>
  (SML) "Word32.word" and
  (Haskell) "Uint32.Word32" and
  (OCaml) "int32" and
  (Scala) "Int" and
  (Eval) "Word32.word"
| constant Uint32 \<rightharpoonup>
  (SML) "Word32.fromLargeInt (IntInf.toLarge _)" and
  (Haskell) "(Prelude.fromInteger _ :: Uint32.Word32)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint32.Word32)" and
  (Scala) "_.intValue"
| constant Uint32_signed \<rightharpoonup>
  (OCaml) "Big'_int.int32'_of'_big'_int"
| constant "0 :: uint32" \<rightharpoonup>
  (SML) "(Word32.fromInt 0)" and
  (Haskell) "(0 :: Uint32.Word32)" and
  (OCaml) "Int32.zero" and
  (Scala) "0"
| constant "1 :: uint32" \<rightharpoonup>
  (SML) "(Word32.fromInt 1)" and
  (Haskell) "(1 :: Uint32.Word32)" and
  (OCaml) "Int32.one" and
  (Scala) "1"
| constant "plus :: uint32 \<Rightarrow> _ " \<rightharpoonup>
  (SML) "Word32.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (OCaml) "Int32.add" and
  (Scala) infixl 7 "+"
| constant "uminus :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.~" and
  (Haskell) "negate" and
  (OCaml) "Int32.neg" and
  (Scala) "!(- _)"
| constant "minus :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (OCaml) "Int32.sub" and
  (Scala) infixl 7 "-"
| constant "times :: uint32 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (OCaml) "Int32.mul" and
  (Scala) infixl 8 "*"
| constant "HOL.equal :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "!((_ : Word32.word) = _)" and
  (Haskell) infix 4 "==" and
  (OCaml) "(Int32.compare _ _ = 0)" and
  (Scala) infixl 5 "=="
| class_instance uint32 :: equal \<rightharpoonup>
  (Haskell) -
| constant "less_eq :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word32.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (OCaml) "Uint32.less'_eq" and
  (Scala) "Uint32.less'_eq"
| constant "less :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word32.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (OCaml) "Uint32.less" and
  (Scala) "Uint32.less"
| constant "bitNOT :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.notb" and
  (Haskell) "Data'_Bits.complement" and
  (OCaml) "Int32.lognot" and
  (Scala) "_.unary'_~"
| constant "bitAND :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (OCaml) "Int32.logand" and
  (Scala) infixl 3 "&"
| constant "bitOR :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (OCaml) "Int32.logor" and
  (Scala) infixl 1 "|"
| constant "bitXOR :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (OCaml) "Int32.logxor" and
  (Scala) infixl 2 "^"

definition uint32_divmod :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32 \<times> uint32" where
  "uint32_divmod x y = 
  (if y = 0 then (undefined (op div :: uint32 \<Rightarrow> _) x (0 :: uint32), undefined (op mod :: uint32 \<Rightarrow> _) x (0 :: uint32)) 
  else (x div y, x mod y))"

definition uint32_div :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" 
where "uint32_div x y = fst (uint32_divmod x y)"

definition uint32_mod :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" 
where "uint32_mod x y = snd (uint32_divmod x y)"

lemma div_uint32_code [code]: "x div y = (if y = 0 then 0 else uint32_div x y)"
including undefined_transfer unfolding uint32_divmod_def uint32_div_def
by transfer (simp add: word_div_def)

lemma mod_uint32_code [code]: "x mod y = (if y = 0 then x else uint32_mod x y)"
including undefined_transfer unfolding uint32_mod_def uint32_divmod_def
by transfer (simp add: word_mod_def)

definition uint32_sdiv :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32"
where [code del]:
  "uint32_sdiv x y =
   (if y = 0 then undefined (op div :: uint32 \<Rightarrow> _) x (0 :: uint32)
    else Abs_uint32 (Rep_uint32 x sdiv Rep_uint32 y))"

definition div0_uint32 :: "uint32 \<Rightarrow> uint32"
where [code del]: "div0_uint32 x = undefined (op div :: uint32 \<Rightarrow> _) x (0 :: uint32)"
declare [[code abort: div0_uint32]]

definition mod0_uint32 :: "uint32 \<Rightarrow> uint32"
where [code del]: "mod0_uint32 x = undefined (op mod :: uint32 \<Rightarrow> _) x (0 :: uint32)"
declare [[code abort: mod0_uint32]]

lemma uint32_divmod_code [code]:
  "uint32_divmod x y =
  (if 0x80000000 \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint32 x, mod0_uint32 x)
   else let q = (uint32_sdiv (x >> 1) y) << 1;
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
including undefined_transfer unfolding uint32_divmod_def uint32_sdiv_def div0_uint32_def mod0_uint32_def
by transfer(simp add: divmod_via_sdivmod)

lemma uint32_sdiv_code [code abstract]:
  "Rep_uint32 (uint32_sdiv x y) =
   (if y = 0 then Rep_uint32 (undefined (op div :: uint32 \<Rightarrow> _) x (0 :: uint32))
    else Rep_uint32 x sdiv Rep_uint32 y)"
unfolding uint32_sdiv_def by(simp add: Abs_uint32_inverse)

text {* 
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint32_divmod_code} computes both with division only.
*}

code_printing
  constant uint32_div \<rightharpoonup>
  (SML) "Word32.div ((_), (_))" and
  (Haskell) "Prelude.div"
| constant uint32_mod \<rightharpoonup>
  (SML) "Word32.mod ((_), (_))" and
  (Haskell) "Prelude.mod"
| constant uint32_divmod \<rightharpoonup>
  (Haskell) "divmod"
| constant uint32_sdiv \<rightharpoonup>
  (OCaml) "Int32.div" and
  (Scala) "_ '/ _"

definition uint32_test_bit :: "uint32 \<Rightarrow> integer \<Rightarrow> bool"
where [code del]:
  "uint32_test_bit x n =
  (if n < 0 \<or> 31 < n then undefined (test_bit :: uint32 \<Rightarrow> _) x n
   else x !! (nat_of_integer n))"

lemma test_bit_uint32_code [code]:
  "test_bit x n \<longleftrightarrow> n < 32 \<and> uint32_test_bit x (integer_of_nat n)"
including undefined_transfer integer.lifting unfolding uint32_test_bit_def
by transfer(auto cong: conj_cong dest: test_bit_size simp add: word_size)

lemma uint32_test_bit_code [code]:
  "uint32_test_bit w n =
  (if n < 0 \<or> 31 < n then undefined (test_bit :: uint32 \<Rightarrow> _) w n else Rep_uint32 w !! nat_of_integer n)"
unfolding uint32_test_bit_def
by(simp add: test_bit_uint32.rep_eq)

code_printing constant uint32_test_bit \<rightharpoonup>
  (SML) "Uint32.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (OCaml) "Uint32.test'_bit" and
  (Scala) "Uint32.test'_bit"

definition uint32_set_bit :: "uint32 \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint32"
where [code del]:
  "uint32_set_bit x n b =
  (if n < 0 \<or> 31 < n then undefined (set_bit :: uint32 \<Rightarrow> _) x n b
   else set_bit x (nat_of_integer n) b)"

lemma set_bit_uint32_code [code]:
  "set_bit x n b = (if n < 32 then uint32_set_bit x (integer_of_nat n) b else x)"
including undefined_transfer integer.lifting unfolding uint32_set_bit_def
by(transfer)(auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint32_set_bit_code [code abstract]:
  "Rep_uint32 (uint32_set_bit w n b) = 
  (if n < 0 \<or> 31 < n then Rep_uint32 (undefined (set_bit :: uint32 \<Rightarrow> _) w n b)
   else set_bit (Rep_uint32 w) (nat_of_integer n) b)"
including undefined_transfer unfolding uint32_set_bit_def by transfer simp

code_printing constant uint32_set_bit \<rightharpoonup>
  (SML) "Uint32.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (OCaml) "Uint32.set'_bit" and
  (Scala) "Uint32.set'_bit"

lift_definition uint32_set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> uint32 \<Rightarrow> nat \<Rightarrow> uint32" is set_bits_aux .

lemma uint32_set_bits_code [code]:
  "uint32_set_bits f w n =
  (if n = 0 then w 
   else let n' = n - 1 in uint32_set_bits f ((w << 1) OR (if f n' then 1 else 0)) n')"
by(transfer fixing: n)(cases n, simp_all)

lemma set_bits_uint32 [code]:
  "(BITS n. f n) = uint32_set_bits f 0 32"
by transfer(simp add: set_bits_conv_set_bits_aux)


lemma lsb_code [code]: fixes x :: uint32 shows "lsb x = x !! 0"
by transfer(simp add: word_lsb_def word_test_bit_def)


definition uint32_shiftl :: "uint32 \<Rightarrow> integer \<Rightarrow> uint32"
where [code del]:
  "uint32_shiftl x n = (if n < 0 \<or> 32 \<le> n then undefined (shiftl :: uint32 \<Rightarrow> _) x n else x << (nat_of_integer n))"

lemma shiftl_uint32_code [code]: "x << n = (if n < 32 then uint32_shiftl x (integer_of_nat n) else 0)"
including undefined_transfer integer.lifting unfolding uint32_shiftl_def
by transfer(simp add: not_less shiftl_zero_size word_size)

lemma uint32_shiftl_code [code abstract]:
  "Rep_uint32 (uint32_shiftl w n) =
  (if n < 0 \<or> 32 \<le> n then Rep_uint32 (undefined (shiftl :: uint32 \<Rightarrow> _) w n) else Rep_uint32 w << (nat_of_integer n))"
including undefined_transfer unfolding uint32_shiftl_def by transfer simp

code_printing constant uint32_shiftl \<rightharpoonup>
  (SML) "Uint32.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (OCaml) "Uint32.shiftl" and
  (Scala) "Uint32.shiftl"

definition uint32_shiftr :: "uint32 \<Rightarrow> integer \<Rightarrow> uint32"
where [code del]:
  "uint32_shiftr x n = (if n < 0 \<or> 32 \<le> n then undefined (shiftr :: uint32 \<Rightarrow> _) x n else x >> (nat_of_integer n))"

lemma shiftr_uint32_code [code]: "x >> n = (if n < 32 then uint32_shiftr x (integer_of_nat n) else 0)"
including undefined_transfer integer.lifting unfolding uint32_shiftr_def
by transfer(simp add: not_less shiftr_zero_size word_size)

lemma uint32_shiftr_code [code abstract]:
  "Rep_uint32 (uint32_shiftr w n) =
  (if n < 0 \<or> 32 \<le> n then Rep_uint32 (undefined (shiftr :: uint32 \<Rightarrow> _) w n) else Rep_uint32 w >> nat_of_integer n)"
including undefined_transfer unfolding uint32_shiftr_def by transfer simp

code_printing constant uint32_shiftr \<rightharpoonup>
  (SML) "Uint32.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (OCaml) "Uint32.shiftr" and
  (Scala) "Uint32.shiftr"

definition uint32_sshiftr :: "uint32 \<Rightarrow> integer \<Rightarrow> uint32"
where [code del]:
  "uint32_sshiftr x n =
  (if n < 0 \<or> 32 \<le> n then undefined sshiftr_uint32 x n else sshiftr_uint32 x (nat_of_integer n))"

lemma sshiftr_beyond: fixes x :: "'a :: len word" shows
  "size x \<le> n \<Longrightarrow> x >>> n = (if x !! (size x - 1) then -1 else 0)"
by(rule word_eqI)(simp add: nth_sshiftr word_size)

lemma sshiftr_uint32_code [code]:
  "x >>> n = 
  (if n < 32 then uint32_sshiftr x (integer_of_nat n) else if x !! 31 then -1 else 0)"
including undefined_transfer integer.lifting unfolding uint32_sshiftr_def
by transfer(simp add: not_less sshiftr_beyond word_size)

lemma uint32_sshiftr_code [code abstract]:
  "Rep_uint32 (uint32_sshiftr w n) =
  (if n < 0 \<or> 32 \<le> n then Rep_uint32 (undefined sshiftr_uint32 w n) else Rep_uint32 w >>> (nat_of_integer n))"
including undefined_transfer unfolding uint32_sshiftr_def by transfer simp

code_printing constant uint32_sshiftr \<rightharpoonup>
  (SML) "Uint32.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint32.Int32) _)) :: Uint32.Word32)" and
  (OCaml) "Uint32.shiftr'_signed" and
  (Scala) "Uint32.shiftr'_signed"

lemma uint32_msb_test_bit: "msb x \<longleftrightarrow> (x :: uint32) !! 31"
by transfer(simp add: msb_nth)

lemma msb_uint32_code [code]: "msb x \<longleftrightarrow> uint32_test_bit x 31"
by(simp add: uint32_test_bit_def uint32_msb_test_bit)

lemma uint32_of_int_code [code]: "uint32_of_int i = Uint32 (integer_of_int i)"
including integer.lifting by transfer simp

lemma int_of_uint32_code [code]:
  "int_of_uint32 x = int_of_integer (integer_of_uint32 x)"
by(simp add: integer_of_uint32_def)

lemma nat_of_uint32_code [code]:
  "nat_of_uint32 x = nat_of_integer (integer_of_uint32 x)"
unfolding integer_of_uint32_def including integer.lifting by transfer (simp add: unat_def)

definition integer_of_uint32_signed :: "uint32 \<Rightarrow> integer"
where
  "integer_of_uint32_signed n = (if n !! 31 then undefined integer_of_uint32 n else integer_of_uint32 n)"

lemma integer_of_uint32_signed_code [code]:
  "integer_of_uint32_signed n =
  (if n !! 31 then undefined integer_of_uint32 n else integer_of_int (uint (Rep_uint32' n)))"
unfolding integer_of_uint32_signed_def integer_of_uint32_def
including undefined_transfer by transfer simp

lemma integer_of_uint32_code [code]:
  "integer_of_uint32 n =
  (if n !! 31 then integer_of_uint32_signed (n AND 0x7FFFFFFF) OR 0x80000000 else integer_of_uint32_signed n)"
unfolding integer_of_uint32_def integer_of_uint32_signed_def o_def
including undefined_transfer integer.lifting
by transfer(auto simp add: word_ao_nth uint_and_mask_or_full mask_numeral mask_Suc_0 intro!: uint_and_mask_or_full[symmetric])

code_printing
  constant "integer_of_uint32" \<rightharpoonup>
  (SML) "IntInf.fromLarge (Word32.toLargeInt _) : IntInf.int" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint32_signed" \<rightharpoonup>
  (OCaml) "Big'_int.big'_int'_of'_int32" and
  (Scala) "BigInt"

section {* Quickcheck setup *}

definition uint32_of_natural :: "natural \<Rightarrow> uint32"
where "uint32_of_natural x \<equiv> Uint32 (integer_of_natural x)"

instantiation uint32 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint32 \<equiv> qc_random_cnv uint32_of_natural"
definition "exhaustive_uint32 \<equiv> qc_exhaustive_cnv uint32_of_natural"
definition "full_exhaustive_uint32 \<equiv> qc_full_exhaustive_cnv uint32_of_natural"
instance ..
end

instantiation uint32 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint32 i in (x, 0xFFFFFFFF - x)" "0"
  "Typerep.Typerep (STR ''Uint32.uint32'') []" .

definition "narrowing_uint32 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint32 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint32 [code] = partial_term_of_code

instance ..
end

no_notation sshiftr_uint32 (infixl ">>>" 55)

end
