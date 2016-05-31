theory Lib_Word_toString
imports "../Common/Lib_toString"
        "~~/src/HOL/Word/Word"
        "./l4v/lib/Word_Lib/Word_Lemmas"
begin

(*immitation of http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
(*lc = lower-case*)
definition string_of_word_single :: "bool \<Rightarrow> 'a::len word \<Rightarrow> string" where
  "string_of_word_single lc w \<equiv>
    (if w < 10 then [char_of_nat (48 + unat w)] else if w < 36 then [char_of_nat ((if lc then 87 else 55) + unat w)] else undefined)"

value "let word_upto = ((\<lambda> i j. map (of_nat \<circ> nat) [i .. j]) :: int \<Rightarrow> int \<Rightarrow> 12 word list)
       in map (string_of_word_single False) (word_upto (-1) (36))"

(* parameters: lowercase, base, minimum length - 1, to-be-serialized word *) 
function string_of_word :: "bool \<Rightarrow> ('a :: len) word \<Rightarrow> nat \<Rightarrow> ('a :: len) word \<Rightarrow> string" where
  "string_of_word lc base ml n =
    (if
       base < 2 \<or> len_of TYPE('a) < 2
     then
       undefined
     else (if
       n < base \<and> ml = 0
     then
       string_of_word_single lc n
     else string_of_word lc base (ml - 1) (n div base) @ string_of_word_single lc (n mod base)
     ))"
by clarsimp+

definition "hex_string_of_word l \<equiv> string_of_word True (16 :: ('a::len) word) l"
definition "hex_string_of_word0 \<equiv> hex_string_of_word 0"
(* be careful though, these functions only make sense with words > length 4. With 4 bits, base 16 is not representable. *)
definition "dec_string_of_word0 \<equiv> string_of_word True 10 0"

termination string_of_word
	apply(relation "measure (\<lambda>(a,b,c,d). unat d + c)")
	 apply(rule wf_measure)
	apply(subst in_measure)
	apply(clarsimp)
	subgoal for base ml n
    apply(case_tac "ml \<noteq> 0")
     apply(simp add: less_eq_Suc_le unat_div)
    apply(simp)
    apply(subgoal_tac "(n div base) < n")
     apply(blast intro: unat_mono)
    apply(rule div_less_dividend_word)
     subgoal by(metis Word_Lemmas.power_not_zero linorder_neqE_nat numeral_less_iff power_zero_numeral semiring_norm(76) word_neq_0_conv)
    apply(clarsimp)
    apply(thin_tac "n \<noteq> 0")
    subgoal by (metis One_nat_def mult.right_neutral power_0 power_Suc unat_1 unat_power_lower Suc_1 inc_induct le_def less_eq_Suc_le lt1_neq0 not_degenerate_imp_2_neq_0 word_le_less_eq)
  done
done 

lemma "hex_string_of_word0 (0xdeadbeef42 :: 42 word) = ''deadbeef42''" by eval
lemma "hex_string_of_word 1 (0x1 :: 5 word) = ''01''" by eval

value "dec_string_of_word0 (8::32 word)"
value "string_of_nat (unat  (8::32 word))"
value "dec_string_of_word0 (1::2 word)"
value "string_of_nat (unat  (1::2 word))"
value "dec_string_of_word0 (-1::8 word)" (*wow, this is fast!*)
value "string_of_nat (unat  (-1::8 word))"


lemma string_of_word_single_atoi:
  "n < 10 \<Longrightarrow> string_of_word_single True n = [char_of_nat (48 + unat n)]"
  by(simp add: string_of_word_single_def)

(*TODO: I want the reverse as [code_unfold] ! ! ! ! ! ! ! ! !*)
lemma fixes w ::"32 word" (*TODO: for all words?*)
  shows "base = 10 \<Longrightarrow> zero = 0 \<Longrightarrow> string_of_word True base zero w = string_of_nat (unat w)"
  proof(induction True base zero w rule: string_of_word.induct)
  case (1 base ml n)
  have unat_mod_ten: "unat (n mod 0xA) = unat n mod 10"
    apply(subst Word.unat_mod)
    by(simp)
  have unat_div_ten: "(unat (n div 0xA)) = unat n div 10"
    apply(subst Word.unat_div)
    by simp
  have n_less_ten_unat: "n < 0xA \<Longrightarrow> (unat n < 10)"
    apply(rule Word_Lemmas.unat_less_helper)
    by(simp)
  have "0xA \<le> n \<Longrightarrow> 10 \<le> unat n" 
    apply(subst(asm) Word.word_le_nat_alt)
    by(simp)
  hence n_less_ten_unat_not: "\<not> n < 0xA \<Longrightarrow> \<not> unat n < 10" by fastforce
  from 1(2,3) have " \<not> (base < 2 \<or> len_of TYPE(32) < 2)"
    by(simp)
  with 1 have IH: "\<not> n < 0xA \<Longrightarrow> string_of_word True 0xA 0 (n div 0xA) = string_of_nat (unat (n div 0xA))"
     by(simp del: string_of_word.simps)
  show ?case
    apply(simp add: 1 del: string_of_word.simps)
    (*using[[simp_trace]] apply(simp del: string_of_word.simps string_of_nat.simps)*)
    apply(case_tac "n < 0xA")
     subgoal
     apply(subst(1) string_of_word.simps)
     apply(subst(1) string_of_nat.simps)
     apply(simp add: n_less_ten_unat del: string_of_word.simps)
     by(simp add: string_of_word_single_atoi)
    using sym[OF IH] apply(simp del: string_of_word.simps)
    apply(subst(1) string_of_word.simps)
    apply(simp del: string_of_word.simps)
    apply(subst(1) string_of_nat.simps)
    apply(simp add: del: string_of_word.simps)
    apply(safe)
     apply(simp add: n_less_ten_unat_not del: string_of_word.simps; fail)
    apply(subst string_of_word_single_atoi)
     apply(rule Word.word_mod_less_divisor, simp; fail)
    apply(simp add: unat_mod_ten del: string_of_word.simps)
    apply(rule sym)
    apply(simp add: n_less_ten_unat_not del: string_of_word.simps)
    apply(simp add: unat_div_ten del: string_of_word.simps)
    done
qed
lemma "dec_string_of_word0 w = string_of_nat (unat w)"
  (*TODO*)
  unfolding dec_string_of_word0_def
  oops

end