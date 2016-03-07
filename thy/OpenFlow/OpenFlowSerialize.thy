theory OpenFlowSerialize
imports OpenFlowMatches OpenFlowAction Semantics_OpenFlow
begin

(*immitation of http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
definition "string_of_word_single lc w \<equiv> (if w < 10 then [char_of_nat (48 + unat w)] else if w < 36 then [char_of_nat ((if lc then 87 else 55) + unat w)] else undefined)"
value "map (string_of_word_single False) $ word_upto (-1) (36 :: 12 word)"
function string_of_word :: "bool \<Rightarrow> ('a :: len) word \<Rightarrow> ('a :: len) word \<Rightarrow> string" where
  "string_of_word lc base n = (if base < 2 \<or> len_of TYPE('a) < 2 then undefined else
  	(if n < base then string_of_word_single lc n else string_of_word lc base (n div base) @ string_of_word_single lc (n mod base)))"
by clarsimp+

find_theorems "?a div (?b::('a :: len) word)"
termination string_of_word
	apply(relation "measure (unat \<circ> snd \<circ> snd)")
	apply(rule wf_measure)
	apply(subst in_measure)
	apply(clarsimp)
	apply(subgoal_tac "(n div base) < n")
	apply(blast intro: unat_mono)
	apply(rule div_less_dividend_word)
	apply(metis WordLemmaBucket.power_not_zero linorder_neqE_nat numeral_less_iff power_zero_numeral semiring_norm(76) word_neq_0_conv)
	apply(clarsimp)
	apply(thin_tac _)
	apply(metis Suc_1 inc_induct le_def less_eq_Suc_le lt1_neq0 not_degenerate_imp_2_neq_0 power_one power_overflow_simp word_le_less_eq) (* words are fun *)
done 

value "string_of_word True 16 (0xdeadbeef42 :: 42 word)"

value "map (op << (1::48 word) \<circ> op * 8) \<circ> rev $ [0..<6]"

fun intersperse where
"intersperse _ [] = []" |
"intersperse a [x] = x" |
"intersperse a (x#xs) = x @ a # intersperse a xs"

definition "serialize_mac (m::48 word) \<equiv> intersperse (CHR '':'') \<circ> map (string_of_word True 16 \<circ> (\<lambda>h. (m >> h * 8) && 0xff)) \<circ> rev $ [0..<6]"
value "serialize_mac 0xdeadbeefcafe"

definition "serialize_action pids a \<equiv> (case a of
	Forward oif \<Rightarrow> ''output:'' @ pids oif |
	ModifyField_l2dst na \<Rightarrow> ''mod_dl_dst:'' @ serialize_mac na)" 

definition "serialize_actions pids \<equiv> intersperse (CHR '','') \<circ> map (serialize_action pids)"

value "serialize_actions (\<lambda>oif. ''42'') [ModifyField_l2dst 0xA641F185E862, Forward ''test'']"

end