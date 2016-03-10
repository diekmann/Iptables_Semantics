theory OpenFlowSerialize
imports OpenFlowMatches OpenFlowAction Semantics_OpenFlow "../Primitive_Matchers/Common_Primitive_toString"
begin

definition "serialization_test_entry \<equiv> OFEntry 7 {IPv4Dst (PrefixMatch 0xA000201 32), IngressPort ''s1-lan'', L4Dst 0x50 0, L4Src 0x400 0x3FF, IPv4Proto 6, EtherType 0x800} [ModifyField_l2dst 0xA641F185E862, Forward ''s1-wan'']"

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
	apply(thin_tac "n \<noteq> 0")
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

definition "serialize_actions pids a \<equiv> if length a = 0 then ''drop'' else intersperse (CHR '','') \<circ> map (serialize_action pids) $ a"

value "serialize_actions (\<lambda>oif. ''42'') (ofe_action serialization_test_entry)"
value "serialize_actions undefined []"

definition "prefix_to_string pfx \<equiv> ipv4_cidr_toString (pfxm_prefix pfx, pfxm_length pfx)"

primrec serialize_of_match where
"serialize_of_match pids (IngressPort p) = ''in_port='' @ pids p" |
"serialize_of_match _ (VlanId i) = ''dl_vlan='' @ string_of_word True 10 i" |
"serialize_of_match _ (VlanPriority _) = undefined" | (* uh, äh\<dots> We don't use that anyway\<dots> *)
"serialize_of_match _ (EtherType i) = ''dl_type=0x'' @ string_of_word True 16 i" |
"serialize_of_match _ (EtherSrc m) = ''dl_src='' @ serialize_mac m" |
"serialize_of_match _ (EtherDst m) = ''dl_dst'' @ serialize_mac m" |
"serialize_of_match _ (IPv4Proto i) = ''nw_proto='' @ string_of_word True 10 i" |
"serialize_of_match _ (IPv4Src p) = ''nw_src='' @ prefix_to_string p" |
"serialize_of_match _ (IPv4Dst p) = ''nw_dst='' @ prefix_to_string p" |
"serialize_of_match _ (L4Src i m) = ''tp_src='' @ string_of_word True 10 i @ (if m = max_word then [] else ''/0x'' @ string_of_word True 16 m)" |
"serialize_of_match _ (L4Dst i m) = ''tp_dst='' @ string_of_word True 10 i @ (if m = max_word then [] else ''/0x'' @ string_of_word True 16 m)"

definition "serialize_of_matches pids \<equiv> op @ ''hard_timeout=0,idle_timeout=0,'' \<circ> intersperse (CHR '','') \<circ> map (serialize_of_match pids) \<circ> sorted_list_of_set" 

value "serialize_of_matches (\<lambda>oif. ''42'') (ofe_fields serialization_test_entry)"

definition "serialize_of_entry pids e \<equiv> (case e of (OFEntry p f a) \<Rightarrow> ''priority='' @ string_of_word True 10 p @ '','' @ serialize_of_matches pids f @ '','' @ ''action='' @ serialize_actions pids a)"

value "serialize_of_entry (the \<circ> map_of [(''s1-lan'',''42''),(''s1-wan'',''1337'')]) serialization_test_entry"


end