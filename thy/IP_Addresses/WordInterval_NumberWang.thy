theory WordInterval_NumberWang
imports WordInterval
  "../Word_Lib/Word_Lemmas"
  WordInterval
begin

text\<open>Cardinality approximation for @{typ "('a::len) wordinterval"}s\<close>
(*TODO: move!*)
context begin
  lemma card_enum_upto: fixes s::"('a::len) word" shows "card (set [s .e. e]) = Suc (unat e) - unat s"
    apply(subst List.card_set)
    apply(simp add: remdups_enum_upto)
    done
  
  lemma card_atLeastAtMost_word: fixes s::"('a::len) word" shows "card {s..e} = Suc (unat e) - (unat s)"
    apply(cases "s > e")
     apply(simp)
     apply(subst(asm) Word.word_less_nat_alt)
     apply simp
    apply(subst Word_Lemmas.upto_enum_set_conv2[symmetric])
    apply(subst List.card_set)
    apply(simp add: remdups_enum_upto)
    done

  lemma finite_wordinterval: "finite (wordinterval_to_set r)" by simp

  fun wordinterval_card :: "('a::len) wordinterval \<Rightarrow> nat" where
    "wordinterval_card (WordInterval s e) = Suc (unat e) - (unat s)" |
    "wordinterval_card (RangeUnion a b) = wordinterval_card a + wordinterval_card b"

  lemma wordinterval_card: "wordinterval_card r \<ge> card (wordinterval_to_set r)"
    proof(induction r)
    case WordInterval thus ?case by (simp add: card_atLeastAtMost_word)
    next
    case (RangeUnion r1 r2)
      have "card (wordinterval_to_set r1 \<union> wordinterval_to_set r2) \<le> card (wordinterval_to_set r1) + card (wordinterval_to_set r2)"
        using Finite_Set.card_Un_le by blast
      with RangeUnion show ?case by(simp)
    qed

  text\<open>With @{thm wordinterval_compress} it should be possible to get the exact cardinality\<close>
end



end
