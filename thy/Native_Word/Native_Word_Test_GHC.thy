(*  Title:      Native_Word_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_GHC imports
  Native_Word_Test
begin

section {* Test with GHC *}

declare [[code_test_ghc = "-XTypeSynonymInstances"]]

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint16
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts test_casts'
in GHC

subsection {* Test quickcheck narrowing *}

lemma "(x :: uint32) AND y = x OR y"
quickcheck[narrowing, expect=counterexample]
oops

lemma "(f :: uint32 \<Rightarrow> bool) = g"
quickcheck[narrowing, size=3, expect=counterexample]
oops

lemma "(x :: uint16) AND y = x OR y"
quickcheck[narrowing, expect=counterexample]
oops

lemma "(f :: uint16 \<Rightarrow> bool) = g"
quickcheck[narrowing, size=3, expect=counterexample]
oops

lemma "(x :: uint8) AND y = x OR y"
quickcheck[narrowing, expect=counterexample]
oops

lemma "(f :: uint8 \<Rightarrow> bool) = g"
quickcheck[narrowing, size=3, expect=counterexample]
oops

lemma "(x :: uint) AND y = x OR y"
quickcheck[narrowing, expect=counterexample]
oops

lemma "(f :: uint \<Rightarrow> bool) = g"
quickcheck[narrowing, size=3, expect=counterexample]
oops

end
