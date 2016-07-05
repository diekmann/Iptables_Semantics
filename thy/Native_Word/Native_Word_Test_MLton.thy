(*  Title:      Native_Word_Test_MLton.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_MLton imports
  Native_Word_Test
begin

section {* Test with MLton *}

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts
in MLton

text {* MLton provides a \texttt{Word16} structure. To test it in the SML\_word target, we have
  to associate a driver with the combination. *}

setup {* Code_Test.add_driver ("MLton_word", (Code_Test.evaluate_in_mlton, "SML_word")) *}

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint16
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts
  test_casts'
in MLton_word

end
