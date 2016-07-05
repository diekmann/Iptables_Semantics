(*  Title:      Native_Word_Test_SMLNJ.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_SMLNJ imports
  Native_Word_Test
begin

section {* Test with SML/NJ *}

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts
in SMLNJ

end
