(*  Title:      Native_Word_Test_PolyML.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_PolyML imports
  Native_Word_Test
begin

section {* Test with PolyML *}

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts
in PolyML

end
