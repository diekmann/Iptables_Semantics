(*  Title:      Native_Word_Test_SMLNJ2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_SMLNJ2 imports
  Native_Word_Test_Emu
begin

test_code
  test_uint16 test_uint16_emulation
  test_casts'
in SMLNJ

end
