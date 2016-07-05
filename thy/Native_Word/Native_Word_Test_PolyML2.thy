(*  Title:      Native_Word_Test_PolYML2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_PolyML2 imports
  Native_Word_Test_Emu
begin

test_code
  test_uint16 test_uint16_emulation
  test_casts'
in PolyML

end
