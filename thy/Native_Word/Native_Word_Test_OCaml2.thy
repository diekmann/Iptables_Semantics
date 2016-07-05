(*  Title:      Native_Word_Test_OCaml2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_OCaml2 imports
  Native_Word_Test_Emu
begin

test_code
  test_uint16 test_uint16_emulation
  test_uint8 "test_uint8' = 0x12" test_uint8_emulation
  test_casts test_casts'
in OCaml

end
