(*  Title:      Native_Word_Test_MLton2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_MLton2 imports
  Native_Word_Test_Emu
begin

export_code test_casts' in SML module_name Generated_Code

declare [[code_test_overlord]]

test_code
  test_uint16 test_uint16_emulation
  test_casts'
in MLton

end
