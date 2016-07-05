(*  Title:      Native_Word_Test_MLton2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_OCaml imports
  Native_Word_Test
begin

section {* Test with OCaml *}

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint
in OCaml

end
