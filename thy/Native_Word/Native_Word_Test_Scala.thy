(*  Title:      Native_Word_Test_Scala.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_Scala imports
  Native_Word_Test
begin

section {* Test with Scala *}

text {*
  In Scala, @{typ uint} and @{typ uint32} are both implemented as type \texttt{Int}.
  When they are used in the same generated program, we have to suppress the type class
  instances for one of them. Similarly for @{typ uint16} and @{typ char}
  if @{theory Code_Char} is loaded.
*}
code_printing class_instance uint32 :: equal \<rightharpoonup> (Scala) -
  | class_instance uint16 :: equal \<rightharpoonup> (Scala) -

test_code
  test_uint32 "test_uint32' = 0x12"
  test_uint16
  test_uint8 "test_uint8' = 0x12" 
  test_uint
  test_casts test_casts'
in Scala

end
