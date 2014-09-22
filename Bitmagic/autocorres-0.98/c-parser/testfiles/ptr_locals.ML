(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions, and the following disclaimer,
 *    without modification.
 *
 * 2. Redistributions in binary form must reproduce at minimum a disclaimer
 *    substantially similar to the "NO WARRANTY" disclaimer below
 *    ("Disclaimer") and any redistribution must be conditioned upon
 *    including a substantially similar Disclaimer requirement for further
 *    binary redistribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDERS OR CONTRIBUTORS BE LIABLE FOR SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGES.
 *)

val result = state "testfiles/ptr_locals.c";

local
      open CalculateState TermsTypes NameGeneration
      val INTINFO ii = std_types_IntInfo
      val int_refname = heapreftype_name "int"
      val intptrrefname = heapreftype_name "int_ptr"
      val int_refty = Type(int_refname, [])
      val intptrrefty = Type(intptrrefname, [])
      val int = #ity ii
      val expected_result =
          [vdecl (global_var "x", int, true),
           refinstance int_refname,
           vdecl (heap_var_name "int", int_refty --> int, true),
           vdecl (global_var "ptr", int_refty, true),
           vdecl (global_var "array", mk_list_type int, true),
           vdecl (local_var "f" return_var_name, int_refty, false),
           refinstance intptrrefname,
           vdecl (heap_var_name "int_ptr", intptrrefty --> int_refty, true),
           vdecl (local_var "f" "p", intptrrefty, false),
           vdecl (local_var "f" "ptrarray", mk_list_type int_refty, false)
           ]
in
val _ = if result = expected_result then print "ptr_locals.c: PASSED\n"
        else print "ptr_locals.c: FAILED\n"
end


(* Local variables: *)
(* mode: sml *)
(* End: *)
