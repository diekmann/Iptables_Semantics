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

theory parse_struct
imports "../CTranslation"
begin

install_C_file "parse_struct.c"

(* mem_type instances proved automatically.  If you remove the additional
   theorems from the simp add: list below, you see that the LHS of the goal
   turns into sizeof TYPE(struct1), demonstrating that the mem_type's axiom
   "len" is applied.  Thus, struct1 is really a mem_type. *)

lemma
  "length bs = size_of TYPE(struct1_C) \<Longrightarrow> length (to_bytes (x::struct1_C) bs) = 12"
  by (simp)

print_locale parse_struct_global_addresses

thm allinclusive_C_typ_tag

thm parse_struct_global_addresses.mkall_body_def

(* fold congruences proved in creation of these records help us
   by reducing the doubling of syntax on the lhs *)
lemma "s \<lparr> c1_C := c1_C s + 2 \<rparr> = c1_C_update (\<lambda>x. x + 2) s"
  apply (simp cong: charpair_C_fold_congs)
  done

end
