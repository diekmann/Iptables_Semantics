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

theory bigstruct
imports "../CTranslation"
begin

declare sep_conj_ac [simp add]
thm size_td_simps

install_C_file "bigstruct.c"

(*
instance foo :: mem_type
apply intro_classes

prefer 4
apply(simp add: foo_tag_def)
apply clarify
apply(rule fu_eq_mask)
 apply(simp add: size_td_simps typ_info_array
     array_tag_def align_td_array_tag size_of_def)
apply(simp add: size_td_simps typ_info_array
     array_tag_def align_td_array_tag size_of_def)
apply(rule fu_eq_mask_final_pad)
apply(rule fu_eq_mask_ti_typ_pad_combine)+
apply(rule fu_eq_mask_empty_typ_info)
apply(simp add: there_is_only_one)
apply(fastforce simp: fg_cons_def comp_def intro: fc_ti_typ_pad_combine)+

*)

end
