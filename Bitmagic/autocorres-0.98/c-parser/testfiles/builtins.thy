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

theory builtins
imports "../CTranslation"
begin

install_C_file "builtins.c"

context builtins
begin

thm f_body_def
thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> \<acute>i = 3 \<rbrace> Call f_'proc \<lbrace> \<acute>ret__int = 6 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret__int = 6 \<rbrace>"])
  apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (hoare_rule HoarePartial.Cond [where P\<^sub>1="{}" and P\<^sub>2="\<lbrace>\<acute>i=3\<rbrace>"])
        apply (simp add: subset_eq word_sless_def word_sle_def)
      apply (hoare_rule HoarePartial.conseq_exploit_pre)
      apply simp
    apply vcg
    apply simp
  apply vcg
apply vcg
done

(* NOTE:

  apply vcg

at the outset generates three sub-goals, last of which is not provable
*)

end
end
