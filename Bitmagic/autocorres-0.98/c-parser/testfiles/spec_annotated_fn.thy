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

theory spec_annotated_fn
imports "../CTranslation"
begin

declare sep_conj_ac [simp add]

install_C_file "spec_annotated_fn.c"


print_locale spec_annotated_fn_global_addresses
print_locale Square_spec

thm Square_spec_def

context spec_annotated_fn_global_addresses
begin

thm Square_body_def
thm Square_impl
thm Square_spec_def
thm \<Gamma>_def

end

lemma (in Square_spec) foo:
  shows "\<Gamma> \<turnstile> \<lbrace> T \<rbrace> \<acute>ret__unsigned :== CALL Square(4) \<lbrace> \<acute>ret__unsigned = 16 \<rbrace> "
apply vcg
apply simp
done

lemma (in spec_annotated_fn_global_addresses)
shows "\<forall>n. \<Gamma> \<turnstile> \<lbrace> \<acute>n = n \<rbrace> \<acute>ret__unsigned :== PROC Square(\<acute>n)
               \<lbrace>\<acute>ret__unsigned = n * n \<rbrace>"
apply vcg
done

end
