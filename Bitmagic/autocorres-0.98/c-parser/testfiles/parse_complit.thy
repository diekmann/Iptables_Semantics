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

theory parse_complit
imports "../CTranslation"
begin

install_C_file "parse_complit.c"

context parse_complit_global_addresses
begin
thm simple1_body_def
thm simple2_body_def
thm simple3_body_def
thm simple4_body_def
thm simple5_body_def
thm f_body_def
thm g_body_def
thm h_body_def
thm function_body_def
thm function2_body_def
thm function3_body_def
thm sjw_body_def
thm enum_test_body_def
thm main_body_def
term "aa_'"  (* should have an 11-wide array of ints as its range *)

end

lemma (in parse_complit_global_addresses) f2_test:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL function2() \<lbrace> \<acute>ret__int = 3 \<rbrace>"
apply vcg
apply simp
done

lemma (in parse_complit_global_addresses) foo:
  "\<forall>x. \<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL enum_test(x) \<lbrace> \<acute>ret__int = -1 \<rbrace>"
apply vcg
apply (simp add: val2_def)
done

end
