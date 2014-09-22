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

theory fncall
imports "../CTranslation"
begin

declare sep_conj_ac [simp add]

primrec
  fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = (Suc n) * fac n"

ML {*

val ast = IsarInstall.get_Csyntax @{theory} "fncall.c"

*}

install_C_file "fncall.c"

context fncall
begin


thm "\<Gamma>_def"
thm has_bogus_spec_'proc_def
thm has_bogus_spec_impl
thm f_impl
thm g_impl
thm h_impl
thm i_impl
thm calls_bogus_impl
thm f_body_def
thm g_body_def
thm fact_body_def

thm fact_'proc_def

thm has_bogus_spec_modifies
thm g_modifies
thm f_modifies
thm fact_modifies

term "f_body"
term "\<Gamma>"
term "fact_body"
term "f_'proc"

end

print_locale fncall_global_addresses

print_locale g_modifies
thm g_modifies_def

print_locale f_spec
thm f_spec_def

lemma (in g_modifies)
  shows "\<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== PROC g() \<lbrace> \<acute>t_hrs = t \<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


lemma (in fncall_global_addresses) f_impl_result:
  "\<Gamma> f_'proc = Some f_body"
  apply (rule f_impl)
  done

lemma (in fncall_global_addresses) g_spec:
  shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC g() \<lbrace> \<acute>ret__int = 257 \<rbrace>"
  apply vcg
  done

lemma (in fncall_global_addresses) foo:
  shows
   "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC f(n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
apply vcg
apply (simp )
done

lemma (in f_spec) foo :
shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(\<acute>n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"

apply vcg
done

lemma (in fncall_global_addresses) bar:
shows "\<Gamma> \<turnstile> \<lbrace> 1\<le> \<acute>n & \<acute>n \<le> 12 \<rbrace> \<acute>ret__int :== CALL fact(\<acute>n) \<lbrace> \<acute>ret__int = of_nat (fac (unat \<acute>n)) \<rbrace>"
apply vcg
apply unat_arith
oops

lemma (in fncall_global_addresses) baz:
shows "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== PROC i() \<lbrace> \<acute>t_hrs = t \<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done

locale ih = i_modifies + h_modifies
lemma (in ih) qux:
shows "\<forall>t. \<Gamma> \<turnstile> \<lbrace>\<acute>t_hrs = t\<rbrace> \<acute>ret__int :== CALL i() \<lbrace> t = \<acute>t_hrs \<rbrace>"
apply vcg
oops

locale ff = f_spec + f_modifies
(* this lemma is bogus, because f does actually modify the globals *)
lemma (in ff) bogus1:
shows "\<forall>t. \<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== CALL f(\<acute>n) \<lbrace> t = \<acute>t_hrs \<rbrace>"
apply vcg
apply simp
done

lemma (in has_bogus_spec_spec) bogus2:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL has_bogus_spec() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
apply vcg
done

lemma (in fncall_global_addresses) toldyou:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL has_bogus_spec() \<lbrace> \<acute>ret__int = 3 \<rbrace>"
apply vcg
done

lemma (in has_bogus_spec_spec) bogus3:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL calls_bogus() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
apply vcg
done

end
