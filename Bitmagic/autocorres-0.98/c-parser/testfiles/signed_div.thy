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

theory signed_div
imports "../CTranslation"
begin

install_C_file "signed_div.c"

context signed_div
begin

lemma f_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(5, -1) \<lbrace> \<acute>ret__int = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: sdiv_word_def sdiv_int_def)
  done

lemma word_not_minus_one [simp]:
  "0 \<noteq> (-1 :: word32)"
  by (metis word_msb_0 word_msb_n1)

lemma f_overflow:
  shows "\<lbrakk> a_' s = of_int (-2^31); b_' s = -1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle> Call f_'proc ,Normal s\<rangle> \<Rightarrow> Fault SignedArithmetic"
  apply (rule exec.Call [where \<Gamma>=\<Gamma>, OF f_impl, simplified f_body_def creturn_def])
  apply (rule exec.CatchMiss)
  apply (subst exec.simps, clarsimp simp del: word_neq_0_conv simp: sdiv_word_def sdiv_int_def)+
  apply simp
  done

lemma g_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g(-5, 10) \<lbrace> \<acute>ret__int = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: smod_word_def smod_int_def sdiv_int_def)
  done

lemma h_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL h(5, -1) \<lbrace> \<acute>ret__int = 0 \<rbrace>"
  apply vcg
  apply (clarsimp simp: word_arith_nat_div ucast_def bintr_Min)
  done

lemma i_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(5, -1) \<lbrace> \<acute>ret__int = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: sdiv_word_def sdiv_int_def)
  done

end

end
