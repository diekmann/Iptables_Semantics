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

theory longlong
imports "../CTranslation"
begin

install_C_file "longlong.c"

ML {* NameGeneration.return_var_name (Absyn.Signed Absyn.LongLong) *}


context longlong
begin

thm f_body_def
thm shifts1_body_def
thm shifts2_body_def

lemma "(ucast :: 16 word \<Rightarrow> 8 word) 32768 = 0"
apply simp
done

lemma "(scast :: 16 word \<Rightarrow> 8 word) 32768 = 0"
by simp

lemma "(scast :: 16 word \<Rightarrow> 8 word) 65535 = 255"
by simp

lemma "(ucast :: 16 word \<Rightarrow> 8 word) 65535 = 255"
by simp

lemma "(ucast :: 16 word \<Rightarrow> 8 word) 32767 = 255" by simp
lemma "(scast :: 16 word \<Rightarrow> 8 word) 32767 = 255" by simp

lemma "(scast :: 8 word \<Rightarrow> 16 word) 255 = 65535" by simp
lemma "(ucast :: 8 word \<Rightarrow> 16 word) 255 = 255" by simp

lemma sint_1 [simp]: "1 < len_of TYPE('a) \<Longrightarrow> sint (1 :: 'a::len word) = 1"
apply (subgoal_tac "1 \<in> sints (len_of TYPE ('a))")
  defer
  apply (simp add: sints_num)
  apply (rule order_trans [where y = 0])
    apply simp
  apply simp
  apply (drule Word.word_sint.Abs_inverse)
  apply (simp add: Word.word_of_int_hom_syms)
done

lemma g_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL callg() \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply (simp add: max_word_def)
done

thm literals_body_def

lemma literals_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL literals() \<lbrace> \<acute>ret__int = 31 \<rbrace>"
apply vcg
apply simp
done

end (* context *)

end (* theory *)
