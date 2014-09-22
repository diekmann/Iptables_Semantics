(*
 * Copyright (C) 2014, National ICT Australia Limited. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 *  * The name of National ICT Australia Limited nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

(*
 * Convert a SIMPL fragment into a monadic fragment.
 *)

theory SimplConv
imports L1Defs L1Peephole
begin

(*
 * Lemmas to unfold prior to L1 conversion.
 *)
declare creturn_def [L1unfold]
declare creturn_void_def [L1unfold]
declare cbreak_def [L1unfold]
declare whileAnno_def [L1unfold]
declare ccatchbrk_def [L1unfold]

(* Alternative definitions of "Language.switch" *)
lemma switch_alt_defs [L1unfold]:
  "switch x [] \<equiv> SKIP"
  "switch v ((a, b) # vs) \<equiv> Cond {s. v s \<in> a} b (switch v vs)"
  by auto

(* Convert "lvar_nondet_init" (which sets local variables to
 * undefined values) into a "Spec" command we can translate. *)
definition "lvar_init_spec upd \<equiv> {(s, t). \<exists>v. t = upd (\<lambda>_. v) s}"
lemma lvar_nondet_init_rewrite [L1unfold]:
  "lvar_nondet_init accessor upd \<equiv> Spec (lvar_init_spec upd)"
  apply (clarsimp simp: lvar_nondet_init_def lvar_init_spec_def)
  done

lemma lvar_init_spec_to_L1_init [L1opt]:
  "L1_spec (lvar_init_spec upd) \<equiv> L1_init upd"
  apply (rule eq_reflection)
  apply (clarsimp simp: L1_defs lvar_init_spec_def)
  apply (clarsimp simp: bind_liftE_distrib [symmetric])
  apply (rule arg_cong [where f=liftE])
  apply (rule ext)
  apply (clarsimp simp: spec_def select_def simpler_modify_def bind_def)
  apply force
  done

lemma not_msb_from_less:
  "(v :: 'a word) < 2 ^ (len_of TYPE('a :: len) - 1) \<Longrightarrow> \<not> msb v"
  apply (clarsimp simp add: msb_nth)
  apply (drule less_mask_eq)
  apply (drule word_eqD, drule(1) iffD2)
  apply simp
  done

lemma sless_positive [simp]:
  "\<lbrakk> a < n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <s n"
  apply (subst signed.less_le)
  apply safe
  apply (subst word_sle_msb_le)
  apply safe
    apply clarsimp
    apply (metis One_nat_def msb_shift not_msb_from_less word_not_simps(1))
   apply simp
  apply simp
  done

lemma sle_positive [simp]:
  "\<lbrakk> a \<le> n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <=s n"
  apply (subst signed.le_less)
  apply (case_tac "n=0")
   apply clarsimp
  apply (clarsimp simp: sless_positive)
  done

(* An induction rule that matches our recursive definitions. *)
lemma recguard_induct: "\<lbrakk> P 0; \<And>n. P (recguard_dec n) \<Longrightarrow> P n \<rbrakk> \<Longrightarrow> P n"
  apply (unfold recguard_dec_def)
  apply (erule nat_induct)
  apply (metis diff_Suc_1)
  done

end
