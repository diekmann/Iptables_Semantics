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

theory Simple
imports
  "../../AutoCorres"
  GCD
begin

(* Parse the input file. *)
install_C_file "simple.c"

(* Abstract the input file. *)
autocorres [ ts_force pure = max, ts_force nondet = gcd, unsigned_word_abs = gcd ] "simple.c"

(* Generated theorems and proofs. *)
thm simple.max'_def simple.max'_ccorres
thm simple.gcd'_def simple.gcd'_ccorres

context simple begin

(* Show generated "max'" function matches in-built "max". *)
lemma "max' a b = max a b"
  unfolding max'_def max_def
  by (rule refl)

(* Show "gcd'" calculates the gcd. *)
lemma gcd_wp [wp]:
    "\<lbrace> P (gcd a b) \<rbrace> gcd' a b \<lbrace> P \<rbrace>!"
  (* Unfold definition of "gcd'". *)
  apply (unfold gcd'_def)

  (* Annoate the loop with an invariant and measure. *)
  apply (subst whileLoop_add_inv [where
     I="\<lambda>(a', b') s. gcd a b = gcd a' b' \<and> P (gcd a b) s"
     and M="\<lambda>((a', b'), s). a'"])

  (* Solve using weakest-precondition. *)
  apply wp
    apply clarsimp
    apply (metis gcd_commute_nat gcd_red_nat)
   apply clarsimp
  apply clarsimp
  done

lemma monad_to_gets:
    "\<lbrakk> \<And>P. \<lbrace> P \<rbrace> f \<lbrace> \<lambda>r s. P s \<and> r = v s \<rbrace>!; empty_fail f \<rbrakk> \<Longrightarrow> f = gets v"
  apply atomize
  apply (monad_eq simp: validNF_def valid_def no_fail_def empty_fail_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x="\<lambda>s'. s = s'" in spec)
   apply clarsimp
   apply force
  apply clarsimp
  apply (drule_tac x="\<lambda>s'. s' = t" in spec)
  apply clarsimp
  apply force
  done

lemma gcd_to_return [simp]:
    "gcd' a b = return (gcd a b)"
  apply (subst monad_to_gets [where v="\<lambda>_. gcd a b"])
    apply (wp gcd_wp)
    apply simp
   apply (clarsimp simp: gcd'_def)
   apply (rule empty_fail_bind)
    apply (rule empty_fail_whileLoop)
    apply (clarsimp simp: split_def)
   apply (clarsimp simp: split_def)
  apply (clarsimp simp: split_def)
  done

end

end
