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

theory Plus
imports
  "../../AutoCorres"
begin

install_C_file "plus.c"

autocorres [ ts_force nondet = plus2 ] "plus.c"

context plus begin

(* 3 + 2 should be 5 *)
lemma "plus' 3 2 = 5"
  unfolding plus'_def
  by eval

(* plus does what it says on the box *)
lemma plus_correct: "plus' a b = a + b"
  unfolding plus'_def
  apply (rule refl)
  done

(* Compare pre-lifting to post-lifting *)
thm plus_global_addresses.plus2_body_def
thm plus2'_def

(* plus2 does what it says on the box *)
lemma plus2_correct: "\<lbrace>\<lambda>s. True\<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b\<rbrace>"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply (wp, auto simp: not_less)
  done

(* plus2 does what it says on plus's box *)
lemma plus2_is_plus: "\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = plus' a b \<rbrace>"
  unfolding plus'_def
  apply (simp add:plus2_correct)
  done

(* Prove plus2 with no failure *)
lemma plus2_valid:"\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b \<rbrace>!"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply wp
    apply clarsimp
    apply unat_arith
   apply clarsimp
   apply unat_arith
  apply clarsimp
  done

end

end
