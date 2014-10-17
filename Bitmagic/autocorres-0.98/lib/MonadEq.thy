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
 * Tactic for solving monadic equalities, such as:
 *
 * (liftE (return 3) = returnOk 3
 *
 * Theorems of the form:
 *
 *   ((a, s') \<in> fst (A s)) = P a s s'
 *
 * and
 *
 *   snd (A s) = P s
 *
 * are added to the "monad_eq" set.
 *)
theory MonadEq
imports "wp/NonDetMonadVCG"
begin

(* Setup "monad_eq" attributes. *)
ML {*
structure MonadEqThms = Named_Thms (
    val name = Binding.name "monad_eq"
    val description = "monad equality-prover theorems"
    )
*}
attribute_setup monad_eq = {*
  Attrib.add_del
    (Thm.declaration_attribute MonadEqThms.add_thm)
    (Thm.declaration_attribute MonadEqThms.del_thm) *}
  "Monad equality-prover theorems"

(* Setup tactic. *)

ML {*
fun monad_eq_tac ctxt =
let
  (* Set a simpset as being hidden, so warnings are not printed from it. *)
  val ctxt' = Context_Position.set_visible false ctxt
in
  CHANGED (clarsimp_tac (ctxt' addsimps (MonadEqThms.get ctxt')) 1)
end
*}

method_setup monad_eq = {*
    Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD o monad_eq_tac)) *}
  "prove equality on monads"

lemma monad_eq_simp_state [monad_eq]:
  "((A :: ('s, 'a) nondet_monad) s = B s') =
      ((\<forall>r t. (r, t) \<in> fst (A s) \<longrightarrow> (r, t) \<in> fst (B s'))
         \<and> (\<forall>r t. (r, t) \<in> fst (B s') \<longrightarrow> (r, t) \<in> fst (A s))
         \<and> (snd (A s) = snd (B s')))"
  apply (auto intro!: set_eqI prod_eqI)
  done

lemma monad_eq_simp [monad_eq]:
  "((A :: ('s, 'a) nondet_monad) = B) =
      ((\<forall>r t s. (r, t) \<in> fst (A s) \<longrightarrow> (r, t) \<in> fst (B s))
         \<and> (\<forall>r t s. (r, t) \<in> fst (B s) \<longrightarrow> (r, t) \<in> fst (A s))
         \<and> (\<forall>x. snd (A x) = snd (B x)))"
  apply (auto intro!: set_eqI prod_eqI)
  done

declare in_monad [monad_eq]
declare in_bindE [monad_eq]

(* Test *)
lemma "returnOk 3 = liftE (return 3)"
  apply monad_eq
  oops

end
