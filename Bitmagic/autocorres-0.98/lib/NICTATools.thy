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

(* Miscellaneous Isabelle tools. *)
theory NICTATools
imports Apply_Trace_Cmd
begin

section "Detect unused meta-forall"

(*
 * Detect meta-foralls that are unused in "lemma" statements,
 * and warn the user about them.
 *
 * They can sometimes create weird issues, usually due to the
 * fact that they have the empty sort "'a::{}", which confuses
 * certain tools, such as "atomize".
 *)
ML {*

(* Return a list of meta-forall variable names that appear
 * to be unused in the input term. *)
fun find_unused_metaall (Const (@{const_name "Pure.all"}, _) $ Abs (n, _, t)) =
      (if not (Term.is_dependent t) then [n] else []) @ find_unused_metaall t
  | find_unused_metaall (Abs (_, _, t)) =
      find_unused_metaall t
  | find_unused_metaall (a $ b) =
      find_unused_metaall a @ find_unused_metaall b
  | find_unused_metaall _ = []

(* Given a proof state, analyse its assumptions for unsued
 * meta-foralls. *)
fun detect_unused_meta_forall _ (state : Proof.state) =
let
  (* Fetch all assumptions and the main goal, and analyse them. *)
  val {context = lthy, goal = goal, ...} = Proof.goal state
  val checked_terms =
      [concl_of goal] @ map term_of (Assumption.all_assms_of lthy)
  val results = List.concat (map find_unused_metaall checked_terms)

  (* Produce a message. *)
  fun message results =
    Pretty.paragraph [
      Pretty.str "Unused meta-forall(s): ",
      Pretty.commas
        (map (fn b => Pretty.mark_str (Markup.bound, b)) results)
      |> Pretty.paragraph,
      Pretty.str "."
    ]

  (* We use a warning instead of the standard mechanisms so that
   * we can produce a "warning" icon in Isabelle/jEdit. *)
  val _ =
    if length results > 0 then
      warning (message results |> Pretty.str_of)
    else ()
in
  (false, ("", state))
end

(* Setup the tool, stealing the "auto_solve_direct" option. *)
val _ = Try.tool_setup ("unused_meta_forall",
    (1, @{system_option auto_solve_direct}, detect_unused_meta_forall))

*}

lemma test_unused_meta_forall: "\<And>x. y \<or> \<not> y"
  oops

end
