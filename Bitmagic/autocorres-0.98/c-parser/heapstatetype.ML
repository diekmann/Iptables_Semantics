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

signature HEAPSTATETYPE =
sig

  val hst_prove_globals : string -> theory -> theory
   (* string is the fully expanded name of the global record type *)

end

structure HeapStateType : HEAPSTATETYPE =
struct

open TermsTypes
open UMM_TermsTypes

fun hst_mem_lhs_t ty = Const(@{const_name "hst_mem"}, ty --> heap_ty)
fun hst_mem_rhs_t hrs ty =
    mk_comp_t (ty, heap_raw_ty, heap_ty) $ mk_hrs_mem_t $
	      Const(hrs, ty --> heap_raw_ty)
fun hst_mem_update_lhs_t ty = Const(@{const_name "hst_mem_update"},
    (heap_ty --> heap_ty) --> ty --> ty)
fun hst_mem_update_rhs_t hrs ty =
    mk_comp_t (heap_ty --> heap_ty, heap_raw_ty --> heap_raw_ty, ty --> ty) $
	      Const(hrs^"_update", (heap_raw_ty --> heap_raw_ty) --> ty --> ty) $ mk_hrs_mem_update_t


fun hst_htd_lhs_t ty = Const(@{const_name "hst_htd"}, ty --> heap_desc_ty)
fun hst_htd_rhs_t hrs ty =
    mk_comp_t (ty, heap_raw_ty, heap_desc_ty) $ mk_hrs_htd_t $
	      Const(hrs, ty --> heap_raw_ty)
fun hst_htd_update_lhs_t ty = Const(@{const_name "hst_htd_update"},
    (heap_desc_ty --> heap_desc_ty) --> ty --> ty)
fun hst_htd_update_rhs_t hrs ty =
    mk_comp_t (heap_desc_ty --> heap_desc_ty, heap_raw_ty --> heap_raw_ty, ty --> ty) $
	      Const(hrs^"_update", (heap_raw_ty --> heap_raw_ty) --> ty --> ty) $ mk_hrs_htd_update_t


fun hst_prove_globals fullrecname thy = let
  val recty = Type(fullrecname, [TVar(("'a",0), ["HOL.type"])])
  val hst'_instance_t =
      Logic.mk_of_class(recty, "SepFrame.heap_state_type'")
  val hst'_instance_ct = cterm_of thy hst'_instance_t
  val is_hst'_thm =
      Goal.prove_internal (thy2ctxt thy) [] hst'_instance_ct
                          (fn _ => Class.intro_classes_tac [])
  val thy = Axclass.add_arity is_hst'_thm thy
  val recty' =  Type(fullrecname, [alpha])
  val hrs = Sign.intern_const thy NameGeneration.global_heap_var
  val triples =
      [("hst_mem_",hst_mem_lhs_t,hst_mem_rhs_t),
       ("hst_mem_update",hst_mem_update_lhs_t,hst_mem_update_rhs_t),
       ("hst_htd_",hst_htd_lhs_t,hst_htd_rhs_t),
       ("hst_htd_update",hst_htd_update_lhs_t,hst_htd_update_rhs_t)]
  val defs = map (fn (n,l,r) =>
                     ((Binding.name (n ^ NameGeneration.global_rcd_name),
		       mk_defeqn(l recty', r hrs recty')),
		      []))
                 triples
  val (hst_thms, thy) = Global_Theory.add_defs true defs thy
  val thy' = thy |> Context.theory_map (Simplifier.map_ss (fn ss => ss addsimps hst_thms))
  val hst_instance_t =
      Logic.mk_of_class(recty, "SepFrame.heap_state_type")
  val hst_instance_ct = cterm_of thy' hst_instance_t
  val hst_thms = @{thms "hrs_simps"} @ [@{thm "split_def"}]
  val is_hst_thm =
      Goal.prove_internal (thy2ctxt thy)
          [] hst_instance_ct
          (fn _ =>
              Class.intro_classes_tac [] THEN
              ALLGOALS (asm_full_simp_tac
                            (thy2ctxt thy' addsimps hst_thms)))
in
  Axclass.add_arity is_hst_thm thy'
end
end (* struct *)
