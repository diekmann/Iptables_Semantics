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

(* This is the "standard" instantiation of the MemoryModelExtras
   signature.

   Other implementations using the parser code may wish to 'use' a different
   file than this one.  The theory is that everything will "just work" as
   long as that file declares a structure MemoryModelExtras matching the
   signature.
*)

structure MemoryModelExtras : MEMORY_MODEL_EXTRAS =
struct

open TermsTypes UMM_TermsTypes
val extended_heap_ty = heap_raw_ty
fun check_safety {heap=h,ptrval} = let
  val heap_desc = mk_hrs_htd_t $ h
in
  (mk_ptr_safe ptrval heap_desc, safety_error)
end

fun dereference_ptr {heap,ptrval} = mk_lift(mk_hrs_mem_t $ heap,ptrval)

fun mk_heap_update_extended t = mk_hrs_mem_update_t $ t

fun mk_aux_guard t = mk_aux_guard_t $ t

fun mk_aux_update t = mk_hrs_htd_update_t $ (mk_aux_heap_desc_t $ t)

fun mk_aux_type ty = mk_auxupd_ty ty

val check_global_record_type = HeapStateType.hst_prove_globals

fun mk_lookup_proc_pair symtab naming addr = let
  val argTs = [fastype_of symtab, fastype_of naming, fastype_of addr]
  in (Const (@{const_name lookup_proc}, argTs ---> int)
        $ symtab $ naming $ addr,
    Const (@{const_name lookup_proc_safe}, argTs ---> HOLogic.boolT)
        $ symtab $ naming $ addr)
  end

structure UserTypeDeclChecking =
struct
  open UMM_Proofs
  type t = T
  type csenv = ProgramAnalysis.csenv
  val initial_state = umm_empty_state
  val finalise = umm_finalise
  fun struct_type _ {struct_type,state} thy =
      umm_struct_calculation (struct_type,state,thy)
  fun array_type _ {element_type, array_size, state} thy =
      umm_array_calculation element_type array_size state thy

end

end
