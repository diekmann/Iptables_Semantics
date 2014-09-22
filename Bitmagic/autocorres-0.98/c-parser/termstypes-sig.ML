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

signature INT_INFO = sig
  val int : typ
  val long : typ
  val short : typ
  val char : typ
  val bool : typ
  val longlong : typ
  val addr_ty : typ
  val ity_to_nat : term -> term
  val numeral2w : int Absyn.ctype -> int -> term
  val ptrdiff_ity : typ
  val INT_MAX : int
  val INT_MIN : int
  val UINT_MAX : int
  val ity2wty : int Absyn.ctype -> typ
  val nat_to_word : int Absyn.ctype -> term -> term
  val word_to_int : int Absyn.ctype -> term -> term
end

signature TERMS_TYPES =
sig
  include ISABELLE_TERMS_TYPES
  include HP_TERMS_TYPES

  (* Free variables which will be locale parameters *)
  val symbol_table : term

  (* types - words and arrays *)
  val word_ty : typ -> typ
  val word8 : typ
  val word16 : typ
  val word32 : typ
  val word64 : typ

  val dest_array_type : typ -> typ * typ
  val mk_array_type : typ * int -> typ


  (* terms *)
  val mk_array_update_t : typ -> term (* element type *)
  val mk_array_nth : term * term -> term (* number second *)

  structure IntInfo : INT_INFO

  (* Basic machine terms/types - for calculate_state.ML *)
  val mk_ptr_ty : typ -> typ
  val is_ptr_ty : typ -> bool
  val addr_ty : typ
  val mk_okptr : term -> term
  val heap_ty : typ
  val mk_sizeof : term -> term

  (* More terms/types - for expression_translation.ML *)
  val NULLptr : term
  val mk_ptr : term * typ -> term
  val mk_fnptr : theory -> string -> term
  val mk_cguard_ptr : term -> term
  val mk_global_addr_ptr : string * typ -> term

  val dest_ptr_ty : typ -> typ
  val mk_ptr_val : term -> term (* there is a HOL constant "ptr_val" *)
  val mk_ptr_coerce : term * typ -> term
  val mk_ptr_add : term * term -> term
  val mk_lift : term * term -> term


  val mk_lshift : term * term -> term
  val mk_rshift : term * term -> term

  (* Given (addr,value) yield a primitive heap => heap transformer. *)
  val mk_heap_upd : term * term -> term

  val mk_field_lvalue_ptr : Proof.context -> term * term * typ * typ -> term

  val mk_qualified_field_name : string -> term
  val field_name_ty : typ
  val qualified_field_name_ty : typ

  datatype 'varinfo termbuilder =
           TB of {var_updator : bool -> 'varinfo -> term -> term -> term,
                  var_accessor : 'varinfo -> term -> term,
                  rcd_updator : string*string -> term -> term -> term,
                  rcd_accessor : string*string -> term -> term}
                  (* in updator functions, first term is the new value,
                     second is composite value being updated *)

  (* for creation of uint w, and sint w terms *)
  val mk_w2ui : term -> term
  val mk_w2si : term -> term

end
