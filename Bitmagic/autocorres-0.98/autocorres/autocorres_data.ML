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
 * Definition of context data.
 *)
signature AUTOCORRES_DATA =
sig
  val get_thm: theory -> string -> string -> string -> thm option
  val add_thm: string -> string -> string -> thm -> theory -> theory
  val get_def: theory -> string -> string -> string -> thm option
  val add_def: string -> string -> string -> thm -> theory -> theory

  val debug : theory -> ((string * string * string) * thm) list
end

structure AutoCorresData : AUTOCORRES_DATA =
struct

(* Construct an ordering for 3-ples. *)
fun triple_ord a b c ((x1, y1, z1), (x2, y2, z2)) =
  prod_ord (prod_ord a b) c (((x1, y1), z1), ((x2, y2), z2))

(* Symbol table with three string inputs. *)
structure Symtab3 = Table(
  type key = string * string * string
  val ord = triple_ord fast_string_ord fast_string_ord fast_string_ord
);

(* AutoCorres Context Data. *)
type ac_record = {
  proofs : thm Symtab3.table
};
datatype ac_data = ACData of ac_record;

fun dest_ac_data (ACData x) = x

(* Instantiate AutoCorres Data. *)
structure Terms = Theory_Data(
  type T = ac_data;
  val empty = ACData { proofs = Symtab3.empty };
  val extend = I;
  fun merge (ACData ts1, ACData ts2) =
    ACData {
      proofs = Symtab3.merge Thm.eq_thm (#proofs ts1, #proofs ts2)
    }
)

(* Fetch a theorem. *)
fun get_thm thy filename module fn_name =
  Terms.get thy
  |> dest_ac_data
  |> #proofs
  |> (fn x => Symtab3.lookup x (filename, module, fn_name))

(* Add a theorem. *)
fun add_thm filename module fn_name thm thy =
  Terms.map (fn ACData x =>
    ACData {
      proofs = Symtab3.update_new
          ((filename, module, fn_name), thm) (#proofs x)
    }) thy

(* Fetch a definition. *)
fun get_def thy filename module fn_name =
  get_thm thy filename (module ^ "'def") fn_name

(* Add a definition. *)
fun add_def filename module fn_name =
  add_thm filename (module ^ "'def") fn_name

(* Dump everything. *)
fun debug thy = Terms.get thy |> dest_ac_data |> #proofs |> Symtab3.dest

end
