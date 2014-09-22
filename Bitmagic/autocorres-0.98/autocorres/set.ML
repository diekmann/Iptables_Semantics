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
 * Sets of items.
 *
 * Currently implemented using sorted lists.
 *)

signature SET =
sig
  type key
  type 'a set

  val empty : key set
  val is_empty : key set -> bool
  val make : key list -> key set
  val dest : key set -> key list
  val inter : key set -> key set -> key set
  val subtract : key set -> key set -> key set
  val union : key set -> key set -> key set
  val union_sets : key set list -> key set
  val insert : key -> key set -> key set
  val contains : key set -> key -> bool
  val subset : (key set * key set) -> bool
  val card: key set -> int
  val map: (key -> key) -> key set -> key set
end;

functor Set(Key: KEY): SET =
struct

type key = Key.key;

(*
 * We wrap everything in a private datatype to enforce the user to only use the
 * abstract interface.
 *)
datatype 'a set = S of 'a list;

(* Make a set from a list. *)
fun make x = Ord_List.make Key.ord x |> S

(* Convert the set back into a list. *)
fun dest (S x) = x

(* Emptiness *)
val empty = S []
fun is_empty (S x) = (length x = 0)

(* Set manipulation. *)
fun inter (S a) (S b) = Ord_List.inter Key.ord a b |> S
fun subtract (S a) (S b) = Ord_List.subtract Key.ord a b |> S
fun union (S a) (S b) = Ord_List.union Key.ord a b |> S
fun insert a (S b) = Ord_List.insert Key.ord a b |> S
fun union_sets l = foldl (fn (a, b) => union a b) empty l
fun contains (S l) a = Ord_List.member Key.ord l a
fun subset (S a, S b) = Ord_List.subset Key.ord (a, b)
fun card (S a) = length a
fun map f (S a) = make (List.map f a)

end;

structure Intset = Set(type key = int val ord = int_ord);
structure Symset = Set(type key = string val ord = fast_string_ord);
structure Varset = Set(type key = (string * typ) val ord =
    fn (a,b) => Term_Ord.var_ord (((fst a, 0), snd a), ((fst b, 0), snd b)));
structure Typset = Set(type key = typ val ord = Term_Ord.typ_ord);

type varset = Varset.key Varset.set
type symset = Symset.key Symset.set
type typset = Typset.key Typset.set

