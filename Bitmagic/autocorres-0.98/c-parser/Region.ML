(*
 * This is the license for MLton, a whole-program optimizing compiler for
 * the Standard ML programming language.  Send comments and questions to
 * MLton@mlton.org.
 *
 * MLton COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.
 *
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 by the NEC Research Institute
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose and without fee is hereby granted,
 * provided that the above copyright notice appear in all copies and that
 * both the copyright notice and this permission notice and warranty
 * disclaimer appear in supporting documentation, and that the name of
 * NEC, or any NEC entity not be used in advertising or publicity
 * pertaining to distribution of the software without specific, written
 * prior permission.
 *
 * NEC disclaims all warranties with regard to this software, including
 * all implied warranties of merchantability and fitness. In no event
 * shall NEC be liable for any special, indirect or consequential damages
 * or any damages whatsoever resulting from loss of use, data or profits,
 * whether in an action of contract, negligence or other tortious action,
 * arising out of or in connection with the use or performance of this
 * software.
 *)

(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * Please see the file MLton-LICENSE for license information.
 *)
signature REGION =
   sig

      type t

      val <= : t * t -> bool
      val append: t * t -> t
      val bogus: t
      val compare: t * t -> order
      val equals: t * t -> bool
      val extendRight: t * SourcePos.t -> t
      val left: t -> SourcePos.t option
      val list: 'a list * ('a -> t) -> t
      val make: {left: SourcePos.t, right: SourcePos.t} -> t
      val right: t -> SourcePos.t option
      val toString: t -> string

      structure Wrap:
	 sig
	    type region
	    type 'a t
	    val region: 'a t -> region
	    val node: 'a t -> 'a
	    val makeRegion: 'a * region -> 'a t
	    val makeRegion':  'a * SourcePos.t * SourcePos.t -> 'a t
	    val dest: 'a t -> 'a * region
	 end
      sharing type Wrap.region = t
   end


structure Region: REGION =
struct

datatype t =
   Bogus
 | T of {left: SourcePos.t,
	 right: SourcePos.t}

val bogus = Bogus

local
   fun make f r =
      case r of
	 Bogus => NONE
       | T r => SOME (f r)
in
   val left = make #left
   val right = make #right
end

val extendRight =
   fn (Bogus, _) => Bogus
    | (T {left, ...}, right) => T {left = left, right = right}

val toString =
   fn Bogus => "Bogus"
    | T {left, right} =>
	 String.concat [SourcePos.file left, ":",
		 SourcePos.posToString left, "-", SourcePos.posToString right]

val make = T

val append =
   fn (Bogus, r) => r
    | (r, Bogus) => r
    | (T {left, ...}, T {right, ...}) => T {left = left, right = right}

fun list (xs, reg) = List.foldl (fn (x, r) => append (reg x, r)) Bogus xs

fun compare (r, r') =
   case (left r, left r') of
      (NONE, NONE) => EQUAL
    | (NONE, _) => LESS
    | (_, NONE) => GREATER
    | (SOME p, SOME p') => SourcePos.compare (p, p')

fun equals (r, r') = compare (r, r') = EQUAL

fun r <= r' =
   case compare (r, r') of
      EQUAL => true
    | GREATER => false
    | LESS => true

structure Wrap =
   struct
      type region = t
      datatype 'a t = T of {node: 'a,
			    region: region}

      fun node (T {node, ...}) = node
      fun region (T {region, ...}) = region
      fun makeRegion (node, region) = T {node = node, region = region}
      fun makeRegion' (node, left, right) = T {node = node,
					       region = make {left = left,
							      right = right}}

      fun dest (T {node, region}) = (node, region)
   end

end

