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

 * Slightly adjusted by Michael Norrish (2006)

 *)

signature SOURCE_POS =
sig

  type t

  val bogus: t
  val column: t -> int
  val compare: t * t -> order
  val equals: t * t -> bool
  val file: t -> string
  val line: t -> int
  val make: {column: int, file: string, line: int} -> t
  val toString: t -> string
  val posToString : t -> string
end

structure SourcePos : SOURCE_POS =
struct

datatype t = T of {column: int, file: string, line: int}

local
   fun f g (T r) = g r
in
   val column = f #column
   val line = f #line
end

fun compare (T {column = c, file = f, line = l},
	     T {column = c', file = f', line = l'}) =
   case String.compare (f, f') of
      EQUAL =>
	 (case Int.compare (l, l') of
	     EQUAL => Int.compare (c, c')
	   | r => r)
    | r => r

fun equals (T r, T r') = r = r'

fun make {column, file, line} =
   T {column = column,
      file = file,
      line = line}

fun file (p as T {file, ...}) = file

val bogus = T {column = ~1,
	       file = "<bogus>",
	       line = ~1}

fun toString (p as T {column, line, ...}) =
   String.concat [file p, " ", Int.toString line, ".", Int.toString column]

fun posToString (T {column,line,...}) =
   String.concat [Int.toString line, ".", Int.toString column]

end
