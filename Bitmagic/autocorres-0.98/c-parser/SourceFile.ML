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
signature SOURCE_FILE =
   sig
      type t

      (* The pos in the following specs is a file position (e.g. yypos of mllex).
       *)
      val getPos: t * int -> SourcePos.t
      val observe_line_directives : bool ref
      val lineDirective:
           t * string option * {lineNum: int, lineStart: int} -> unit
      val lineStart: t -> SourcePos.t

      val new: string -> t
      val newline: t * int -> unit
   end;



structure SourceFile: SOURCE_FILE =
struct

datatype t = T of {file: string ref,
                   lineNum: int ref,
                   lineStart: int ref}

fun getPos (T {file, lineNum, lineStart, ...}, n) =
   SourcePos.make {column = n - !lineStart,
                   file = !file,
                   line = !lineNum}

fun lineStart (s as T {lineStart, ...}) = getPos (s, !lineStart)

val observe_line_directives = ref true

fun new file = T {file = ref file,
                  lineNum = ref 1,
                  lineStart = ref 0}

fun newline (T {lineStart, lineNum, ...}, n) =
   (lineNum := !lineNum + 1
    ; lineStart := n)

fun lineDirective (src as T {file, lineNum, lineStart},
                   f,
                   {lineNum = n, lineStart = s}) =
    if !observe_line_directives then
      (Option.app (fn f => file := f) f
       ; lineNum := n
       ; lineStart := s)
    else newline(src,s)



end;

