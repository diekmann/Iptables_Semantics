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

signature FEEDBACK =
sig

  exception WantToExit of string
  val numErrors : int ref
  val errorThreshold : int option ref
  val errorStr : Region.t * string -> unit
  val errorStr' : SourcePos.t * SourcePos.t * string -> unit
  val warnStr' : SourcePos.t * SourcePos.t * string -> unit
  val informStr : int * string -> unit
  val informStr' : int * SourcePos.t * SourcePos.t * string -> unit

  val errorf : (string -> unit) ref
  val warnf : (string -> unit) ref
  val informf : (string -> unit) ref

  val verbosity_level : int ref

  val timestamp : string -> string

end

structure Feedback :> FEEDBACK =
struct

exception WantToExit of string
val isSome = Option.isSome

val numErrors = ref 0
val errorThreshold = ref (SOME 10)

fun default s =  (TextIO.output(TextIO.stdErr, s);
                  TextIO.flushOut TextIO.stdErr)

val errorf = ref default
val warnf = ref default
val informf = ref default

val verbosity_level = ref 1

fun informStr (v,s) = if v <= !verbosity_level then !informf (s ^ "\n") else ()
fun informStr' (v,l,r,s) =
    informStr (v,Region.toString(Region.make {left = l, right = r}) ^ ": " ^ s)

fun errorStr (r, s) = let
in
  !errorf (Region.toString r ^ ": " ^ s ^ "\n");
  numErrors := !numErrors + 1;
  if isSome (!errorThreshold) andalso !numErrors > valOf (!errorThreshold) then
    raise WantToExit "Too many errors - aborted."
  else ()
end

fun errorStr' (l,r,s) = errorStr(Region.make {left = l, right = r}, s)


fun warnStr' (l,r,s) =
    !warnf ("Warning "^SourcePos.toString l^ " " ^ s ^ "\n")

fun timestamp s = Time.fmt 0 (Time.now()) ^ ": " ^ s

end; (* struct *)


