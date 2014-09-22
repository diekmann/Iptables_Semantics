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

signature IMPLEMENTATION_NUMBERS =
sig

  type int = IntInf.int
  val UCHAR_MAX : int
  val USHORT_MAX : int
  val UINT_MAX : int
  val ULONG_MAX : int
  val ULLONG_MAX : int

  val SCHAR_MAX : int
  val CHAR_MAX : int
  val SHORT_MAX : int
  val INT_MAX : int
  val LONG_MAX : int
  val LLONG_MAX : int

  val SCHAR_MIN : int
  val CHAR_MIN : int
  val SHORT_MIN : int
  val INT_MIN : int
  val LONG_MIN : int
  val LLONG_MIN : int

  val char_signedp : bool

  val CHAR_BIT : int
  val boolWidth : int
  val charWidth : int
  val shortWidth : int
  val intWidth : int
  val longWidth : int
  val llongWidth : int
  val ptrWidth : int

  exception BadChar
  val charliteral_conversion : int -> int

end

signature CHAR_LIT_UTIL =
sig
  exception BadChar
  type int = IntInf.int
  val schar_conv : {umax:int,smin:int,smax:int} -> int -> int
  val uchar_conv : {umax:int} -> int -> int
end

structure CharLitUtil :> CHAR_LIT_UTIL =
struct
open IntInf
exception BadChar
fun schar_conv {umax,smin,smax} i = let
  val _ = 0 <= i andalso i <= umax orelse
          raise BadChar
in
  if i > smax then smin + i
  else i
end
fun uchar_conv {umax} i = let
  val _ = 0 <= i andalso i <= umax orelse
          raise BadChar
in
  i
end

end
