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

structure ImplementationNumbers :> IMPLEMENTATION_NUMBERS =
struct

open IntInf

fun exp (n, ex) = if ex = 0 then 1
                  else let
                      val q = ex div 2
                      val r = if ex mod 2 = 1 then n else 1
                      val qex = exp (n, q)
                    in
                      qex * qex * r
                    end

val boolWidth = fromInt 8
val charWidth = 8
val shortWidth = 16
val intWidth = 32
val longWidth = 32
val llongWidth = 64
val ptrWidth : int = 32
val CHAR_BIT : int = 8

fun umax width = exp(2, width) - 1
fun max width = exp(2, width - 1) - 1
fun min width = ~(exp(2, width - 1))

val UCHAR_MAX = umax charWidth
val USHORT_MAX = umax shortWidth
val UINT_MAX = umax intWidth
val ULONG_MAX = umax longWidth
val ULLONG_MAX = umax llongWidth

val SCHAR_MAX = max intWidth
val SHORT_MAX = max shortWidth
val INT_MAX = max intWidth
val LONG_MAX = max longWidth
val LLONG_MAX = max llongWidth

val SCHAR_MIN = min charWidth
val SHORT_MIN = min shortWidth
val INT_MIN = min intWidth
val LONG_MIN = min longWidth
val LLONG_MIN = min llongWidth

val char_signedp = false

val CHAR_MAX = UCHAR_MAX
val CHAR_MIN = IntInf.fromInt 0

open CharLitUtil

val charliteral_conversion = uchar_conv {umax=UCHAR_MAX}

end
