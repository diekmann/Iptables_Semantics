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

signature REGION_EXTRAS =
sig
  type 'a wrap
  val bogus : SourcePos.t
  val wrap : 'a * SourcePos.t * SourcePos.t -> 'a wrap
  val bogwrap : 'a -> 'a wrap
  val left : 'a wrap -> SourcePos.t
  val right : 'a wrap -> SourcePos.t
  val node : 'a wrap -> 'a
  val apnode : ('a -> 'b) -> 'a wrap -> 'b wrap
end

structure RegionExtras =
struct

val bogus = SourcePos.bogus
type 'a wrap = 'a Region.Wrap.t
fun wrap (x,l,r) = Region.Wrap.makeRegion'(x,l,r)
fun bogwrap x = wrap(x,bogus,bogus)
fun left w =
    valOf (Region.left (Region.Wrap.region w)) handle Option => bogus
fun right w =
    valOf (Region.right (Region.Wrap.region w))
    handle Option => bogus
val node = Region.Wrap.node

fun apnode f x_w = let
  val x = node x_w
in
  wrap (f x, left x_w, right x_w)
end

end (* struct *)
