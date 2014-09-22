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
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val dir = valOf (OS.Process.getEnv "STP_PFX")

infix |>
fun x |> f = f x

fun readmlb fname = let
  val istr = TextIO.openIn fname
  fun recurse () =
      case TextIO.inputLine istr of
        NONE => ()
      | SOME s => let
          open Substring
          val s = s |> full |> dropr Char.isSpace |> dropl Char.isSpace |> string
          val lower_s = CharVector.map Char.toLower s
        in
          if not (String.isPrefix "mlton" lower_s) andalso
             (String.isSuffix "ml" lower_s orelse String.isSuffix "sig" lower_s)
          then
            use (dir ^ "/" ^ s)
          else ();
          recurse ()
        end
in
  recurse ()
end

structure MLton =
struct
  val eq = PolyML.pointerEq
end;

val _ = app (fn s => use (dir ^ "/../" ^ s))
        ["tools/mlyacc/mlyacclib/MLY_base-sig.ML",
         "tools/mlyacc/mlyacclib/MLY_join.ML",
         "tools/mlyacc/mlyacclib/MLY_lrtable.ML",
         "tools/mlyacc/mlyacclib/MLY_stream.ML",
         "tools/mlyacc/mlyacclib/MLY_parser2.ML"]

val _ = readmlb (dir ^ "/tokenizer.mlb");


fun main() = Main.doit (CommandLine.arguments())

val _ = PolyML.shareCommonData main;
val _ = PolyML.export(dir ^ "/tokenizer", main);
