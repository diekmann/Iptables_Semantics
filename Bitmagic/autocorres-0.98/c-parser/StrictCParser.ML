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

structure StrictCParser =
struct

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke lookahead pi lexstream = let
  fun print_error (s,lpos,rpos) = Feedback.errorStr'(lpos,rpos,s)
in
  (#1 (StrictCParser.parse(lookahead,lexstream,print_error,pi)), !Feedback.numErrors)
end

fun parse error_lookahead (includes : string list) (fname : string) = let
  val includes_string = String.concat (map (fn s => "-I\""^s^"\" ") includes)
  val cpped_fname = let
    open OS.FileSys OS.Process
    val tmpname = tmpName()
  in
    if isSuccess (system ("/usr/bin/cpp " ^ includes_string ^ " -CC \"" ^ fname ^
                          "\" > " ^ tmpname))
    then
      tmpname
    else raise Feedback.WantToExit ("cpp failed on "^fname)
  end
  val istream = TextIO.openIn cpped_fname
  val _ = Feedback.numErrors := 0 (* FIXME - global reference *)
  val lexarg = StrictCLex.UserDeclarations.new_state fname
  val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
  val pos = #source lexarg
in
  invoke error_lookahead pos lexer before
  (TextIO.closeIn istream;
   if cpped_fname <> fname then
     OS.FileSys.remove cpped_fname
   else ())
end


end;
