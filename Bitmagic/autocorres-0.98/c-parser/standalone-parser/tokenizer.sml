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

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke pi lexstream = let
  val (StrictCParser.Token.TOKEN (nexttok, _), strm') = StrictCParser.Stream.get lexstream
  val tok_s = StrictCLrVals.ParserData.EC.showTerminal nexttok
in
  print (tok_s ^ " ");
  if tok_s <> "EOF" then invoke pi strm' else print "\n"
end

fun lexit (includes : string list) (fname : string) = let
  val includes_string = String.concat (map (fn s => "-I"^s^" ") includes)
  val cpped_fname = let
    open OS.FileSys OS.Process
    val tmpname = tmpName()
  in
    if isSuccess (system ("/usr/bin/cpp " ^ includes_string ^ " -CC " ^ fname ^
                          " > " ^ tmpname))
    then
      tmpname
    else raise Feedback.WantToExit ("cpp failed on "^fname)
  end
  val istream = TextIO.openIn cpped_fname
  val lexarg = StrictCLex.UserDeclarations.new_state fname
  val _ = Feedback.numErrors := 0
  val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
in
  invoke (#source lexarg) lexer before
  (TextIO.closeIn istream;
   if cpped_fname <> fname then
     OS.FileSys.remove cpped_fname
   else ())
end

open OS.Process

fun die s = (print s; print "\n"; exit failure)
fun warn s = (TextIO.output(TextIO.stdErr, s^"\n");
              TextIO.flushOut TextIO.stdErr)

fun usage() = die ("Usage: "^CommandLine.name()^ " filename1 filename2 ...")


fun handle_args acc_incs args =
    case args of
      [] => usage()
    | arg::rest => let
      in
        if String.isPrefix "-I" arg then
          handle_args (String.extract(arg,2,NONE) :: acc_incs) rest
        else let
            val incs = List.rev acc_incs
            val num_errors = List.app (lexit incs) args
          in
            exit success
          end
      end

structure Main = struct fun doit args = handle_args [] args end
