(*
 * STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.
 * Copyright (c) 1989-1998 by Lucent Technologies
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose and without fee is hereby granted,
 * provided that the above copyright notice appear in all copies and that
 * both the copyright notice and this permission notice and warranty
 * disclaimer appear in supporting documentation, and that the name of
 * Lucent Technologies, Bell Labs or any Lucent entity not be used in
 * advertising or publicity pertaining to distribution of the software
 * without specific, written prior permission.
 *
 * Lucent disclaims all warranties with regard to this software, including
 * all implied warranties of merchantability and fitness. In no event shall
 * Lucent be liable for any special, indirect or consequential damages or
 * any damages whatsoever resulting from loss of use, data or profits,
 * whether in an action of contract, negligence or other tortious action,
 * arising out of or in connection with the use or performance of this
 * software.
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi
 *
 * $Log$
 * Revision 1.1  2006/06/22 07:40:27  michaeln
 * Add a MoscowML compilable implementation of MLyacc, using the MLton sources
 * as the base.
 *
 * Revision 1.2  1997/05/23 16:21:10  dbm
 *   SML '97 sharing, where clauses.
 *
# Revision 1.1.1.1  1997/01/14  01:38:06  george
#   Version 109.24
#
 * Revision 1.2  1996/02/26  15:02:38  george
 *    print no longer overloaded.
 *    use of makestring has been removed and replaced with Int.toString ..
 *    use of IO replaced with TextIO
 *
 * Revision 1.1.1.1  1996/01/31  16:01:46  george
 * Version 109
 *
 *)

functor ParseGenParserFun(structure Header : HEADER
			  structure Parser : ARG_PARSER
			    where type pos = Header.pos
			  sharing type Parser.result = Header.parseResult
			  sharing type Parser.arg = Header.inputSource =
			                  Parser.lexarg
			 ) : PARSE_GEN_PARSER =

 struct
      structure Header = Header
      val parse = fn file =>
          let
	      val in_str = TextIO.openIn file
	      val source = Header.newSource(file,in_str,TextIO.stdOut)
	      val error = fn (s : string,i:int,_) =>
		              Header.error source i s
	      val stream =  Parser.makeLexer (fn i => (TextIO.inputN(in_str,i)))
		            source
	      val (result,_) = (Header.lineno := 1;
				Header.text := nil;
		                Parser.parse(15,stream,error,source))
	   in (TextIO.closeIn in_str; (result,source))
	   end
  end;
