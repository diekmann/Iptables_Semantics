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

header "Prettier Printing for Programs"

theory PrettyProgs
imports "hoare-package/Vcg"
begin

syntax (output)
  "_Assign"      :: "'b => 'b => ('a,'p,'f) com"    ("(2_ :==/ _)" [30, 30] 23)

  "_seq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" ("_;;//_" [20, 21] 20)

  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) com"
        ("(0WHILE (_)//INV (_)//_)"  [25, 0, 81] 71)

  "_Do" :: "('a,'p,'f) com \<Rightarrow> bdy" ("DO//  (_)//OD" [0] 1000)

  "_Cond"        :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF _ THEN//  (_)//ELSE//  (_)//FI)" [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF _ THEN//  (_)//FI)" [0, 0] 71)

  "_Try_Catch":: "('a,'p,'f) com \<Rightarrow>('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
        ("(0TRY//  (_)//CATCH _//END)"  [0,0] 71)

end
