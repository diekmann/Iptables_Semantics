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

(* this is an -*- sml -*- file *)
structure RecursiveRecordPP =
struct

(* a chunk of RecordPackage.ML ripped violently free of its shackles *)


(* this much handles pretty-printing record field updates *)
val updateN = Record.updateN

fun gen_field_upds_tr' mark sfx (tm as Const (name_field, _) $ k $ u) =
  let val t = (case k of (Abs (_,_,(Abs (_,_,t)$Bound 0)))
                  => if null (loose_bnos t) then t else raise Match
               | Abs (_,_,t) => if null (loose_bnos t) then t else raise Match
               | _ => raise Match)
  in
    (case try (unsuffix sfx) name_field of
      SOME name =>
        apfst (cons (Syntax.const mark $ Syntax.free name $ t)) (gen_field_upds_tr' mark sfx u)
     | NONE => ([], tm))
  end
  | gen_field_upds_tr' _ _ tm = ([], tm);

fun record_update_tr' _ tm =
  let val (ts, u) = gen_field_upds_tr' "_update" updateN tm in
    if null ts then raise Match
    else Syntax.const "_record_update" $ u $
          foldr1 (fn (v, w) => Syntax.const "_updates" $ v $ w) (rev ts)
  end;

fun gen_field_tr' sfx tr' name =
  let val name_sfx = suffix sfx name
  in (name_sfx, fn ctxt => fn [t, u] => tr' ctxt (Syntax.const name_sfx $ t $ u) | _ => raise Match) end;

fun print_translation names =
  map (gen_field_tr' updateN record_update_tr') names;


fun install_translations
      {record_name = _, fields : {fldname : string, fldty : typ} list} thy =
let
  val field_tr's = print_translation (map #fldname fields)
in
  Sign.print_translation field_tr's thy
end

end;
