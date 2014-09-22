(*
 * Copyright (C) 2014, National ICT Australia Limited. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 *  * The name of National ICT Australia Limited nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

theory AutoCorresAttributes
imports "~~/src/HOL/Main"
begin

ML_file "attributes.ML"

attribute_setup L1opt = {*
  Attrib.add_del
    (Thm.declaration_attribute L1PeepholeThms.add_thm)
    (Thm.declaration_attribute L1PeepholeThms.del_thm) *}
  "Peephole optimisations carried out after L1 SIMPL to monadic conversion."

attribute_setup L1unfold = {*
  Attrib.add_del
    (Thm.declaration_attribute L1UnfoldThms.add_thm)
    (Thm.declaration_attribute L1UnfoldThms.del_thm) *}
  "Definitions unfolded prior to L1 SIMPL to monadic conversion."

attribute_setup L1except = {*
  Attrib.add_del
    (Thm.declaration_attribute L1ExceptionThms.add_thm)
    (Thm.declaration_attribute L1ExceptionThms.del_thm) *}
  "Definitions used to rewrite control flow to reduce exception usage."

attribute_setup L2opt = {*
  Attrib.add_del
    (Thm.declaration_attribute L2PeepholeThms.add_thm)
    (Thm.declaration_attribute L2PeepholeThms.del_thm) *}
  "Peephole optimisations carried out after L2 monadic conversion."

attribute_setup L2unfold = {*
  Attrib.add_del
    (Thm.declaration_attribute L2UnfoldThms.add_thm)
    (Thm.declaration_attribute L2UnfoldThms.del_thm) *}
  "Definitions unfolded prior to L2 monadic conversion from L1."

attribute_setup heap_abs = {*
  Attrib.add_del
    (Thm.declaration_attribute HeapAbsThms.add_thm)
    (Thm.declaration_attribute HeapAbsThms.del_thm) *}
  "Heap abstraction rules."

attribute_setup heap_abs_fo = {*
  Attrib.add_del
    (Thm.declaration_attribute HeapAbsFOThms.add_thm)
    (Thm.declaration_attribute HeapAbsFOThms.del_thm) *}
  "First-order Heap abstraction rules."

attribute_setup word_abs = {*
  Attrib.add_del
    (Thm.declaration_attribute WordAbsThms.add_thm)
    (Thm.declaration_attribute WordAbsThms.del_thm) *}
  "Word abstraction rules."

attribute_setup polish = {*
  Attrib.add_del
    (Thm.declaration_attribute PolishSimps.add_thm)
    (Thm.declaration_attribute PolishSimps.del_thm) *}
  "Final simplification rules."

(* Set up the ts_rule attribute. *)
ML_file "monad_types.ML"
setup {*
 Attrib.setup (Binding.name "ts_rule") Monad_Types.ts_attrib
              "AutoCorres type strengthening rule"
*}

end
