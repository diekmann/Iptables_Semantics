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

(*
 * Definition of various attributes.
 *
 * We define it early so that we can tag theorems that are defined prior to
 * the code that uses them.
 *)

structure L1UnfoldThms =
  Named_Thms (
    val name = Binding.name "L1unfold"
    val description = "Definitions unfolded prior to L1 SIMPL to monadic conversion."
    )

structure L1PeepholeThms =
  Named_Thms (
    val name = Binding.name "L1peephole"
    val description = "Peephole optimisations carried out after L1 SIMPL to monadic conversion."
    )

structure L1ExceptionThms =
  Named_Thms (
    val name = Binding.name "L1exception"
    val description = "Exception control flow rewriting"
    )

structure L2UnfoldThms =
  Named_Thms (
    val name = Binding.name "L2unfold"
    val description = "Definitions unfolded prior to L2 monadic conversion from L1."
    )

structure L2PeepholeThms =
  Named_Thms (
    val name = Binding.name "L2peephole"
    val description = "Peephole optimisations carried out after L2 monadic conversion."
    )

structure HeapAbsThms =
  Named_Thms (
    val name = Binding.name "heap_abs"
    val description = "Heap Abstraction Rule"
    )

structure HeapAbsFOThms =
  Named_Thms (
    val name = Binding.name "heap_abs_fo"
    val description = "First-Order Heap Abstraction Rule"
    )

structure WordAbsThms =
  Named_Thms (
    val name = Binding.name "word_abs"
    val description = "Word Abstraction Rule"
    )

structure PolishSimps =
  Named_Thms (
    val name = Binding.name "polish"
    val description = "Final simplification rules."
    )
