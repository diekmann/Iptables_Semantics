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
 * Simple test cases for heap_abs_syntax feature.
 * JIRA issue ID: VER-356
 *)
theory HeapWrap
imports "../../AutoCorres"
begin

install_C_file "heap_wrap.c"
autocorres [heap_abs_syntax] "heap_wrap.c"

context heap_wrap begin
thm f1'_def f2'_def f3'_def f4'_def f5'_def f6'_def f7'_def f8'_def
end

context heap_wrap begin

(* simps for working with the new heap wrappers *)
declare [[show_types]]
thm heap_wrap.heap_abs_simps
thm (*heap_wrap.*)heap_abs_simps
declare [[show_types=false]]

(* overloaded syntax is not scalable *)
term "s[p\<rightarrow>right := s[q]\<rightarrow>left][q]\<rightarrow>right = s[r] +\<^sub>p uint (s[t]\<rightarrow>x) \<and>
      s[p\<rightarrow>right := s[q]\<rightarrow>left] = s[q\<rightarrow>left := s[p]\<rightarrow>right] \<and>
      s[t]\<rightarrow>p = s[q]\<rightarrow>p \<and>
      s[ptr_coerce (s[p]\<rightarrow>p) :: 32 word ptr] = ucast (s[q]\<rightarrow>x)"

end

end
