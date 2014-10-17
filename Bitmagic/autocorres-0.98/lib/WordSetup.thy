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

header "Machine Word Setup"

theory WordSetup
imports WordEnum DistinctProp

begin

text {* This theory defines the standard platform-specific word size
and alignment. *}

definition
  word_bits :: nat where
  "word_bits \<equiv> len_of TYPE(32)"

definition
  word_size :: "'a :: numeral" where
  "word_size \<equiv> 4"

lemma word_bits_conv:
  "word_bits = 32" unfolding word_bits_def by simp

lemma word_bits_word_size_conv:
  "word_bits = word_size * 8"
  unfolding word_bits_def word_size_def by simp

definition
  is_aligned :: "'a :: len word \<Rightarrow> nat \<Rightarrow> bool" where
  "is_aligned ptr n \<equiv> 2^n dvd unat ptr"

definition
  ptr_add :: "word32 \<Rightarrow> nat \<Rightarrow> word32" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  complement :: "('a :: len) word \<Rightarrow> 'a word"  where
 "complement x \<equiv> x xor -1"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 && complement (2 ^ n - 1)"

end
