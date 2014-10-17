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

(* Author: Thomas Sewell

  Instance of words in the enumeration class.
*)

header "Enumeration instances for Words"

theory WordEnum
imports Enumeration WordLib
begin

instantiation word :: (len) enum
begin

definition
  "(enum_class.enum :: ('a :: len) word list) \<equiv> map of_nat [0 ..< 2 ^ len_of TYPE('a)]"

definition
  "enum_class.enum_all (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: ('a :: len) word \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

instance
  apply (intro_classes)
     apply (simp add: enum_word_def)
     apply force
    apply (simp add: distinct_map enum_word_def)
    apply (rule subset_inj_on, rule word_unat.Abs_inj_on)
    apply (clarsimp simp add: unats_def)
   apply (simp add: enum_all_word_def)
  apply (simp add: enum_ex_word_def)
  done

end

lemma fromEnum_unat[simp]: "fromEnum (x :: ('a :: len) word) = unat x"
  apply (subgoal_tac "x \<in> set enum")
   defer
   apply (simp add: enum_surj)
  apply (unfold fromEnum_def enum_word_def)
  apply (subgoal_tac "ALL n. n < 2 ^ len_of TYPE('a) --> (map of_nat [0..< 2 ^ len_of TYPE('a)] ! n) = x --> n = unat x")
   apply (subgoal_tac "(map of_nat [0..< 2 ^ len_of TYPE('a)]) ! (the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x) = x")
    apply (subgoal_tac "the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x < 2 ^ len_of TYPE('a)")
     apply simp
    apply (subgoal_tac "the_index (map of_nat [0..< 2 ^ len_of TYPE('a)]) x < length (map of_nat [0..< 2 ^ len_of TYPE('a)])")
     apply simp
    apply (rule the_index_bounded)
    apply (simp add: enum_word_def)
   apply (rule nth_the_index)
   apply (simp add: enum_word_def)
  apply safe
  apply (simp add: unat_of_nat)
  done

lemma length_word_enum: "length (enum :: ('a :: len) word list) = 2 ^ len_of TYPE('a)"
  apply (simp add: enum_word_def)
  done

lemma toEnum_of_nat[simp]: "n < 2 ^ len_of TYPE('a) \<Longrightarrow> ((toEnum n) :: ('a :: len) word) = of_nat n"
  apply (subst toEnum_def)
  apply (simp add: length_word_enum)
  apply (subst enum_word_def)
  apply simp
  done

declare of_nat_diff [simp]
declare word_pow_0 [simp]

lemma "(maxBound :: ('a :: len) word) = -1"
  apply (unfold maxBound_def enum_word_def)
  apply (subst last_map)
   apply simp
  apply simp
  done

lemma "(minBound :: ('a :: len) word) = 0"
  apply (unfold minBound_def enum_word_def)
  apply (simp add: hd_conv_nth)
  done

instantiation word :: (len) enumeration_both
begin

definition
  enum_alt_word_def: "enum_alt \<equiv> alt_from_ord (enum :: ('a :: len) word list)"

instance
  by (intro_classes, simp add: enum_alt_word_def)

end


definition
  upto_enum_step :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 list" ("[_ , _ .e. _]")
where
  "upto_enum_step a b c \<equiv>
      if c < a then [] else map (\<lambda>x. a + x * (b - a)) [0 .e. (c - a) div (b - a)]"
  (* in the wraparound case, bad things happen. *)

end
