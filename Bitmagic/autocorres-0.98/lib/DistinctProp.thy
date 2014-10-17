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
   Miscellaneous library definitions and lemmas.
*)

header "Distinct Proposition"

theory DistinctProp
imports
  "../lib/Lib"
  "~~/src/HOL/Library/Sublist"
begin

text {* distinct\_prop *}

primrec
  distinct_prop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
where
  "distinct_prop P [] = True"
| "distinct_prop P (x # xs) = ((\<forall>y\<in>set xs. P x y) \<and> distinct_prop P xs)"

lemma distinct_prop_map:
  "distinct_prop P (map f xs)
    = distinct_prop (\<lambda>x y. P (f x) (f y)) xs"
  apply (induct xs)
   apply simp
  apply simp
  done

lemma distinct_prop_append:
  "distinct_prop P (xs @ ys) =
    (distinct_prop P xs \<and> distinct_prop P ys \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. P x y))"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (simp add: conj_ac ball_Un)
  done

lemma distinct_prop_distinct:
  "\<lbrakk> distinct xs; \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs; x \<noteq> y \<rbrakk> \<Longrightarrow> P x y \<rbrakk>
     \<Longrightarrow> distinct_prop P xs"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply blast
  done

lemma distinct_prop_True [simp]:
  "distinct_prop (\<lambda>x y. True) xs"
  by (induct xs, auto)

end
