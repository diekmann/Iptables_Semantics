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

theory AbstractArrays
imports
  "../lib/TypHeapLib"
  "../lib/WordLemmaBucket"
begin

(*
 * Return a list of addresses that contain an element for an array at location
 * "p" of length "n".
 *)
primrec
  array_addrs :: "('a::mem_type) ptr \<Rightarrow> nat \<Rightarrow> 'a ptr list"
where
  "array_addrs _ 0 = []"
| "array_addrs p (Suc n) = p # (array_addrs (p +\<^sub>p 1) n)"

declare array_addrs.simps(2) [simp del]

(* The first element is in the array if the array has non-zero length. *)
lemma hd_in_array_addrs [simp]:
  "(x \<in> set (array_addrs x n)) = (n > 0)"
  by (case_tac n, auto simp: array_addrs.simps(2))

lemma array_addrs_1 [simp]:
  "array_addrs p (Suc 0) = [p]"
  "array_addrs p 1 = [p]"
  by (auto simp: array_addrs.simps(2))

(* All array elements are aligned if the array itself is aligned. *)
lemma array_addrs_ptr_aligned:
     "\<lbrakk> x \<in> set (array_addrs p n); ptr_aligned p \<rbrakk> \<Longrightarrow> ptr_aligned x"
  apply (induct n arbitrary: x p)
   apply clarsimp
  apply (clarsimp simp: array_addrs.simps(2))
  apply (erule disjE)
   apply clarsimp
  apply atomize
  apply (drule_tac x=x in spec)
  apply (drule_tac x="p +\<^sub>p 1" in spec)
  apply (clarsimp simp: ptr_aligned_plus)
  done

(* Split off the last element in an array. *)
lemma set_array_addrs_unfold_last:
  shows "set (array_addrs a (Suc n)) = set (array_addrs a n) \<union> {(a :: ('a::mem_type) ptr) +\<^sub>p int n}"
    (is "?LHS a n = ?RHS a n")
proof (induct n arbitrary: a)
  fix a
  show "?LHS a 0 = ?RHS a 0"
    by clarsimp
next
  fix a n
  assume induct: "\<And>a. ?LHS a n = ?RHS a n"
  show "?LHS a (Suc n) = ?RHS a (Suc n)"
  apply (subst array_addrs.simps(2))
  apply (subst set_simps)
  apply (subst induct [where a="a +\<^sub>p 1"])
  apply (subst array_addrs.simps(2))
  apply (subst set_simps)
  apply (clarsimp simp: CTypesDefs.ptr_add_def field_simps insert_commute)
  done
qed

(* Alternative representation of the set of array elements. *)
lemma set_array_addrs:
  "set (array_addrs (p :: ('a::mem_type) ptr) n)
           = {x. \<exists>k. x = p +\<^sub>p int k \<and> k < n }"
  apply (induct n arbitrary: p)
   apply (clarsimp simp: not_less)
  apply (subst set_array_addrs_unfold_last)
  apply atomize
  apply (drule_tac x=p in spec)
  apply (erule ssubst)
  apply (rule set_eqI)
  apply (rule iffI)
   apply clarsimp
   apply (erule disjE)
    apply clarsimp
    apply force
   apply force
  apply clarsimp
  apply (drule_tac x=k in spec)
  apply (clarsimp simp: not_less)
  apply (subgoal_tac "k = n")
   apply clarsimp
  apply clarsimp
  done

end

