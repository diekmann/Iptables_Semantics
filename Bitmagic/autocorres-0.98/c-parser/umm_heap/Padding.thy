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

theory Padding
imports "~~/src/HOL/Main"
begin

definition padup :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "padup align n \<equiv> (align - n mod align) mod align"

lemma padup_dvd:
  "0 < b \<Longrightarrow> (padup b n = 0) = (b dvd n)"
apply(clarsimp simp: padup_def dvd_eq_mod_eq_0)
apply(subst mod_if [where m="b - n mod b"])
apply clarsimp
apply(insert mod_less_divisor [of b n])
apply arith
done

lemma mod_triv_le:
  "0 < n \<Longrightarrow> m mod (n::nat) \<le> m"
apply(case_tac "m < n")
 apply simp
apply(subgoal_tac "m mod n < n")
 apply arith
apply(erule mod_less_divisor)
done

lemma dvd_padup_add:
  "0 < x \<Longrightarrow> x dvd y + padup x y"
apply(clarsimp simp: padup_def)
apply(subst mod_if [where m="x - y mod x"])
apply(clarsimp split: split_if_asm)
apply(rule conjI)
 apply clarsimp
 apply(subst ac_simps)
 apply(subst diff_add_assoc)
  apply(rule mod_triv_le)
  apply simp
 apply(rule dvd_add)
  apply simp
 apply(subst mod_div_equality')
 apply(subst diff_diff_right)
  apply(subst ac_simps)
  apply(subst mult_div_cancel)
  apply simp
 apply simp
apply(auto simp: dvd_eq_mod_eq_0)
done


end
