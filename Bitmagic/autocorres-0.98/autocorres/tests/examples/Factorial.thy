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
Termination for recursive functions.
*)
theory Factorial
imports
  "../../AutoCorres"
  "../../../lib/OptionMonadWP"
begin

(* Parse the input file. *)
install_C_file "factorial.c"

autocorres "factorial.c"

context factorial begin

(* Termination *)
thm factorial'.simps
thm l1_call_factorial_def

lemma ovalidNF_grab_asm2:
  "ovalidNF (\<lambda>s. G \<and> P s) f Q \<Longrightarrow> G \<Longrightarrow> ovalidNF P f Q"
  by (auto simp: ovalidNF_def)

lemma ovalidNF_grab_asm_eq:
  "(G \<longrightarrow> ovalidNF P f Q) = ovalidNF (\<lambda>s. G \<and> P s) f Q"
  by (auto simp: ovalidNF_def)

lemma ovalid_post_triv:
  "(\<And>r s. Q r s) \<Longrightarrow> ovalid P f Q"
  by (simp add: ovalid_def)

lemma factorial'_terminates: "no_ofail (\<lambda>_. m > unat n) (factorial' m n)"
proof (induct n arbitrary: m rule: less_induct)
   fix x m
   assume induct_asm0: "(\<And>y m. y < x \<Longrightarrow> no_ofail (\<lambda>_. unat y < m) (factorial' m y))"
   have induct_asm: "(\<And>y m. no_ofail (\<lambda>_. y < x \<and> unat y < m) (factorial' m y))"
     apply (rule no_ofail_grab_asm)
     by (rule induct_asm0)

   show "no_ofail (\<lambda>_. unat x < m) (factorial' m x)"
     apply (subst factorial'.simps)
     apply (wp induct_asm ovalid_post_triv)
     apply unat_arith
    done
qed

lemma factorial'_terminates_old: "m > unat n \<longrightarrow> factorial' m n s \<noteq> None"
  apply (induct n arbitrary: m)
   apply (subst factorial'.simps, simp add: ocondition_def obind_def)
  apply (subst factorial'.simps, simp add: ocondition_def obind_def split: option.splits)
  apply (metis One_nat_def Suc_eq_plus1 less_diff_conv option.distinct(1) unatSuc)
  done

(* A fun fact *)
function fact :: "('n :: len) word \<Rightarrow> ('n :: len) word" where
  "fact n = (if n = 0 then 1 else n * fact (n - 1))"
  by auto
termination by (metis "termination" in_measure measure_unat wf_measure)
declare fact.simps [simp del]

(* Termination & correctness *)
lemma factorial'_correct: "ovalidNF (\<lambda>_. m > unat n) (factorial' m n) (\<lambda>r _. r = fact n)"
proof (induct n arbitrary: m)
   fix n m
   show "ovalidNF (\<lambda>_. unat 0 < m) (factorial' m 0) (\<lambda>r _. r = fact 0)"
     apply (subst factorial'.simps)
     apply (simp add: ovalidNF_def ocondition_def ofail_def oreturn_def obind_def fact.simps)
     done

   assume induct_asm0: "\<And>m. ovalidNF (\<lambda>_. unat n < m) (factorial' m n) (\<lambda>r _. r = fact n)"
   have induct_asm: "\<And>m. 1 + n \<noteq> 0 \<Longrightarrow> ovalidNF (\<lambda>_. unat n < m) (factorial' m n) (\<lambda>r _. (1 + n) * r = fact (1 + n))"
     apply (subst fact.simps)
     apply simp
     apply (insert induct_asm0)
     apply (unfold ovalidNF_def)
     apply simp
     done

   show "\<lbrakk> 1 + n \<noteq> 0 \<rbrakk>
          \<Longrightarrow> ovalidNF (\<lambda>_. unat (1 + n) < m) (factorial' m (1 + n))
              (\<lambda>r _. r = fact (1 + n))"
     apply (subst factorial'.simps)
     apply (rule_tac G = "1 + n \<noteq> 0" in ovalidNF_grab_asm2)
      apply wp
       apply (simp del: One_nat_def)
       apply (wp induct_asm)
       apply assumption
      apply unat_arith
     apply assumption
    done
qed

lemma factorial'_correct_old: "m > unat n \<longrightarrow> factorial' m n s = Some (fact n)"
  apply (induct n arbitrary: m)
   apply (subst factorial'.simps, subst fact.simps, simp add: ocondition_def obind_def)
  apply (subst factorial'.simps, subst fact.simps, simp add: ocondition_def obind_def)
  apply (clarsimp split: option.splits)
  apply (intro conjI impI)
    apply unat_arith
   apply (metis (hide_lams, no_types) Nat.add_0_right Nat.le_iff_add Suc_eq_plus1_left Suc_pred factorial.factorial'_terminates_old less_nat_zero_code nat_add_left_cancel_less nat_less_le unatSuc)
  apply (unat_arith, force)
  done

(* Termination & correctness of call_factorial *)
thm call_factorial'_def

lemma "\<lbrace> \<top> \<rbrace> call_factorial' \<lbrace> \<lambda>r s. r = fact 42 \<rbrace>!"
  unfolding call_factorial'_def
  apply wp
   using factorial'_correct_old
   apply force
  apply (force simp: option_monad_mono_eq (* factorial'_mono *))
  done

end

end
