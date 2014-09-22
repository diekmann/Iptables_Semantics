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
 * Random lemmas relating to the SIMPL language.
 *)

theory SimplBucket
imports "../c-parser/CTranslation"
begin

lemma Normal_resultE:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Normal t'; \<And>t. \<lbrakk> \<Gamma> \<turnstile> \<langle>c, Normal t\<rangle> \<Rightarrow> Normal t'; s = Normal t\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis noAbrupt_startD noFault_startD noStuck_startD xstate.exhaust)

(* The final state of a While loop will not have the condition. *)
lemma exec_While_final_cond':
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>b, s\<rangle> \<Rightarrow> s'; b = While C B; s = Normal v; s' = Normal x \<rbrakk> \<Longrightarrow> x \<notin> C"
  apply (induct arbitrary: v x rule: exec.induct)
  apply simp_all
  apply (atomize, clarsimp)
  apply (erule exec_elim_cases, auto)
  done

lemma exec_While_final_cond:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>While C B, s\<rangle> \<Rightarrow> Normal s'\<rbrakk> \<Longrightarrow> s' \<notin> C"
  apply (erule Normal_resultE)
  apply (erule exec_While_final_cond', auto)
  done

(*
 * If an invariant is held over a while loop, it will still hold when
 * the loop is complete.
 *)
lemma exec_While_final_inv':
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>b, s\<rangle> \<Rightarrow> s'; b = While C B; s = Normal v; s' = Normal x; I v; \<And>s s'. \<lbrakk> I s; \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> Normal s' \<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> I x"
  apply atomize
  apply (induct arbitrary: v x rule: exec.induct)
  (* We avoid using the simplifier here, because of looping. *)
  apply (clarify | (atomize, erule Normal_resultE, metis))+
  done

lemma exec_While_final_inv:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>While C B, Normal s\<rangle> \<Rightarrow> Normal s'; I s; \<And>s s'. \<lbrakk> I s; \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> Normal s' \<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> I s'"
  apply (erule exec_While_final_inv', auto)
  done

(* Determine if the given SIMPL fragment may throw an exception. *)
primrec
  exceptions_thrown :: "('a, 'p, 'e) com \<Rightarrow> bool"
where
    "exceptions_thrown Skip = False"
  | "exceptions_thrown (Seq a b) = (exceptions_thrown a \<or> exceptions_thrown b)"
  | "exceptions_thrown (Basic a) = False"
  | "exceptions_thrown (Spec a) = False"
  | "exceptions_thrown (Cond a b c) = (exceptions_thrown b \<or> exceptions_thrown c)"
  | "exceptions_thrown (Catch a b) = (exceptions_thrown a \<and> exceptions_thrown b)"
  | "exceptions_thrown (While a b) = exceptions_thrown b"
  | "exceptions_thrown Throw = True"
  | "exceptions_thrown (Call p) = True"
  | "exceptions_thrown (Guard f g a) = exceptions_thrown a"
  | "exceptions_thrown (DynCom a) = (\<exists>s. exceptions_thrown (a s))"

(* May the given stack of exception handlers throw an exception? *)
primrec
  exceptions_unresolved :: "('a, 'p, 'e) com list \<Rightarrow> bool"
where
    "exceptions_unresolved [] = True"
  | "exceptions_unresolved (x#xs) = (exceptions_thrown x \<and> exceptions_unresolved xs)"

(* If code can't throw an exception, it won't result in abrupt termination. *)
lemma exceptions_thrown_not_abrupt:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>p, s\<rangle> \<Rightarrow> s'; \<not> exceptions_thrown p; \<not> isAbr s \<rbrakk> \<Longrightarrow> \<not> isAbr s'"
  apply (induct rule: exec.induct, auto)
  done

end
