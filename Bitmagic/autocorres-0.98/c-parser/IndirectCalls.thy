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

theory IndirectCalls

imports
  "PrettyProgs"

begin

definition
  lookup_proc :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_id \<rightharpoonup> string)
    \<Rightarrow> 'proc_addr \<Rightarrow> 'proc_id"
where
  "lookup_proc symtab naming x
    = (THE pid. naming pid \<noteq> None \<and> symtab (the (naming pid)) = x)"

definition
  lookup_proc_safe :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_id \<rightharpoonup> string)
    \<Rightarrow> 'proc_addr \<Rightarrow> bool"
where
  "lookup_proc_safe symtab naming x
    = (card {pid. naming pid \<noteq> None \<and> symtab (the (naming pid)) = x} = 1)"

definition
  procs_consistent :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_nm \<rightharpoonup> string)
    \<Rightarrow> bool"
where
  "procs_consistent symtab naming
    = (finite (dom naming)
        \<and> (\<forall>x y nm nm'. naming x = Some nm \<and> naming y = Some nm'
            \<and> symtab nm = symtab nm'
                \<longrightarrow> x = y))"

lemma procs_consistent_eq:
  "\<lbrakk> naming proc = Some nm; procs_consistent symtab naming; addr = symtab nm \<rbrakk>
    \<Longrightarrow> lookup_proc symtab naming addr = proc"
  apply (clarsimp simp: procs_consistent_def lookup_proc_def)
  apply (rule the_equality)
   apply clarsimp
  apply clarsimp
  done

lemma procs_consistent_safe:
  "\<lbrakk> naming proc = Some nm; procs_consistent symtab naming; addr = symtab nm \<rbrakk>
    \<Longrightarrow> lookup_proc_safe symtab naming addr"
  apply (clarsimp simp: procs_consistent_def lookup_proc_safe_def)
  apply (rule trans, rule arg_cong[where f=card and y="{proc}"])
   apply auto
  done

lemma hoare_indirect_call_procs_consistent:
  "\<lbrakk> naming proc = Some nm; 
        \<Gamma> \<turnstile> P (call initf proc ret c) Q, A \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> ({s. procs_consistent symtab naming \<and> x_fn s = symtab nm} \<inter> P)
            (dynCall initf (\<lambda>s. lookup_proc symtab naming (x_fn s))
                    ret c) Q, A"
  apply (rule hoare_complete, drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply (erule exec_dynCall_Normal_elim)
  apply (simp add: procs_consistent_eq)
  apply blast
  done

end

