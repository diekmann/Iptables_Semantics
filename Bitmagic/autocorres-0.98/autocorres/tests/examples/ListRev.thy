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

theory ListRev
imports "../../AutoCorres"
begin

install_C_file "list_rev.c"

autocorres [heap_abs_syntax] "list_rev.c"

primrec
  list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"
where
  "list s p [] = (p = NULL)"
| "list s p (x#xs) = (
       p = x \<and> p \<noteq> NULL \<and> is_valid_node_C s p \<and> list s (s[p]\<rightarrow>next) xs)"

lemma list_empty [simp]:
  "list s NULL xs = (xs = [])"
  by (induct xs) auto

lemma list_in [simp]:
  "\<lbrakk> list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (induct xs) auto

lemma list_non_NULL:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    list s p xs = (\<exists>ys. xs = p # ys \<and> is_valid_node_C s p \<and> list s (s[p]\<rightarrow>next) ys)"
  by (cases xs) auto

lemma list_unique:
  "list s p xs \<Longrightarrow> list s p ys \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: p ys) (auto simp add: list_non_NULL)

lemma list_append_Ex:
  "list s p (xs @ ys) \<Longrightarrow> (\<exists>q. list s q ys)"
  by (induct xs arbitrary: p) auto

lemma list_distinct [simp]:
  "list s p xs \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: p)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma list_heap_update_ignore [simp]:
  "q \<notin> set xs \<Longrightarrow> list (s[q\<rightarrow>next := v]) p xs = list s p xs"
  apply (induct xs arbitrary: p)
   apply clarsimp
  apply (clarsimp simp: fun_upd_def)
  done

definition
  the_list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list"
where
  "the_list s p = (THE xs. list s p xs)"

lemma the_list_val [simp]: "list s p xs \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

lemma [simp]:
   "\<lbrakk> q \<notin> set xs; list s p xs \<rbrakk> \<Longrightarrow> the_list s[q\<rightarrow>next := v] p = the_list s p"
  apply (subgoal_tac "list s[q\<rightarrow>next := v] p xs")
   apply (metis the_list_val)
  apply clarsimp
  done

definition "reverse_inv xs list' rev' s =
                 (\<exists>ys zs. list s list' ys
                    \<and> list s rev' zs
                    \<and> rev xs = rev ys @ zs
                    \<and> distinct (rev xs))"

lemma (in list_rev) reverse_correct:
  "\<lbrace> \<lambda>s. list s p xs \<rbrace>
     reverse' p
   \<lbrace> \<lambda>rv s. list s rv (rev xs) \<rbrace>!"
  apply (clarsimp simp: reverse'_def)
  apply (subst whileLoop_add_inv [where
        I="\<lambda>(list', rev') s. reverse_inv xs list' rev' s"
        and M="\<lambda>((list', rev'), s). length (the_list s list')",
        unfolded reverse_inv_def])
  apply wp
    apply (clarsimp simp del: distinct_rev)
    apply (case_tac ys, fastforce)
    apply (clarsimp simp del: distinct_rev)
    apply (rule_tac x=lista in exI)
    apply (simp add: fun_upd_def)
   apply (clarsimp simp del: distinct_rev)
  apply simp
  done

end
