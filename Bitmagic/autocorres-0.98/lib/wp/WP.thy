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

theory WP
imports "~~/src/HOL/Main"
begin

definition
  triple_judgement :: "('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
where
 "triple_judgement pre body property = (\<forall>s. pre s \<longrightarrow> property s body)"

definition
  postcondition :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('r \<times> 's) set)
            \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
 "postcondition P f = (\<lambda>a b. \<forall>(rv, s) \<in> f a b. P rv s)"

definition
  postconditions :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
where
 "postconditions P Q = (\<lambda>a b. P a b \<and> Q a b)"

ML_file "WP-method.ML"

setup WeakestPre.setup

method_setup wp = {* WeakestPre.apply_rules_args false *}
  "applies weakest precondition rules"

method_setup wp_once = {* WeakestPre.apply_once_args false *}
  "applies one weakest precondition rule"

method_setup wp_trace = {* WeakestPre.apply_rules_args true *}
  "applies weakest precondition rules with tracing"

method_setup wp_once_trace = {* WeakestPre.apply_once_args true *}
  "applies one weakest precondition rule with tracing"

end
