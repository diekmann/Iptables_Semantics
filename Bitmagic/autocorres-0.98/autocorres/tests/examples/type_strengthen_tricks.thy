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
 * Configuring type strengthen rules.
 * Based on type_strengthen.thy.
 *)
theory type_strengthen_tricks imports
  "../../AutoCorres"
begin

install_C_file "type_strengthen.c"

(* We can configure the type strengthen rules individually.
   For example, suppose that we do not want to lift loops to the option monad: *)
declare gets_theE_L2_while [ts_rule option del]

(* We can also specify which monads are used for type strengthening.
   Here, we exclude the read-only monad completely, and specify
   rules for some individual functions. *)
autocorres [
  ts_rules = pure option nondet,
  ts_force option = pure_f,
  statistics
  ] "type_strengthen.c"

context type_strengthen begin
(* pure_f (and indirectly, pure_f2) are now lifted to the option monad. *)
thm pure_f'_def pure_f2'_def
thm pure_g'_def pure_h'_def
    pure_i'_def pure_j'_def pure_k'_def pure_div_roundup'_def
(* gets_f and gets_g are now lifted to the option monad. *)
thm gets_f'_def gets_g'_def
thm opt_f'_def opt_g'_def opt_h'.simps opt_i'_def
    opt_j'_def opt_a'.simps
(* opt_l is now lifted to the state monad. *)
thm opt_l'_def
thm st_f'_def st_g'_def st_h'_def st_i'.simps (* hax'_def *)
thm exc_f'_def
end

end