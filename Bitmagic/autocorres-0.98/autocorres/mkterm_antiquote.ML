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
 * Term generation.
 *
 * Construct a term-generator at compile time.
 *
 *    @{mk_term "foo"} ()
 *      ==> @{term "foo"}
 *
 *    @{mk_term "?f a b c" (f)}
 *      ==> (fn t1 => t1 $ @{term a} $ @{term b} $ @{term c}
 *
 *    @{mk_term "a::(?'a::plus) + b" ('a)}
 *      ==> (fn t1 => Const (@{const_name plus}, t1 --> t1 --> t1) $ Free ("a", t1) $ Free ("b", t1))
 *)
structure MkTermAntiquote =
struct

local
  open ML_Syntax

  (*
   * Find the name and type of all schematic variables in the given term.
   *
   *   @{term "?x ?y"} ==> [("x", 'a => 'b), ("y", 'b)]
   *)
  fun get_schematic_types (a $ b) = get_schematic_types a @ get_schematic_types b
    | get_schematic_types (t as (Abs _)) = get_schematic_types (snd (Term.strip_abs_eta (~1) t))
    | get_schematic_types (Var ((name, _), T)) = [(name, T)]
    | get_schematic_types _ = []

  (*
   * Generate ML code to perform variable capture of the given type.
   *
   * In particular, all type variables will be captured into ML variables. The
   * returned dictionary indicates the mapping from type variables to ML variable
   * names.
   *)
  fun capture_type prefix (Type (_, Ts)) dict =
      let
        val (strings, new_dict) = fold_map (capture_type prefix) Ts dict
      in
        if length (Symtab.dest dict) = length (Symtab.dest new_dict) then
          ("_", dict)
        else
          ("Type (_,  " ^ (ML_Syntax.print_list I strings) ^ ")", new_dict)
      end
    | capture_type prefix (T as (TVar ((var_name, _), _))) dict =
      let
        val name = prefix ^ "_" ^ string_of_int (length (Symtab.dest dict))
      in
        case Symtab.lookup dict var_name of
          SOME _ => ("_", dict)
        | NONE => (name, Symtab.update_new (var_name, (name, T)) dict)
      end
    | capture_type _ (TFree _) dict = ("_", dict)

    (* Parse a list of the form "(x, y, z)". "inner" parses each of the indivdual items. *)
    fun comma_list inner =
      (inner >> (fn a => [a])) ||
          (Args.parens (inner -- (Scan.repeat (Args.$$$ "," -- inner >> snd)) >> (fn (a, b) => a :: b)))

  (* Write ML code for generating the given term, replacing schematic variables
   * with the ML code in the "replacements" dictionary. *)
  fun write_term_constructor replacements term =
  let
    fun print_typ (Type arg) = "Type " ^ print_pair print_string (print_list print_typ) arg
      | print_typ (TFree arg) = "TFree " ^ print_pair print_string print_sort arg
      | print_typ (TVar (arg as ((name, _), _))) =
          (case Symtab.lookup replacements name of
             NONE => "TVar " ^ print_pair print_indexname print_sort arg
           | SOME ml => atomic ml)

    fun print_term (Const arg) = "Const " ^ print_pair print_string print_typ arg
      | print_term (Free arg) = "Free " ^ print_pair print_string print_typ arg
      | print_term (Var (arg as ((name, _), _))) =
          (case Symtab.lookup replacements name of
             NONE => "Var " ^ print_pair print_indexname print_typ arg
           | SOME ml => atomic ml)
      | print_term (Bound i) = "Bound " ^ print_int i
      | print_term (Abs (s, T, t)) =
          "Abs (" ^ print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
      | print_term (t1 $ t2) = atomic (print_term t1) ^ " $ " ^ atomic (print_term t2);
  in
    print_term term
  end

  (* Print ML code for rendering a tuple. *)
  val print_tuple = enclose "(" ")" o commas

  (*
   * Generate ML code for a lambda function that replaces variables and types
   * in a term with parameters.
   *
   *   print_lambda ["a", "'b"] "xxx"
   *     ==> ("(fn (t1, t2) => (xxx))", {"t1 => a", "t2 => 'b"})
   *)
  fun print_lambda vars =
  let
    val temps = 1 upto (length vars)
      |> map (fn x => "t" ^ (string_of_int x))
    val lambda_term = (fn x => atomic ("fn " ^ print_tuple temps ^ " => " ^ (atomic x)))
    val dict = Symtab.make (vars ~~ temps)
  in
    (lambda_term,  dict)
  end

  (* Generate ML code for constructing the given pattern with the given
   * template variables. *)
  fun gen_constructor ((ctxt, pattern), params : string list ) =
  let
    (* Parse user term. *)
    val term = Proof_Context.read_term_pattern ctxt pattern

    (*
     * Generate the outer shell of our final result:
     *
     *    (fn (t1, t2, t3) => ...)
     *)
    val (outer_fn, var_dict) = print_lambda params

    (*
     * For each parameter passed in by the user, generate ML code
     * to extract relevant parts of its type.
     *
     * For example, if the user wants to replace "?X" (having type "?'a =>
     * ?'b"), then when the user finally fills us in with a concrete term, we
     * want to substitute "?'a" and "?'b" with their concrete values.
     *)
    val schematic_types =
    let
      val typ_table =
        get_schematic_types term
        |> distinct (op =)
        |> Symtab.make
    in
      (params ~~ map (Symtab.lookup typ_table) params)
      |> filter (fn (_, b) => b <> NONE)
      |> map (fn (a, b) => (a, the b))
    end
    val (type_patterns, typ_dict) =
        fold_map (fn (v, T) => capture_type ("T__" ^ v) T) schematic_types Symtab.empty

    (* Merge the dictionary generated above (designed to capture types from
     * the input term) with the user-provided definitions (which may also
     * attempt to define types). *)
    val replacement_dict = Symtab.join
        (fn k => fn _ => error ("Key " ^ k ^ " used twice."))
        (Symtab.map (K fst) typ_dict, var_dict)

    (* Generate code to determine types of variables. *)
    val typ_match =
      outer_fn (
        "(let "
        ^ (cat_lines (map (fn (pattern, param) =>
            "val " ^ pattern ^ " = fastype_of " ^ param ^ "; ")
            (type_patterns ~~ map (the o Symtab.lookup var_dict o fst) schematic_types)))
        ^ " in "
          ^ (write_term_constructor replacement_dict term)
        ^ " end)"
      )
  in
    typ_match
  end
in
  val _ = Context.>> (Context.map_theory (
    ML_Antiquotation.inline @{binding "mk_term"}
      ((Args.context -- Scan.lift Args.name_inner_syntax -- (Scan.optional (Scan.lift ((comma_list Args.name))) []))
         >>  gen_constructor)))
end

end
