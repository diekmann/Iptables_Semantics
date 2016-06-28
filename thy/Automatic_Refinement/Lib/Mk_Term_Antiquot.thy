section {* Antiquotation to Build Terms *}
theory Mk_Term_Antiquot
imports Refine_Util
begin

ML {*
(*
  Antiquotation to generate a term from a template.

  This antiquotation takes a term with schematic variables, 
  interprets the schematic variables as names of term-valued ML-variables and generates
  code to create the ML-level representation of the term with the schematics replaced
  by the ML-variables.  

  All type variables in the term must be inferable from the types of the schematics.

  Limitations:
    * The type-inference is not complete, i.e., it may fail to detect some type-errors,
      resulting in untypable terms to be created.

  TODO:
    * We could also provide explicit type variables

  Examples: See below
*)

local

  fun 
    add_nv_tvars (Const (_,T)) l = Term.add_tvarsT T l
  | add_nv_tvars (Free (_,T)) l =  Term.add_tvarsT T l
  | add_nv_tvars (Abs (_,T,t)) l = add_nv_tvars t (Term.add_tvarsT T l)
  | add_nv_tvars (t1$t2) l = add_nv_tvars t1 (add_nv_tvars t2 l)
  | add_nv_tvars _ l = l

  fun prepare env t ctxt = let
    val tvars = add_nv_tvars t []
    val vars = Term.add_vars t []
    val vtvars = fold (Term.add_tvarsT o #2) vars []
  
    fun is_expl_tvar (n,i) = i=0 andalso String.isPrefix "'v_" n
  
    val expl_tvars = Term.add_tvars t []
      |> filter (is_expl_tvar o #1)
  
    val spec_tvars = union op = vtvars expl_tvars
  
    val _ = subset op = (tvars, spec_tvars)
      orelse let
        val loose = subtract op = spec_tvars tvars 
          |> map (TVar #> Syntax.pretty_typ ctxt)
          |> Pretty.commas |> Pretty.block

        val pretty_t = Syntax.pretty_term ctxt t
  
        val msg = Pretty.block [
            Pretty.str "mk_term: Loose type variables in",
            Pretty.brk 1,pretty_t,Pretty.str ":",Pretty.brk 1,loose
          ] |> Pretty.string_of
        
      in error msg end

    val _ = fold 
      (fn v as ((_,i),_) => fn () => if i<>0 then 
          Pretty.block [
            Pretty.str "mk_term: Variable indices must be zero:", Pretty.brk 1,
            Syntax.pretty_term ctxt (Var v)
          ] |> Pretty.string_of |> error
        else ()
      ) 
      vars ()
  
    (* ARGH!!! "subtract eq a b" computes "b - a" *)
    val unused_tvars = subtract (op =) tvars vtvars 
      |> map #1
  
    (*
    val _ = tracing ("tvars: " ^ @{make_string} tvars)
    val _ = tracing ("vtvars: " ^ @{make_string} vtvars)
    val _ = tracing ("unused_tvars: " ^ @{make_string} unused_tvars)
    *)
  
    fun 
      lin_type (TFree f) Ts = (TFree f, Ts)
    | lin_type (TVar (iname,S)) Ts = 
        if is_expl_tvar iname orelse member op = Ts iname then (TVar (("_",0),S), Ts)
        else (TVar (iname,S), iname::Ts)
    | lin_type (Type (name,args)) Ts = let
        val (args,Ts) = map_fold lin_type args Ts
      in
        (Type (name,args),Ts)
      end;

    val (vars,_) = map_fold 
      ( fn (iname,T) => fn Ts => 
          let val (T,Ts) = lin_type T Ts in ((iname,T),Ts) end
      ) 
      vars unused_tvars

    fun name_of_T (name,idx) = 
      if is_expl_tvar (name,idx) then unprefix "'v_" name
      else "T_" ^ name ^ "_" ^ string_of_int idx

    local 
      fun wrv (TVar (("_",_),_)) = "_"
        | wrv (TVar (iname,_)) = name_of_T iname
        | wrv (T as TFree _) = ML_Syntax.print_typ T
        | wrv (Type arg) =
            "Type " ^ ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_list wrv) arg

      fun is_special (TVar _) = false | is_special _ = true
  
      fun mk_error_msg name T = 
        Pretty.block [
          Pretty.str ("mk_term type error: Argument for ?" ^ name ^ " does not match type"),
          Pretty.brk 1, Syntax.pretty_typ ctxt T
        ]
      |> Pretty.unformatted_string_of |> ML_Syntax.print_string
  
      fun pr_fastype name = case env of
        SOME env => "fastype_of1 (" ^ env ^ ", " ^ name ^ ")"
      | _ => "fastype_of " ^ name
  
      fun matcher ((name,_),T) rest = 
        "case " ^ pr_fastype name ^ " of " ^ wrv T ^ " => (" ^ rest ^ ")"
        ^ ( if is_special T then "| _ => raise TERM ("^mk_error_msg name T^",["^name^"])" 
            else "")

    in
      fun matchers [] rest = rest
        | matchers (v::vs) rest = matcher v (matchers vs rest)

    end

    local
      fun print_typ (Type arg) =
            "Type " ^ ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_list print_typ) arg
        | print_typ (TFree arg) =
            "TFree " ^ ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_sort arg
        | print_typ (TVar (iname, _)) = name_of_T iname;

      fun print_term (Const arg) =
            "Const " ^ ML_Syntax.print_pair ML_Syntax.print_string print_typ arg
        | print_term (Free arg) =
            "Free " ^ ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_typ arg
        | print_term (Var ((name, _), _)) = name
        | print_term (Bound i) = "Bound " ^ ML_Syntax.print_int i
        | print_term (Abs (s, T, t)) = 
            if String.isPrefix "v_" s then
              "Abs (" ^ unprefix "v_" s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
            else
              "Abs (" ^ ML_Syntax.print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
        | print_term (t1 $ t2) =
            ML_Syntax.atomic (print_term t1) ^ " $ " ^ ML_Syntax.atomic (print_term t2);
    in
      val et = print_term t
      val e = "(" ^ matchers vars et ^ ")"
    end
  in
    e
  end


  val read = Scan.lift (Scan.option (Args.name --| Args.colon)) -- 
    (Args.context -- Scan.lift (Parse.position Args.name_inner_syntax))

  fun process (env,(ctxt,(raw_t,pos))) = let
    val t = Proof_Context.read_term_pattern ctxt raw_t
  in
    prepare env t ctxt
  end handle ERROR msg => error (msg ^ Position.here pos)

in
  val mk_term_antiquot = read >> process
end
*}

setup {* ML_Antiquotation.inline @{binding mk_term} mk_term_antiquot *}


subsection "Examples"

ML_val {*
  (* The mk_term antiquotation can replace the omnipresent mk_xxx functions, and 
    easily works with complex patterns *)
  fun mk_2elem_list a b = @{mk_term "[?a,?b]"}
  fun mk_compr s P = @{mk_term "{ x\<in>?s. ?P x}"}

  val test1 = mk_2elem_list @{term "1::nat"} @{term "2::nat"} |> Thm.cterm_of @{context}
  val test2 = mk_compr @{term "{1,2,3::nat}"} @{term "op < (2::nat)"} |> Thm.cterm_of @{context}

  val test3 = let 
    val x = Bound 0 
    val env = [@{typ nat}]
  in 
    @{mk_term env: "?x+?x"}
  end

  (*
  val test4 = let 
    val x = Bound 0 
    val T = @{typ nat}
  in 
    ctd here: Handle bounds below lambdas!
    @{mk_term "\<lambda>x::?'v_T. ?x"}
  end
  *)
*}

end
