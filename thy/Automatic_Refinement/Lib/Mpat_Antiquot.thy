section {* Matching-Pattern Antiquotation *}
theory Mpat_Antiquot
imports Main Refine_Util
begin

typedecl term_struct
typedecl typ_struct
typedecl sort

definition mpaq_AS_PAT :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "AS\<^sub>p" 900)
  where "a AS\<^sub>p s \<equiv> a"

definition mpaq_STRUCT :: "term_struct \<Rightarrow> 'a" where "mpaq_STRUCT _ = undefined"

abbreviation mpaq_AS_STRUCT :: "'a \<Rightarrow> term_struct \<Rightarrow> 'a" (infixl "AS\<^sub>s" 900)
  where "a AS\<^sub>s s \<equiv> a AS\<^sub>p mpaq_STRUCT s"

consts
  mpaq_Const :: "string \<Rightarrow> typ_struct \<Rightarrow> term_struct"
  mpaq_Free :: "string \<Rightarrow> typ_struct \<Rightarrow> term_struct"
  mpaq_Var :: "string*nat \<Rightarrow> typ_struct \<Rightarrow> term_struct"
  mpaq_Bound :: "nat \<Rightarrow> term_struct"
  mpaq_Abs :: "string \<Rightarrow> typ_struct \<Rightarrow> term_struct \<Rightarrow> term_struct"
  mpaq_App :: "term_struct \<Rightarrow> term_struct \<Rightarrow> term_struct" (infixl "$$" 900)

consts
  mpaq_TFree :: "string \<Rightarrow> sort \<Rightarrow> typ_struct"
  mpaq_TVar :: "string*nat \<Rightarrow> sort \<Rightarrow> typ_struct"
  mpaq_Type :: "string \<Rightarrow> typ_struct list \<Rightarrow> typ_struct"

ML {*
  (*
    Antiquotation to generate a term-pattern in ML. 
    Features:
      * Schematic term variables are translated to ML-variables of same name.
      * Non-dummy variables in lambda-abstractions are bound to variables of 
        same name, and type of \<lambda>x. t is bound to x_T
      * In (typs) mode, schematic type variables are translated if they start
        with 'v_, where the prefix is removed. Otherwise, types are completely
        ignored and translated to ML dummy pattern.
      * Dummy variables are translated to ML dummy patterns
      * Supports AS to define alternative pattern,
        and STRUCT to reflect term structure
  
    Limitations:
      * Non-linear patterns are not allowed, due to SML limitation.
        For term variables, it will result in an error. Type variables, 
        however, are silently linearized and only the first occurrence is bound.
      * Indexes <>0 on term variables are not allowed. 
        On type variables, such indexes are silently ignored.
      * Sorts are completely ignored
      * Due to the type-inference on patterns, only innermost types can be 
        bound to names.
      * Patterns are not localized. Currently, we issue an error if pattern
        contains free variables.

    TODO:
      * We could also bind the type of a term-var, where the name for the 
        type ML-var is encoded into the term-var name

    Examples: See below

  *)

  local
    fun replace_dummy' (Const (@{const_name Pure.dummy_pattern}, T)) i =
          (Var (("_dummy_", i), T), i + 1)
      | replace_dummy' (Abs (x, T, t)) i =
          let val (t', i') = replace_dummy' t i
          in (Abs (x, T, t'), i') end
      | replace_dummy' (t $ u) i =
          let
            val (t', i') = replace_dummy' t i;
            val (u', i'') = replace_dummy' u i';
          in (t' $ u', i'') end
      | replace_dummy' a i = (a, i);

    fun prepare_dummies' ts = #1 (fold_map replace_dummy' ts 1);

    fun tcheck (Type (name,Ts)) tnames = 
        let
          val (Ts,tnames) = map_fold tcheck Ts tnames
        in 
          (Type (name,Ts),tnames)
        end
      | tcheck (TFree (name,_)) _ = 
          error ("Pattern contains free type variable: " ^ name)
      | tcheck (TVar ((name,idx),S)) tnames = 
          if String.isPrefix "'v_" name andalso not (member op = tnames name) 
          then (TVar ((unprefix "'v_" name,idx),S),name::tnames)
          else (TVar (("_",0),S),tnames)

    fun vcheck (Const (n,T)) (vnames,tnames) = 
        let 
          val (T,tnames) = tcheck T tnames
        in (Const (n,T),(vnames,tnames)) end
      | vcheck (Free (n,_)) _ = 
          error ("Pattern contains free variable: " ^ n)
      | vcheck (Var (("_dummy_",_),T)) (vnames,tnames) = 
        let
          val (T,tnames) = tcheck T tnames
        in (Var (("_",0),T),(vnames,tnames)) end
      | vcheck (Var ((name,idx),T)) (vnames,tnames) = 
        let
          val (T,tnames) = tcheck T tnames
          val _ = idx <> 0 andalso error ("Variable index greater zero: "
            ^ Term.string_of_vname (name,idx)) 
          val _ = member op = vnames name andalso error ("Non-linear pattern: "
            ^ Term.string_of_vname (name,idx))
        in (Var ((name,0),T),(name::vnames,tnames)) end
      | vcheck (Bound i) p = (Bound i,p)
      | vcheck (Abs ("uu_",T,t)) (vnames,tnames) = let
          val (T,tnames) = tcheck T tnames
          val (t,(vnames,tnames)) = vcheck t (vnames,tnames)
        in (Abs ("_",T,t),(vnames,tnames)) end
      | vcheck (Abs (x,T,t)) (vnames,tnames) = let
          val (T,tnames) = tcheck T tnames
          val (t,(vnames,tnames)) = vcheck t (vnames,tnames)
        in (Abs (x,T,t),(vnames,tnames)) end
      | vcheck (t1$t2) p = let
          val (t1,p) = vcheck t1 p
          val (t2,p) = vcheck t2 p
        in (t1$t2,p) end

    val read = Scan.lift (Args.mode "typs" )
      -- (Args.context -- Scan.lift (Parse.position Args.name_inner_syntax))
        

    fun write (with_types, t) = let
      fun twr_aux (Type (name,Ts)) 
            = "Type (" ^ ML_Syntax.print_string name ^ ", " ^ ML_Syntax.print_list twr_aux Ts ^ ")"
        | twr_aux (TFree (name,_)) = "TFree (" ^ ML_Syntax.print_string name ^ ", _)"
        | twr_aux (TVar ((name,_),_)) = name
  
      val twr = if with_types then twr_aux else K "_"

      fun s_string (Var ((name,_),_)) = name
        | s_string t = case try HOLogic.dest_string t of
            SOME s => ML_Syntax.print_string s
          | NONE => raise TERM ("Expected var or string literal",[t])

      fun s_index (Var ((name,_),_)) = name
        | s_index t = case try HOLogic.dest_nat t of
            SOME n => ML_Syntax.print_int n
          | NONE => raise TERM ("Expected var or nat literal",[t])

      fun s_indexname (Var ((name,_),_)) = name
        | s_indexname (Const (@{const_name Pair},_)$n$i) =
            "(" ^ s_string n ^ ", " ^ s_index i ^ ")"
        | s_indexname t = raise TERM ("Expected var or indexname-pair",[t])

      fun s_typ (Var ((name,_),_)) = name
        | s_typ (Const(@{const_name "mpaq_TFree"},_)$name$typ) 
            = "TFree (" ^ s_string name ^ "," ^ s_typ typ ^ ")"
        | s_typ (Const(@{const_name "mpaq_TVar"},_)$name$typ)
            = "TVar (" ^ s_indexname name ^ "," ^ s_typ typ ^ ")"
        | s_typ (Const(@{const_name "mpaq_Type"},_)$name$args)
            = "Type (" ^ s_string name ^ "," ^ s_args args ^ ")"
        | s_typ t = raise TERM ("Expected var or type structure",[t])
      and s_args (Var ((name,_),_)) = name
        | s_args t = ( case try HOLogic.dest_list t of
            SOME l => ML_Syntax.print_list s_typ l
          | NONE => raise TERM ("Expected variable or type argument list",[t])
          )

      fun swr (Const(@{const_name "mpaq_Const"},_)$name$typ) 
            = "Const (" ^ s_string name ^ ", " ^ s_typ typ ^ ")"
        | swr (Const(@{const_name "mpaq_Free"},_)$name$typ)
            = "Free (" ^ s_string name ^ ", " ^ s_typ typ ^ ")"
        | swr (Const(@{const_name "mpaq_Var"},_)$name$typ)
            = "Var (" ^ s_indexname name ^ ", " ^ s_typ typ ^ ")"
        | swr (Const(@{const_name "mpaq_Bound"},_)$idx)
            = "Bound " ^ s_index idx
        | swr (Const(@{const_name "mpaq_Abs"},_)$name$T$t)
            = "Abs (" ^ s_string name ^ ", " ^ s_typ T ^ ", " ^ swr t ^ ")"
        | swr (Const(@{const_name "mpaq_App"},_)$t1$t2)
            = "(" ^ swr t1 ^ ") $ (" ^ swr t2 ^ ")"
        | swr t = raise TERM ("Expected var or term structure",[t])

      fun vwr (Const (name,T)) 
            = "Const (" ^ ML_Syntax.print_string name ^ ", " ^ twr T ^ ")"
        | vwr (Var ((name,_),_)) = name
        | vwr (Free (name,T)) = "Free (" ^ name ^ ", " ^ twr T ^ ")"
        | vwr (Bound i) = "Bound " ^ ML_Syntax.print_int i
        | vwr (Abs ("_",T,t)) = "Abs (_," ^ twr T ^ "," ^ vwr t ^ ")"
        | vwr (Abs (x,T,t)) = "Abs (" ^ x ^ "," 
                ^ x ^ "_T as " ^ twr T ^ "," 
                ^ vwr t ^ ")"
        | vwr (Const(@{const_name mpaq_STRUCT},_)$t) = (
            swr t
          )
        | vwr (trm as Const(@{const_name "mpaq_AS_PAT"},_)$t$s) = ( 
            case t of
              (Var ((name,_),_)) => name ^ " as (" ^ vwr s ^ ")"
            | _ => raise TERM ("_AS_ must have identifier on LHS",[trm])
          )
        | vwr (t1$t2) = "(" ^ vwr t1 ^ ") $ (" ^ vwr t2 ^ ")"

      val (t,_) = vcheck t ([],[])
      val s = vwr t
    in
      "(" ^ s ^ ")"
    end

    fun process (with_types,(ctxt,(raw_t,pos))) = (let
      val ctxt' = Context.proof_map (
        Syntax_Phases.term_check 90 "Prepare dummies" (K prepare_dummies')
      ) ctxt
      val t = Proof_Context.read_term_pattern ctxt' raw_t
      val res = write (with_types,t)
    in
      (*tracing res;*)
      res
    end
    handle ERROR msg => error (msg ^ Position.here pos)
    )


  in
    val mpat_antiquot = read >> process
  end
*}

setup {*
  ML_Antiquotation.inline @{binding "mpat"} mpat_antiquot
*}

subsection {* Examples *}

ML_val {*
  fun dest_pair_singleton @{mpat "{(?a,_)}"} = (a)
    | dest_pair_singleton t = raise TERM ("dest_pair_singleton",[t])

  fun dest_nat_pair_singleton @{mpat (typs) "{(?a::nat,?b::nat)}"} = (a,b)
    | dest_nat_pair_singleton t = raise TERM ("dest_nat_pair_singleton",[t])

  fun dest_pair_singleton_T @{mpat (typs) "{(?a::_ \<Rightarrow> ?'v_Ta,?b::?'v_Tb)}"} = 
    ((a,Ta),(b,Tb))
    | dest_pair_singleton_T t = raise TERM ("dest_pair_singleton_T",[t])

  fun dest_pair_lambda @{mpat "{(\<lambda>a _ _. ?Ta, \<lambda>b. ?Tb)}"} = (a,a_T,b,b_T,Ta,Tb)
    | dest_pair_lambda t = raise TERM ("dest_pair_lambda",[t])


  fun foo @{mpat "[?a,?b AS\<^sub>s mpaq_Bound ?i,?c AS\<^sub>p [?n]]"} = 
    (a,b,i,c,n)
  | foo t = raise TERM ("foo",[t])


*}

hide_type (open) term_struct typ_struct sort


end
