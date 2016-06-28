section {* Tagging of Terms *}
theory Autoref_Tagging
imports "../Lib/Refine_Lib" 
begin
text {*
  We provide a mechanism to tag terms, that supports relator annotations,
  and introduces tags to protect operations, function applications, and 
  abstractions from automatic beta and eta conversions.
*}


ML {*
  structure Autoref_Tag_Defs = Named_Thms (
    val name = @{binding autoref_tag_defs}
    val description = "Autoref: Definitions of internal tags"
  )
*}
setup Autoref_Tag_Defs.setup


text {* General protection tag *}
definition PROTECT where [simp, autoref_tag_defs]: "PROTECT x \<equiv> x"

text {* General annotation tag *}
typedecl annot
definition ANNOT :: "'a \<Rightarrow> annot \<Rightarrow> 'a" 
  where [simp, autoref_tag_defs]: "ANNOT x a \<equiv> x"

text {* Operation-tag, Autoref does not look beyond this *}
definition OP where [simp, autoref_tag_defs]: "OP x \<equiv> x"

text {* Protected function application *}
definition APP (infixl "$" 900) where [simp, autoref_tag_defs]: "f$a \<equiv> f a"

text {* Protected abstraction *}
abbreviation ABS :: "('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b" (binder "\<lambda>''" 10)
  where "ABS f \<equiv> PROTECT (\<lambda>x. PROTECT (f x))"


lemma ABS_beta: "(\<lambda>'x. f x)$x \<equiv> f x" by simp
lemma ABS_eta: "\<lambda>'x. (f$x) \<equiv> f" by simp

text {* This tag is used to highlight failures during operation 
  identification *}
definition "ID_FAIL x \<equiv> x"
notation (output) ID_FAIL ("FAIL *** _ ***")


text {* Relator annotation *}
consts rel_annot :: "('c\<times>'a) set \<Rightarrow> annot"
abbreviation rel_ANNOT :: "'a \<Rightarrow> ('c \<times> 'a) set \<Rightarrow> 'a" (infix ":::" 10)
  where "t:::R \<equiv> ANNOT t (rel_annot R)"

lemma rel_ANNOT_eq: "t \<equiv> t:::R" by simp

text {* Indirect annotation *}
typedecl rel_name
consts ind_annot :: "rel_name \<Rightarrow> annot"
abbreviation ind_ANNOT :: "'a \<Rightarrow> rel_name \<Rightarrow> 'a" (infix "::#" 10)
  where "t::#s \<equiv> ANNOT t (ind_annot s)"





ML {*
  signature AUTOREF_TAGGING = sig
    val term_of_tagged: term -> term
    val is_valid_tagged: term -> bool

    val mk_APP: term -> term -> term
    val mk_OP: term -> term
    val lambda': string * typ -> term -> term

    val list_APP: term * term list -> term
    val strip_app: term -> term * term list

    val untag_conv: Proof.context -> conv

    val mk_APP_conv: conv
    val mk_OP_conv: conv
    val mk_ABS_conv: Proof.context -> conv
    val mk_ANNOT_conv: cterm -> conv
    val mk_rel_ANNOT_conv: Proof.context -> cterm -> conv

    val ABS_beta_conv: Proof.context -> conv

    val rhs_conv: (Proof.context -> conv) -> Proof.context -> conv
  end


  structure Autoref_Tagging :AUTOREF_TAGGING = struct
    fun term_of_tagged (Free v) = Free v
      | term_of_tagged (Var v) = Var v
      | term_of_tagged (Bound i) = Bound i
      | term_of_tagged @{mpat "OP ?t"} = t
      | term_of_tagged @{mpat "ANNOT ?t _"} = term_of_tagged t
      | term_of_tagged @{mpat "?f$?x"} = term_of_tagged f $ term_of_tagged x
      | term_of_tagged @{mpat "PROTECT (\<lambda>x. PROTECT ?t)"} 
        = Abs (x,x_T,term_of_tagged t)
      | term_of_tagged @{mpat (typs) "PROTECT (PROTECT::?'v_T\<Rightarrow>_)"} 
        = Abs ("x",T,Bound 0)
      | term_of_tagged t = raise TERM ("term_of_tagged",[t])

    fun is_valid_tagged (Free _) = true
      | is_valid_tagged (Var _) = true
      | is_valid_tagged (Bound _) = true
      | is_valid_tagged @{mpat "OP _"} = true
      | is_valid_tagged @{mpat "ANNOT ?t _"} = is_valid_tagged t
      | is_valid_tagged @{mpat "?f$?x"} 
        = is_valid_tagged f andalso is_valid_tagged x
      | is_valid_tagged @{mpat "PROTECT (\<lambda>_. PROTECT ?t)"} = is_valid_tagged t
      | is_valid_tagged @{mpat "PROTECT PROTECT"} = true
      | is_valid_tagged _ = false

    fun mk_APP f x = let
      val fT = fastype_of f
      val xT = fastype_of x
      val rT = range_type fT
    in
      Const (@{const_name APP},fT --> xT --> rT)$f$x
    end;

    fun mk_OP x = let 
      val T = fastype_of x 
    in 
      Const(@{const_name OP},T-->T)$x
    end

    fun lambda' (name,T) t = let
      val tT = fastype_of t
      val t' = Const (@{const_name PROTECT},tT --> tT)$
        abstract_over (Free (name,T), t)
      val t' = 
        Const (@{const_name PROTECT},(T --> tT) --> T --> tT)$Abs (name,T,t')
    in
      t'
    end

    val list_APP = Library.foldl (uncurry mk_APP)

    (* f$x1$...$xn goes to (f,[x1,...,xn]*)
    fun strip_app t = let
      fun strip_app_aux @{mpat "?f$?x"} args = strip_app_aux f (x::args)
        | strip_app_aux t args = (t,args)
    in strip_app_aux t [] end
      
    fun untag_conv ctxt = Raw_Simplifier.rewrite ctxt
      true (Autoref_Tag_Defs.get ctxt)

    fun ABS_beta_conv ctxt = Raw_Simplifier.rewrite ctxt
      true @{thms ABS_beta}
  
    val mk_PROTECT_conv = Conv.rewr_conv @{thm PROTECT_def[symmetric]}
    val mk_APP_conv = Conv.rewr_conv @{thm APP_def[symmetric]}
    val mk_OP_conv = Conv.rewr_conv @{thm OP_def[symmetric]}
    fun mk_ABS_conv ctxt = Conv.abs_conv (K mk_PROTECT_conv) ctxt
      then_conv mk_PROTECT_conv

    fun mk_ANNOT_conv a ct = let
      val Tt = Thm.ctyp_of_cterm ct

      val thm = Thm.instantiate' [SOME Tt] [SOME ct,SOME a] 
        @{thm ANNOT_def[symmetric]}
    in
      thm
    end

    fun mk_rel_ANNOT_conv ctxt a ct = let
      val T = Thm.typ_of_cterm a
      val (Tc,Ta) = HOLogic.dest_setT T 
        |> HOLogic.dest_prodT 
        |> apply2 (Thm.ctyp_of ctxt)
      val thm = Thm.instantiate' [SOME Ta, SOME Tc] [SOME ct,SOME a] 
        @{thm rel_ANNOT_eq}
    in
      thm
    end

    (* Convert right hand side of refinement statement *)
    fun rhs_conv conv ctxt ct = let 
      open Conv Refine_Util 
    in
      case Logic.strip_imp_concl (Thm.term_of ct) of
        @{mpat "Trueprop ((_,_)\<in>_)"} =>
          HOL_concl_conv (fn ctxt => (arg1_conv (arg_conv (conv ctxt)))) ctxt ct
      | _ => raise CTERM ("rhs_conv",[ct])
    end
  end

*}

ML_val {*
  Autoref_Tagging.mk_ANNOT_conv @{cterm "bar::annot"} @{cterm "foo::'a::type"};
*}

ML_val {*
  Autoref_Tagging.mk_rel_ANNOT_conv @{context}
    @{cterm "bar::('c\<times>'a) set"} @{cterm "foo::'a::type"}
*}

end
