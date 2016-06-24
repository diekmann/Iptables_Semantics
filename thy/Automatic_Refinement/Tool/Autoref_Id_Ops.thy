section {* Operation Identification *}
theory Autoref_Id_Ops
imports 
  "../Lib/Refine_Lib" 
  Autoref_Phases
  Autoref_Data
  Autoref_Tagging
  "../Parametricity/Parametricity"
begin

subsection {* Main Tool *}

typedecl interface

definition intfAPP 
  :: "(interface \<Rightarrow> _) \<Rightarrow> interface \<Rightarrow> _" 
  where "intfAPP f x \<equiv> f x"

syntax "_intf_APP" :: "args \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>\<^sub>i_" [0,900] 900)

translations
  "\<langle>x,xs\<rangle>\<^sub>iR" == "\<langle>xs\<rangle>\<^sub>i(CONST intfAPP R x)"
  "\<langle>x\<rangle>\<^sub>iR" == "CONST intfAPP R x"

consts
  i_fun :: "interface \<Rightarrow> interface \<Rightarrow> interface" 

abbreviation i_fun_app (infixr "\<rightarrow>\<^sub>i" 60) where "i1\<rightarrow>\<^sub>ii2 \<equiv> \<langle>i1,i2\<rangle>\<^sub>ii_fun"

consts 
  i_annot :: "interface \<Rightarrow> annot"

abbreviation i_ANNOT :: "'a \<Rightarrow> interface \<Rightarrow> 'a" (infixr ":::\<^sub>i" 10) where
  "t:::\<^sub>iI \<equiv> ANNOT t (i_annot I)"

text {* Declaration of interface-type for constant *}
definition CONST_INTF :: "'a \<Rightarrow> interface \<Rightarrow> bool" (infixr "::\<^sub>i" 10)
  where [simp]: "c::\<^sub>i I \<equiv> True"


text {*
  Predicate for operation identification. @{text "ID_OP t t' I"} means
  that term @{text "t"} has been annotated as @{text "t'"}, and its interface
  is @{text "I"}.
*}
definition ID_OP :: "'a \<Rightarrow> 'a \<Rightarrow> interface \<Rightarrow> bool" 
  where [simp]: "ID_OP t t' I \<equiv> t=t'"

text {*
  Interface inference rules. 
  Caution: Some of these must be applied with custom unification!
*}
lemma ID_abs: -- "Tag abs first"
  "\<lbrakk> \<And>x. ID_OP x x I1 \<Longrightarrow> ID_OP (f x) (f' x) I2 \<rbrakk> 
  \<Longrightarrow> ID_OP (\<lambda>'x. f x) (\<lambda>'x. f' x) (I1\<rightarrow>\<^sub>iI2)"
  by simp

lemma ID_app: -- "Tag app first"
  "\<lbrakk> INDEP I1; ID_OP x x' I1; ID_OP f f' (I1\<rightarrow>\<^sub>iI2) \<rbrakk> 
  \<Longrightarrow> ID_OP (f$x) (f'$x') I2" by simp

lemma ID_const: -- "Only if c is constant or free variable"
  "\<lbrakk> c ::\<^sub>i I \<rbrakk> \<Longrightarrow> ID_OP c (OP c :::\<^sub>i I) I"
  by simp

definition [simp]: "ID_TAG x \<equiv> x"
lemma ID_const_any: -- "Only if no typing for constant exists"
  "ID_OP c (OP (ID_TAG c) :::\<^sub>i I) I" 
  by simp

lemma ID_const_check_known: 
  "\<lbrakk> c ::\<^sub>i I' \<rbrakk> \<Longrightarrow> ID_OP c c I" by simp

lemma ID_tagged_OP: -- "Try first"
  "ID_OP (OP f :::\<^sub>i I) (OP f :::\<^sub>i I) I"
  by simp

lemma ID_is_tagged_OP: "ID_OP (OP c) t' I \<Longrightarrow> ID_OP (OP c) t' I" .

lemma ID_tagged_OP_no_annot:
  "c ::\<^sub>i I \<Longrightarrow> ID_OP (OP c) (OP c :::\<^sub>i I) I" by simp

lemmas ID_tagged = ID_tagged_OP ID_abs ID_app

lemma ID_annotated: -- "Try second"
  "ID_OP t t' I \<Longrightarrow> ID_OP (t :::\<^sub>i I) t' I"
  "ID_OP t t' I \<Longrightarrow> ID_OP (ANNOT t A) (ANNOT t' A) I"
  by simp_all


lemma ID_init:
  assumes "ID_OP a a' I"
  assumes "(c,a')\<in>R"
  shows "(c,a)\<in>R"
  using assms by auto

lemma itypeI: "(c::'t) ::\<^sub>i I" by simp

consts depth_limit_dummy :: 'a
notation (output) depth_limit_dummy ("\<dots>")

ML {*
  fun limit_depth _ (t as Const _) = t
    | limit_depth _ (t as Var _) = t
    | limit_depth _ (t as Free _) = t
    | limit_depth _ (t as Bound _) = t
    | limit_depth 0 t = Const (@{const_name depth_limit_dummy},fastype_of t)
    | limit_depth i (t as _$_) = let
        val (f,args) = strip_comb t
        val f = limit_depth (i - 1) f
        val args = map (limit_depth (i - 1)) args
      in 
        list_comb (f,args)
      end
    | limit_depth i (Abs (x,T,t)) = Abs (x,T,limit_depth (i - 1) t)

  fun depth_of (t as _$_) = let
        val (f,args) = strip_comb t
      in 
        Integer.max (depth_of f) (fold (Integer.max o depth_of) args 0) + 1
      end
    | depth_of (Abs (_,_,t)) = depth_of t + 1
    | depth_of _ = 0

  val depth_of_lhs = depth_of o Thm.term_of o Thm.lhs_of
  val depth_of_rhs = depth_of o Thm.term_of o Thm.rhs_of

  fun pretty_rewrite ctxt thm rthm = let
    val lhsd = depth_of_lhs thm
    val t = Thm.lhs_of rthm |> Thm.term_of |> limit_depth lhsd

    val rhsd = depth_of_rhs thm
    val t' = Thm.rhs_of rthm |> Thm.term_of |> limit_depth rhsd
  in
    Pretty.block [
      Syntax.pretty_term ctxt t, 
      Pretty.brk 1, Pretty.str "->", Pretty.brk 1,
      Syntax.pretty_term ctxt t'
    ]
  end


*}

ML_val {*
  depth_of @{term "f [1] [2] []"};

  limit_depth 2 @{term "[1,2,3,4,5,6,7]"}
  |> Thm.cterm_of @{context}

*}


ML {*
  fun index_rewr_thms thms = let
    fun lhs thm = case Thm.concl_of thm of
      @{mpat "?lhs == _"} => [lhs]
    | _ => []

    val net = Item_Net.init Thm.eq_thm_prop lhs
    val net = fold_rev Item_Net.update thms net
  in
    net
  end

  fun net_rewr_tac net get_pat frame_conv ctxt = IF_EXGOAL (
    fn i => fn st => let
      val g = Logic.concl_of_goal (Thm.prop_of st) i |> get_pat
      val thms = Item_Net.retrieve net g
      val cnv = map 
        (fn thm => CONVERSION (frame_conv (Conv.rewr_conv thm) ctxt)) thms
      |> APPEND_LIST'
    in
      cnv i st
    end
  )

*}

ML {*
  signature AUTOREF_ID_OPS = sig
    val id_tac: Proof.context -> tactic'

    val id_phase: Autoref_Phases.phase

    val mk_const_intf: term -> term -> term
    val mk_const_intf_thm: Proof.context -> term -> term -> thm

    val dest_const_intf: term -> term * term
    val dest_const_intf_thm: thm -> term * term

    val cfg_trace_intf_unif: bool Config.T
    val cfg_trace_failed_id: bool Config.T
    val cfg_ss_id_op: bool Config.T
    val cfg_trace_patterns: bool Config.T
    val cfg_use_id_tags: bool Config.T
    val cfg_trace_id_tags: bool Config.T

    val typ_thms_of_seq: Proof.context -> term -> thm Seq.seq
    val has_typ_thms: Proof.context -> term -> bool

    val decl_derived_typing: bool -> term -> term 
      -> Context.generic -> Context.generic

    val setup: theory -> theory
  end
  

  structure Autoref_Id_Ops :AUTOREF_ID_OPS = struct
    open Refine_Util Autoref_Tagging


    fun mk_const_intf c I = let
      val Tc = fastype_of c
      val T = Tc --> @{typ interface} --> @{typ bool}
    in 
      Const (@{const_name CONST_INTF},T)$c$I
    end

    fun mk_const_intf_thm ctxt f I = let
      val fT = fastype_of f |> Thm.ctyp_of ctxt
      val f = Thm.cterm_of ctxt f
      val I = Thm.cterm_of ctxt I
      val thm = Thm.instantiate' [SOME fT] [SOME f, SOME I] @{thm itypeI}
    in
      thm
    end

    fun dest_const_intf @{mpat "?c::\<^sub>i?I"} = (c,I)
      | dest_const_intf t = raise TERM ("dest_const_intf",[t])

    val dest_const_intf_thm = Thm.concl_of 
      #> HOLogic.dest_Trueprop 
      #> dest_const_intf

    fun LHS_COND' P = CONCL_COND'
      (fn @{mpat "Trueprop (ID_OP ?lhs _ _)"} => P lhs | _ => false)
    
    local open Conv in
      fun id_op_lhs_conv cnv ct = case Thm.term_of ct of
        @{mpat "ID_OP _ _ _"} => (fun_conv (fun_conv (arg_conv cnv))) ct
      | _ => raise CTERM ("id_op_lhs_conv",[ct])
    end

    structure intf_types = Named_Thms (
      val name = @{binding autoref_itype}
      val description = "Interface type declaration"
    )

    structure op_patterns = Named_Thms (
      val name = @{binding autoref_op_pat}
      val description = "Operation patterns"
    )

    structure op_patterns_def = Named_Thms (
      val name = @{binding autoref_op_pat_def}
      val description = "Definitive operation patterns"
    )

    val cfg_trace_intf_unif = 
      Attrib.setup_config_bool @{binding autoref_trace_intf_unif} (K false)

    val cfg_trace_failed_id = 
      Attrib.setup_config_bool @{binding autoref_trace_failed_id} (K false)

    val cfg_ss_id_op = 
      Attrib.setup_config_bool @{binding autoref_ss_id_op} (K false)

    val cfg_trace_patterns = 
      Attrib.setup_config_bool @{binding autoref_trace_pat} (K false)

    val cfg_use_id_tags = 
      Attrib.setup_config_bool @{binding autoref_use_id_tags} (K false)

    val cfg_trace_id_tags = 
      Attrib.setup_config_bool @{binding autoref_trace_id_tags} (K false)

    fun get_typ_net ctxt = let
      val thy = Proof_Context.theory_of ctxt
      val typ_net = intf_types.get ctxt
        |> Refine_Util.subsume_sort Thm.concl_of thy
        |> Tactic.build_net
    in typ_net end

    fun typ_thms_of_seq' ctxt typ_net c = let
      val idx = Term.maxidx_of_term c + 1
      val typ_thms = mk_const_intf c (Var (("I",idx),@{typ interface}))
        |> HOLogic.mk_Trueprop
        |> Thm.cterm_of ctxt
        |> Goal.init
        |> resolve_from_net_tac ctxt typ_net 1
        |> Seq.map Goal.conclude
    in typ_thms end

    fun typ_thms_of_seq ctxt = typ_thms_of_seq' ctxt (get_typ_net ctxt)

    fun has_typ_thms' thy typ_net = 
      typ_thms_of_seq' thy typ_net #> Seq.pull #> is_some
    fun has_typ_thms ctxt = has_typ_thms' ctxt (get_typ_net ctxt)
  
    fun id_tac ctxt = let
      val thy = Proof_Context.theory_of ctxt

      val typ_net = get_typ_net ctxt
      val typ_thms_seq_of = typ_thms_of_seq' ctxt typ_net
      val typ_thms_of = typ_thms_seq_of #> Seq.list_of

      fun pretty_typ_thms l = 
        l
        |> map (Thm.pretty_thm ctxt)
        |> Pretty.fbreaks |> Pretty.block


      val tr_iu = 
        if Config.get ctxt cfg_trace_intf_unif then
          fn i => fn st => ((
            case Logic.concl_of_goal (Thm.prop_of st) i of
              (t as @{mpat "Trueprop (?c::\<^sub>i_)"}) => ( case typ_thms_of c of
                [] => ()
              | tts => Pretty.block [
                  Pretty.block [
                    Pretty.str "Interface unification failed:",
                    Pretty.brk 1,
                    Syntax.pretty_term ctxt t
                  ], 
                  Pretty.fbrk,
                  Pretty.str "  ",
                  Pretty.block [
                    Pretty.str "Candidates: ", 
                    Pretty.fbrk,
                    pretty_typ_thms tts
                  ]
                ]
                |> Pretty.string_of |> tracing
              )
            | _ => ()
          ); Seq.empty)
        else K no_tac

      val id_typ = 
        resolve_from_net_tac ctxt typ_net
        ORELSE' tr_iu

      val pat_net = op_patterns.get ctxt 
        |> Refine_Util.subsume_sort (Thm.concl_of #> Logic.dest_equals #> #1) thy
        |> index_rewr_thms

      val def_pat_net = op_patterns_def.get ctxt
        |> Refine_Util.subsume_sort (Thm.concl_of #> Logic.dest_equals #> #1) thy
        |> index_rewr_thms

      val id_abs = CONVERSION (HOL_concl_conv 
        (fn ctxt => id_op_lhs_conv (mk_ABS_conv ctxt)) ctxt)
        THEN' resolve_tac ctxt @{thms ID_abs}
      val id_app = CONVERSION (HOL_concl_conv 
        (fn _ => id_op_lhs_conv (mk_APP_conv)) ctxt)
        THEN' resolve_tac ctxt @{thms ID_app}

      val id_tag_tac = let
        val trace = Config.get ctxt cfg_trace_id_tags
      in 
        if trace then IF_EXGOAL (fn i => fn st => let
            fun tr_tac _ st' = let
              val goal = Logic.get_goal (Thm.prop_of st) i
              val concl = Logic.concl_of_goal (Thm.prop_of st) i
              val _ = case concl of
                  @{mpat "Trueprop (ID_OP ?lhs _ _)"} =>
                    tracing ("ID_TAG: " ^ @{make_string} lhs) 
                | _ => tracing "ID_TAG: LHS???"

              val _ = Pretty.block [
                Pretty.str "ID_TAG: ", Pretty.brk 1,
                Syntax.pretty_term ctxt goal
              ] |> Pretty.string_of |> tracing
            in 
              Seq.single st'
            end
          in
            (resolve_tac ctxt @{thms ID_const_any} THEN' tr_tac) i st
          end) 
        else
          resolve_tac ctxt @{thms ID_const_any}

      end

      val id_const = 
        LHS_COND' (fn t => is_Const t orelse is_Free t)
        THEN' (
          (resolve_tac ctxt @{thms ID_const} THEN' id_typ) (* Try to find type *)
          ORELSE' (
            if Config.get ctxt cfg_use_id_tags then
              CAN' (resolve_tac ctxt @{thms ID_const_check_known} THEN' id_typ)
              THEN_ELSE' (
                K no_tac,
                id_tag_tac
              )
            else K no_tac
          )
        )
  
      val id_tagged = resolve_tac ctxt @{thms ID_tagged}

      val id_annotated = resolve_tac ctxt @{thms ID_annotated}

      (*
      val traced_rewr_conv = if Config.get ctxt cfg_trace_patterns then
        fn ctxt => fn thm => fn ct => let
          val rthm = Conv.rewr_conv thm ct
          val _ = Pretty.block [
            Pretty.str "Trying op-pat:", Pretty.brk 1, 
            pretty_rewrite ctxt thm rthm
          ] |> Pretty.string_of |> tracing
        in
          rthm
        end
      else
        K Conv.rewr_conv
      *)

      fun get_rewr_pat @{mpat "Trueprop (ID_OP ?lhs _ _)"} = lhs
        | get_rewr_pat t = t
      
      fun rewr_frame_conv conv = HOL_concl_conv (fn _ => id_op_lhs_conv conv)

      val def_id_pat = 
        DETERM o net_rewr_tac def_pat_net get_rewr_pat rewr_frame_conv ctxt
  
      val id_pat = 
        net_rewr_tac pat_net get_rewr_pat rewr_frame_conv ctxt
  
      val id_dflt = FIRST' [id_app,id_const,id_abs]
    
      val id_fail = if Config.get ctxt cfg_trace_failed_id then
        IF_EXGOAL (fn i => fn st => 
          let 
            val pat = Logic.concl_of_goal (Thm.prop_of st) i
                  |> get_rewr_pat
            val _ = Pretty.block [ 
                Pretty.str "Failed to identify: ",
                Syntax.pretty_term ctxt pat
              ]
            |> Pretty.string_of |> tracing
          in
            Seq.empty
          end
        ) 
      else K no_tac

      val ss = Config.get ctxt cfg_ss_id_op
      val step_tac = 
        FIRST' [
          assume_tac ctxt,
          id_tagged,
          resolve_tac ctxt @{thms ID_is_tagged_OP} THEN_ELSE' (
            resolve_tac ctxt @{thms ID_tagged_OP_no_annot} THEN' id_typ,
            FIRST' [
              Indep_Vars.indep_tac ctxt,
              id_annotated,
              def_id_pat,
              id_pat APPEND' id_dflt,
              id_fail
            ]
          )
        ] 

      fun rec_tac i st = (
        step_tac THEN_ALL_NEW_FWD (if ss then K all_tac else rec_tac)
      ) i st

    in
      rec_tac
    end

    fun id_analyze _ i j _ = (i = j)
    fun id_pretty_failure _ i j _ = 
      if i = j then
        Pretty.str "No failure"
      else 
        Pretty.str "Interface typing error. Enable tracing for more information"


    val id_phase = {
      init = I,
      tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ID_init} THEN' id_tac ctxt)),
      analyze = id_analyze,
      pretty_failure = id_pretty_failure
    }


    fun decl_derived_typing overl c I context = let
      val ctxt = Context.proof_of context

      val typ_thms = intf_types.get ctxt 
        (* TODO: Use net cached in ctxt here! *)

      val thm = mk_const_intf_thm ctxt c I

      val st = Thm.cprop_of thm |> Goal.init
      val has_t = SOLVED' (match_tac ctxt typ_thms) 1 st |> Seq.pull |> is_some
    in
      if has_t then context
      else (
        not overl andalso has_typ_thms ctxt c andalso (warning (
          Pretty.block [
            Pretty.str "Adding overloaded interface type to constant:",
            Pretty.brk 1,
            Thm.pretty_thm ctxt thm
          ] |> Pretty.string_of
        ); true);
        intf_types.add_thm thm context 
      )
    end

    val setup = I
      #> intf_types.setup
      #> op_patterns.setup
      #> op_patterns_def.setup

  end


*}

setup Autoref_Id_Ops.setup


definition IND_FACT :: "rel_name \<Rightarrow> ('c \<times> 'a) set \<Rightarrow> bool" ("#_=_" 10)
  where [simp]: "#name=R \<equiv> True"

lemma REL_INDIRECT: "#name=R" by simp


definition CNV_ANNOT :: "'a \<Rightarrow> 'a \<Rightarrow> (_\<times>'a) set \<Rightarrow> bool"
  where [simp]: "CNV_ANNOT t t' R \<equiv> t=t'"

definition REL_OF_INTF :: "interface \<Rightarrow> ('c\<times>'a) set \<Rightarrow> bool" 
  where [simp]: "REL_OF_INTF I R \<equiv> True"

definition 
  [simp]: "REL_OF_INTF_P I R \<equiv> True" -- "Version to resolve relator arguments"

lemma CNV_ANNOT:
  "\<And>f f' a a'. \<lbrakk> CNV_ANNOT a a' Ra; CNV_ANNOT f f' (Ra\<rightarrow>Rr) \<rbrakk> 
    \<Longrightarrow> CNV_ANNOT (f$a) (f'$a') (Rr)"
  "\<And>f f'. \<lbrakk> \<And>x. CNV_ANNOT x x Ra \<Longrightarrow> CNV_ANNOT (f x) (f' x) Rr \<rbrakk> 
    \<Longrightarrow> CNV_ANNOT (\<lambda>'x. f x) (\<lambda>'x. f' x) (Ra\<rightarrow>Rr)"
  "\<And>f f I R. \<lbrakk>undefined (''Id tag not yet supported'',f)\<rbrakk> 
    \<Longrightarrow> CNV_ANNOT (OP (ID_TAG f) :::\<^sub>i I) f R"
  "\<And>f I R. \<lbrakk> INDEP R; REL_OF_INTF I R \<rbrakk> 
    \<Longrightarrow> CNV_ANNOT (OP f :::\<^sub>i I) (OP f ::: R) R"
  "\<And>t t' R. CNV_ANNOT t t' R \<Longrightarrow> CNV_ANNOT (t ::: R) t' R"
  "\<And>t t' name R. \<lbrakk> #name=R; CNV_ANNOT t t' R \<rbrakk> \<Longrightarrow> CNV_ANNOT (t ::#name) t' R"
  by simp_all

consts i_of_rel :: "'a \<Rightarrow> 'b"

lemma ROI_P_app: -- "Only if interface is really application"
  "REL_OF_INTF_P I R \<Longrightarrow> REL_OF_INTF I R"
  by auto

lemma ROI_app: -- "Only if interface is really application"
  "\<lbrakk> REL_OF_INTF I R; REL_OF_INTF_P J S \<rbrakk> \<Longrightarrow> REL_OF_INTF_P (\<langle>I\<rangle>\<^sub>iJ) (\<langle>R\<rangle>S)"
  by auto

lemma ROI_i_of_rel:
  "REL_OF_INTF_P (i_of_rel S) S"
  "REL_OF_INTF (i_of_rel R) R"
  by auto

lemma ROI_const:
  "REL_OF_INTF_P J S"
  "REL_OF_INTF I R"
  by auto

lemma ROI_init:
  assumes "CNV_ANNOT a a' R"
  assumes "(c,a')\<in>R"
  shows "(c,a)\<in>R"
  using assms by simp

lemma REL_OF_INTF_I: "REL_OF_INTF I R" by simp

ML {*
signature AUTOREF_REL_INF = sig
  val roi_tac: Proof.context -> tactic'
  val roi_step_tac: Proof.context -> tactic'
  val roi_phase: Autoref_Phases.phase
  val cfg_sbias: int Config.T

  val setup: theory -> theory
end

structure Autoref_Rel_Inf :AUTOREF_REL_INF = struct

  val cfg_sbias = 
    Attrib.setup_config_int @{binding autoref_sbias} (K 100)


  structure rel_indirect = Named_Thms (
    val name = @{binding autoref_rel_indirect}
    val description = "Indirect relator bindings"
  )

  fun rel_of_intf_thm ctxt I = let
    fun 
      roi (Free (n,_)) ctxt = let 
        val (Rn,ctxt) = yield_singleton Variable.variant_fixes ("R_" ^ n) ctxt
      in (Free (Rn,dummyT),ctxt) end
    | roi (Const (n,_)) ctxt = let 
        val n = Long_Name.base_name n
        val (Rn,ctxt) = yield_singleton Variable.variant_fixes ("R_" ^ n) ctxt
      in (Free (Rn,dummyT),ctxt) end
    | roi @{mpat "\<langle>?Ia\<rangle>\<^sub>i?Ib"} ctxt = let
        val (Ra,ctxt) = roi Ia ctxt
        val (Rb,ctxt) = roi Ib ctxt
      in 
        (Const (@{const_name relAPP},dummyT)$Rb$Ra,ctxt)
      end
    | roi @{mpat "i_of_rel ?R"} ctxt = (R,ctxt)
    | roi t _ = raise TERM ("rel_of_intf: Unexpected interface", [t])

    val orig_ctxt = ctxt
    val (I,ctxt) = yield_singleton (Variable.import_terms true) I ctxt
    val (R,ctxt) = roi I ctxt
    val res = Const (@{const_name REL_OF_INTF},dummyT)$I$R
    val res = Syntax.check_term ctxt res
    val res = singleton (Variable.export_terms ctxt orig_ctxt) res
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of ctxt

    val thm = Goal.prove_internal ctxt [] res (fn _ => resolve_tac ctxt @{thms REL_OF_INTF_I} 1)
  in thm end


  fun roi_step_tac ctxt = let
    val ind_net = rel_indirect.get ctxt |> Tactic.build_net
  in
    IF_EXGOAL (
      assume_tac ctxt
      ORELSE'
      Indep_Vars.indep_tac ctxt
      ORELSE' resolve_from_net_tac ctxt ind_net
      ORELSE'
      (fn i => fn st => 
        case Logic.concl_of_goal (Thm.prop_of st) i of
          @{mpat "Trueprop (CNV_ANNOT _ _ _)"} => 
            resolve_tac ctxt @{thms CNV_ANNOT} i st
        | @{mpat "Trueprop (REL_OF_INTF ?I _)"} => 
            resolve_tac ctxt [rel_of_intf_thm ctxt I] i st
        | _ => Seq.empty
      

      (*
        | @{mpat "Trueprop (REL_OF_INTF (\<langle>_\<rangle>\<^sub>i_) _)"} => 
            rtac @{thm ROI_P_app} i st
        | @{mpat "Trueprop (REL_OF_INTF_P (\<langle>_\<rangle>\<^sub>i_) _)"} => 
            rtac @{thm ROI_app} i st
        | @{mpat "Trueprop (REL_OF_INTF_P (i_of_rel _) _)"} => 
            resolve_tac ctxt @{thms ROI_i_of_rel} i st
        | @{mpat "Trueprop (REL_OF_INTF (i_of_rel _) _)"} => 
            resolve_tac ctxt @{thms ROI_i_of_rel} i st
        | _ => resolve_tac ctxt @{thms ROI_const} i st
      *)
      )
    )
  end

  fun roi_tac ctxt = 
    REPEAT_ALL_NEW_FWD (DETERM o roi_step_tac ctxt)

  fun roi_analyze _ i j _ = (i = j)
  fun roi_pretty_failure _ i j _ = 
    if i = j then
      Pretty.str "No failure"
    else 
      Pretty.str "Relator inference error"

  val roi_phase = {
    init = I,
    tac = (fn ctxt => Seq.INTERVAL (resolve_tac ctxt @{thms ROI_init} THEN' roi_tac ctxt)),
    analyze = roi_analyze,
    pretty_failure = roi_pretty_failure
  }

  val setup = rel_indirect.setup

end
*}

setup Autoref_Rel_Inf.setup

end
