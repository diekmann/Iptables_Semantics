section {* Automatic Refinement Tool *}
theory Autoref_Tool
imports 
  Autoref_Translate 
  Autoref_Gen_Algo
  Autoref_Relator_Interface
begin
  subsection {* Standard setup *}

text {* Declaration of standard phases *}

declaration {* fn phi => let open Autoref_Phases in
  I
  #> register_phase "id_op" 10 Autoref_Id_Ops.id_phase phi
  #> register_phase "rel_inf" 20 
       Autoref_Rel_Inf.roi_phase phi
  #> register_phase "fix_rel" 22
       Autoref_Fix_Rel.phase phi
  #> register_phase "trans" 30
       Autoref_Translate.trans_phase phi
end
*}


(*
declaration {* fn phi => let open Autoref_Phases in
  I
  #> register_phase "id_op" 10 Autoref_Id_Ops.id_ops_phase phi
  #> register_phase "rel_inf" 20 
       Autoref_Rel_Inf.hm_infer_rel_phase phi
  #> register_phase "fix_rel" 21
       Autoref_Fix_Rel.phase phi
  #> register_phase "trans" 30
       Autoref_Translate.trans_phase phi
end
*}
*)

text {* Main method *}
method_setup autoref = {* let
    open Refine_Util
    val autoref_flags = 
          parse_bool_config "trace" Autoref_Phases.cfg_trace
      ||  parse_bool_config "debug" Autoref_Phases.cfg_debug
      ||  parse_bool_config "keep_goal" Autoref_Phases.cfg_keep_goal

    val autoref_phases = 
      Args.$$$ "phases" |-- Args.colon |-- Scan.repeat1 Args.name

  in
    parse_paren_lists autoref_flags 
    |-- Scan.option (Scan.lift (autoref_phases)) >>
    ( fn phases => fn ctxt => SIMPLE_METHOD' (
      (
        case phases of
          NONE => Autoref_Phases.all_phases_tac
        | SOME names => Autoref_Phases.phases_tacN names
      ) (Autoref_Phases.init_data ctxt) 
      (* TODO: If we want more fine-grained initialization here, solvers have
         to depend on phases, or on data that they initialize if necessary *)
    ))

  end

 *} "Automatic Refinement"

subsection {* Tools *}

setup {*
  let
    fun higher_order_rl_of ctxt thm = case Thm.concl_of thm of
      @{mpat "Trueprop ((_,?t)\<in>_)"} => let
        val (f,args) = strip_comb t
      in
        if length args = 0 then 
          thm
        else let
          val cT = TVar(("'c",0), @{sort type})
          val c = Var (("c",0),cT)
          val R = Var (("R",0), HOLogic.mk_setT (HOLogic.mk_prodT (cT, fastype_of f)))
          val goal = 
            HOLogic.mk_mem (HOLogic.mk_prod (c,f), R)
            |> HOLogic.mk_Trueprop
            |> Thm.cterm_of ctxt

          val res_thm = Goal.prove_internal ctxt [] goal (fn _ => 
            REPEAT (resolve_tac ctxt @{thms fun_relI} 1)
            THEN (resolve_tac ctxt [thm] 1)
            THEN (ALLGOALS (assume_tac ctxt))
          )
        in
          res_thm
        end
      end
    | _ => raise THM("Expected autoref rule",~1,[thm])

    val higher_order_rl_attr = 
      Thm.rule_attribute [] (higher_order_rl_of o Context.proof_of)
  in
    Attrib.setup @{binding autoref_higher_order_rule} 
      (Scan.succeed higher_order_rl_attr) "Autoref: Convert rule to higher-order form"
  end
*}

subsection {* Advanced Debugging *}
method_setup autoref_trans_step = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Translate.trans_dbg_step_tac (Autoref_Phases.init_data ctxt)
  ))
  *} "Single translation step, leaving unsolved side-coditions"

method_setup autoref_trans_step_only = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Translate.trans_step_only_tac (Autoref_Phases.init_data ctxt)
  ))
  *} "Single translation step, not attempting to solve side-coditions"

method_setup autoref_side = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Translate.side_dbg_tac (Autoref_Phases.init_data ctxt)
  ))
  *} "Solve side condition, leave unsolved subgoals"

method_setup autoref_try_solve = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Fix_Rel.try_solve_tac (Autoref_Phases.init_data ctxt)
  ))
  *} "Try to solve constraint and trace debug information"

method_setup autoref_solve_step = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Fix_Rel.solve_step_tac (Autoref_Phases.init_data ctxt)
  ))
  *} "Single-step of constraint solver"

method_setup autoref_id_op = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Id_Ops.id_tac ctxt
  ))
*}

method_setup autoref_solve_id_op = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Autoref_Id_Ops.id_tac (Config.put Autoref_Id_Ops.cfg_ss_id_op false ctxt)
  ))
*}



ML {*
  structure Autoref_Debug = struct
    fun print_thm_pairs ctxt = let
      val ctxt = Autoref_Phases.init_data ctxt
      val p = Autoref_Fix_Rel.thm_pairsD_get ctxt
        |> Autoref_Fix_Rel.pretty_thm_pairs ctxt
        |> Pretty.string_of
    in
      warning p
    end

    fun print_thm_pairs_matching ctxt cpat = let
      val pat = Thm.term_of cpat
      val ctxt = Autoref_Phases.init_data ctxt
      val thy = Proof_Context.theory_of ctxt

      fun matches NONE = false
        | matches (SOME (_,(f,_))) = Pattern.matches thy (pat,f)

      val p = Autoref_Fix_Rel.thm_pairsD_get ctxt
        |> filter (matches o #1)
        |> Autoref_Fix_Rel.pretty_thm_pairs ctxt
        |> Pretty.string_of
    in
      warning p
    end
  end
*}


text {* General casting-tag, that allows type-casting on concrete level, while 
  being identity on abstract level. *}
definition [simp]: "CAST \<equiv> id"
lemma [autoref_itype]: "CAST ::\<^sub>i I \<rightarrow>\<^sub>i I" by simp

(* TODO: This idea does currently not work, b/c a homogeneity rule
  will be created from the (\<lambda>x. x, CAST)\<in>R \<rightarrow> R rule, which will always
  be applied first! As a workaround, we make the cast mandatory!
*)
(*lemma [autoref_rules]: 
  assumes "PRIO_TAG_GEN_ALGO"
  shows "(\<lambda>x. x,CAST) \<in> R \<rightarrow> R"
  by auto
*)



text {* Hide internal stuff *}

notation (input) rel_ANNOT (infix ":::\<^sub>r" 10)
notation (input) ind_ANNOT (infix "::#\<^sub>r" 10)


locale autoref_syn begin
  notation (input) APP (infixl "$" 900)
  notation (input) rel_ANNOT (infix ":::" 10)
  notation (input) ind_ANNOT (infix "::#" 10)
  notation OP ("OP")
  notation (input) ABS (binder "\<lambda>''" 10)
end

no_notation (input) APP (infixl "$" 900)
no_notation (input) ABS (binder "\<lambda>''" 10)

no_notation (input) rel_ANNOT (infix ":::" 10)
no_notation (input) ind_ANNOT (infix "::#" 10)

hide_const (open) PROTECT ANNOT OP APP ABS ID_FAIL rel_annot ind_annot

end
