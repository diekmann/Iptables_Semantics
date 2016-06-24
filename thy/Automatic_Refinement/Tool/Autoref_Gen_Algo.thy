section {* Infrastructure for Generic Algorithms *}
theory Autoref_Gen_Algo
imports Autoref_Translate
begin

(* TODO/FIXME: The priority ordering is not yet suited for generic
  algorithms! If a refinement rule is generic, the homogenity and relator
  measures make no sense, as they are applied to schematic variables.
  However, currently generic algorithms seem to have lower priority than
  specific ones, so we can probably live with this problem for a while.
*)


definition [simp, autoref_tag_defs]: "GEN_ALGO_tag P == P"
lemma GEN_ALGO_tagI: "P ==> GEN_ALGO_tag P" by simp
abbreviation "SIDE_GEN_ALGO P == PREFER_tag (GEN_ALGO_tag P)"

ML {*
  structure Autoref_Gen_Algo = struct 

    fun transform_ga_rule context rl = let
      val ctxt = Context.proof_of context

      fun warn msg = Pretty.block [
        Pretty.str msg, 
        Pretty.brk 1,
        Pretty.str "(",
        Thm.pretty_thm ctxt rl,
        Pretty.str ")"
        ]
      |> Pretty.string_of |> warning
   
      fun is_side_prem @{mpat "Trueprop (PREFER_tag _)"} = true
        | is_side_prem @{mpat "Trueprop (DEFER_tag _)"} = true
        | is_side_prem _ = false
    in
      if exists is_side_prem (Thm.prems_of rl) then
        warn ("autoref_ga_rules: SIDE condition premise not allowed here")
      else ()
      ;
      case Thm.concl_of rl of
        @{mpat "Trueprop ((_,_)\<in>_)"} => 
          warn ("autoref_ga_rules: Refinement condition conclusion. Did you"
            ^" mean an autoref_rule?")  
      | _ => ()
      ;
      [rl]
    end

    structure ga_side_thms = Named_Sorted_Thms (
      val name = @{binding autoref_ga_rules}
      val description = "Additional rules for generic algorithm side conditions"
      val sort = K I
      val transform = transform_ga_rule
    )

    fun side_ga_tac ctxt = resolve_tac ctxt (ga_side_thms.get ctxt)

    fun side_ga_op_tac ctxt = 
      SOLVED' (Autoref_Tacticals.REPEAT_ON_SUBGOAL 
        (Autoref_Translate.trans_step_tac ctxt))


    val setup = ga_side_thms.setup

    fun decl_setup phi = I
    #> Tagged_Solver.declare_solver @{thms GEN_ALGO_tagI} @{binding GEN_ALGO} 
        "Autoref: Generic algorithm side condition solver" 
        ( side_ga_tac) phi
    #> Autoref_Phases.declare_solver @{thms GEN_OP_tagI} @{binding GEN_OP} 
        "Autoref: Generic algorithm operation instantiation" 
        ( side_ga_op_tac) phi
  end
*}  

setup Autoref_Gen_Algo.setup
declaration Autoref_Gen_Algo.decl_setup

end
