theory Tagged_Solver
imports Refine_Util
begin

(* TODO/FIXME:
  A solver is some named entity, and it should be possible to
  reference it by its short/long name like a constant or a theorem!
*)

ML {*
  signature TAGGED_SOLVER = sig
    type solver = thm list * string * string * (Proof.context -> tactic')
    
    val get_solvers: Proof.context -> solver list
    val declare_solver: thm list -> binding -> string 
      -> (Proof.context -> tactic') -> morphism 
      -> Context.generic -> Context.generic

    val lookup_solver: string -> Context.generic -> solver option
    val add_triggers: string -> thm list -> morphism ->
      Context.generic -> Context.generic

    val delete_solver: string -> morphism -> Context.generic -> Context.generic

    val tac_of_solver: Proof.context -> solver -> tactic'

    val get_potential_solvers: Proof.context -> int -> thm -> solver list
    val get_potential_tacs: Proof.context -> int -> thm -> tactic' list

    val solve_greedy_step_tac: Proof.context -> tactic'
    val solve_greedy_tac: Proof.context -> tactic'
    val solve_greedy_keep_tac: Proof.context -> tactic'

    val solve_full_step_tac: Proof.context -> tactic'
    val solve_full_tac: Proof.context -> tactic'
    val solve_full_keep_tac: Proof.context -> tactic'

    val cfg_keep: bool Config.T
    val cfg_trace: bool Config.T
    val cfg_full: bool Config.T
    val cfg_step: bool Config.T

    val solve_tac: Proof.context -> tactic'

    val pretty_solvers: Proof.context -> Pretty.T
  end

  structure Tagged_Solver : TAGGED_SOLVER = struct
    type solver = thm list * string * string * (Proof.context -> tactic')

    structure solvers = Generic_Data (
      type T = solver Item_Net.T * solver Symtab.table
      val empty = (Item_Net.init 
        (op = o apply2 #2) 
        (fn p:solver => #1 p |> map Thm.concl_of)
      ,
        Symtab.empty
      )
  
      fun merge ((n1,t1),(n2,t2)) 
        = (Item_Net.merge (n1,n2), Symtab.merge (op = o apply2 #2) (t1,t2))
      val extend = I 
    )

    fun get_solvers ctxt = solvers.get (Context.Proof ctxt) 
      |> #2 |> Symtab.dest |> map #2

    fun lookup_solver n context = let
      val tab = solvers.get context |> #2
    in
      Symtab.lookup tab n
    end

    fun add_triggers n thms phi context = 
      case lookup_solver n context of
        NONE => 
          error ("Undefined solver: " ^ n)
      | SOME (trigs,n,desc,tac) => let
          val thms = map (Morphism.thm phi) thms
          val trigs = thms @ trigs
          val solver = (trigs,n,desc,tac)
        in 
          solvers.map (Item_Net.update solver ## Symtab.update (n, solver)) 
            context
        end

    fun declare_solver thms n desc tac phi context = let
      val thms = map (Morphism.thm phi) thms
      val n = Morphism.binding phi n
      val n = Context.cases Sign.full_name Proof_Context.full_name context n
      val _ = 
        if Symtab.defined (solvers.get context |> #2) n then
          error ("Duplicate solver " ^ n)
        else ()
      val solver = (thms,n,desc,tac)
    in
      solvers.map (Item_Net.update solver ## Symtab.update (n,solver)) context
    end

    fun delete_solver n _ context = 
      case lookup_solver n context of
        NONE => error ("Undefined solver: " ^ n)
      | SOME solver => 
          solvers.map (Item_Net.remove solver ## Symtab.delete (#2 solver))
            context

    val cfg_keep = 
      Attrib.setup_config_bool @{binding tagged_solver_keep} (K false)

    val cfg_trace = 
      Attrib.setup_config_bool @{binding tagged_solver_trace} (K false)

    val cfg_step = 
      Attrib.setup_config_bool @{binding tagged_solver_step} (K false)

    val cfg_full = 
      Attrib.setup_config_bool @{binding tagged_solver_full} (K false)



    (* Get potential solvers. Overapproximation caused by net *)
    fun get_potential_solvers ctxt i st = 
      let
        val concl = Logic.concl_of_goal (Thm.prop_of st) i
        val net = solvers.get (Context.Proof ctxt) |> #1
        val solvers = Item_Net.retrieve net concl
      in solvers end

    fun notrace_tac_of_solver ctxt (thms,_,_,tac) = 
      match_tac ctxt thms THEN' tac ctxt

    fun trace_tac_of_solver ctxt (thms,name,_,tac) i st = 
      let
        val _ = tracing ("Trying solver " ^ name)
        val r = match_tac ctxt thms i st
      in
        case Seq.pull r of 
          NONE => (tracing "  No trigger"; Seq.empty)
        | SOME _ => let 
            val r = Seq.maps (tac ctxt i) r
          in
            case Seq.pull r of 
              NONE => (tracing ("  No solution (" ^ name ^ ")"); Seq.empty)
            | SOME _ => (tracing ("  OK (" ^ name ^ ")"); r)
          end
      end

    fun tac_of_solver ctxt = 
      if Config.get ctxt cfg_trace then
        trace_tac_of_solver ctxt
      else
        notrace_tac_of_solver ctxt
    
    fun get_potential_tacs ctxt i st = 
      if i <= Thm.nprems_of st then
        eq_assume_tac :: (
          get_potential_solvers ctxt i st
          |> map (tac_of_solver ctxt)
        )
      else []

    fun solve_greedy_step_tac ctxt i st = 
      (FIRST' (get_potential_tacs ctxt i st)) i st

    fun solve_full_step_tac ctxt i st = 
      (APPEND_LIST' (get_potential_tacs ctxt i st) i st)

    (* Try to solve, take first matching tactic, but allow backtracking over
       its results *)
    fun solve_greedy_tac ctxt i st = let
      val tacs = get_potential_tacs ctxt i st
    in
      (FIRST' tacs THEN_ALL_NEW_FWD solve_greedy_tac ctxt) i st
    end

    (* Try to solve. Allow backtracking over matching tactics. *)
    fun solve_full_tac ctxt i st = let
      val tacs = get_potential_tacs ctxt i st
    in
      (APPEND_LIST' tacs THEN_ALL_NEW_FWD solve_full_tac ctxt) i st
    end

    fun solve_greedy_keep_tac ctxt i st = let
      val tacs = get_potential_tacs ctxt i st
    in
      (FIRST' tacs THEN_ALL_NEW_FWD (TRY o solve_greedy_keep_tac ctxt)) i st
    end

    fun solve_full_keep_tac ctxt i st = let
      val tacs = get_potential_tacs ctxt i st
    in
      (APPEND_LIST' tacs THEN_ALL_NEW_FWD (TRY o solve_full_keep_tac ctxt)) i st
    end

    fun solve_tac ctxt = 
      case (Config.get ctxt cfg_keep, Config.get ctxt cfg_step, 
            Config.get ctxt cfg_full) of
        (_,true,false) => solve_greedy_step_tac ctxt
      | (_,true,true) => solve_full_step_tac ctxt
      | (true,false,false) => solve_greedy_keep_tac ctxt
      | (false,false,false) => solve_greedy_tac ctxt
      | (true,false,true) => solve_full_keep_tac ctxt
      | (false,false,true) => solve_full_tac ctxt


    fun pretty_solvers ctxt = let
      fun pretty_solver (ts,name,desc,_) = Pretty.block (
        Pretty.str (name ^ ": " ^ desc) :: Pretty.fbrk 
        :: Pretty.str ("Triggers: ")
        :: Pretty.commas (map (Thm.pretty_thm ctxt) ts))

      val solvers = get_solvers ctxt
    in
      Pretty.big_list "Solvers:" (map pretty_solver solvers)
    end
  end
  *}

method_setup tagged_solver = {* let
  open Refine_Util
  val flags = 
        parse_bool_config "keep" Tagged_Solver.cfg_keep
    ||  parse_bool_config "trace" Tagged_Solver.cfg_trace
    ||  parse_bool_config "full" Tagged_Solver.cfg_full
    ||  parse_bool_config "step" Tagged_Solver.cfg_step

in
  parse_paren_lists flags >> (fn _ => fn ctxt => 
    SIMPLE_METHOD' (Tagged_Solver.solve_tac ctxt)
  )
end
*} "Select tactic to solve goal by pattern"


term True
(* Localization Test *)
(*
locale foo = 
  fixes A b
  assumes A: "A x = True"
begin
  definition "B == A"

  lemma AI: "A x" unfolding A ..
  lemma A_trig: "A x ==> A x" .
  lemma BI: "A x ==> B x" unfolding B_def .
  lemma B_trig: "B x ==> B x" .
  
  declaration {* fn phi =>
    Tagged_Solver.declare_solver @{thms A_trig} 
      @{binding "A_solver"} "description" 
      (K (rtac (Morphism.thm phi @{thm AI}))) phi
    *}

  ML_val {*
    Tagged_Solver.pretty_solvers @{context} |> Pretty.writeln
    *}

  (* FIXME: Does not work because of improper naming!
  declaration {*
    Tagged_Solver.add_triggers "local.A_solver" @{thms A_trig}
    *}
  *)

  declaration {* fn phi =>
    Tagged_Solver.declare_solver @{thms B_trig} 
      @{binding "B_solver"} "description" 
      (K (rtac (Morphism.thm phi @{thm BI}))) phi
    *}

  ML_val {*
    Tagged_Solver.pretty_solvers @{context} |> Pretty.writeln
    *}

end

definition "TAG x == True"
interpretation tag: foo TAG 1
  apply unfold_locales
  unfolding TAG_def by simp

ML_val {*
  Tagged_Solver.pretty_solvers @{context} |> Pretty.writeln
  *}

definition "TAG' x == True"
interpretation tag': foo TAG' 2
  apply unfold_locales
  unfolding TAG'_def by simp

interpretation tag2: foo TAG 3
  by unfold_locales

ML_val {*
  Tagged_Solver.pretty_solvers @{context} |> Pretty.writeln
  *}


lemma "tag.B undefined"
  by (tagged_solver (keep))

declaration {* Tagged_Solver.delete_solver "Tagged_Solver.tag.B_solver" *}

ML_val {*
  Tagged_Solver.pretty_solvers @{context} |> Pretty.writeln
  *}
*)

end

