section {* Infrastructure for Multi-Phase Methods *}
theory Autoref_Phases
imports "../Lib/Refine_Lib"
begin

ML {*

  signature AUTOREF_PHASES = sig
    type phase = {
      init: Proof.context -> Proof.context,
      tac: Proof.context -> int -> int -> tactic,
      analyze: Proof.context -> int -> int -> thm -> bool,
      pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T
    }

    val register_phase: string -> int -> phase ->
      morphism -> Context.generic -> Context.generic
    val delete_phase: string -> morphism -> Context.generic -> Context.generic
    val get_phases: Proof.context -> (string * int * phase) list

    val get_phase: string -> Proof.context -> (string * int * phase) option

    val init_phase: (string * int * phase) -> Proof.context -> Proof.context
    val init_phases: 
      (string * int * phase) list -> Proof.context -> Proof.context

    val init_data: Proof.context -> Proof.context

    val declare_solver: thm list -> binding -> string
      -> (Proof.context -> tactic') -> morphism
      -> Context.generic -> Context.generic

    val phase_tac: (string * int * phase) -> Proof.context -> tactic'
    val phases_tac: (string * int * phase) list -> Proof.context -> tactic'
    val all_phases_tac: Proof.context -> tactic'

    val phases_tacN: string list -> Proof.context -> tactic'
    val phase_tacN: string -> Proof.context -> tactic'

    val cfg_debug: bool Config.T
    val cfg_trace: bool Config.T
    val cfg_keep_goal: bool Config.T

  end

  structure Autoref_Phases :AUTOREF_PHASES = struct
    type phase = {
      init: Proof.context -> Proof.context,
      tac: Proof.context -> int -> int -> tactic,
      analyze: Proof.context -> int -> int -> thm -> bool,
      pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T
    }

    fun phase_order ((_,i1,_), (_,i2,_)) = (int_ord (i1,i2))

    structure phase_data = Generic_Data (
      type T = (string * int * phase) list
      val empty = []
      val merge = Ord_List.merge phase_order
      val extend = I
    )

    val cfg_debug = Attrib.setup_config_bool @{binding autoref_dbg} (K false)
    val cfg_trace = Attrib.setup_config_bool @{binding autoref_trace} (K false)
    val cfg_keep_goal = 
      Attrib.setup_config_bool @{binding autoref_keep_goal} (K false)

    fun register_phase n i p _ = 
      phase_data.map (Ord_List.insert phase_order (n,i,p))

    fun delete_phase n _ = 
      phase_data.map (filter (curry op = n o #1))

    val get_phases = phase_data.get o Context.Proof

    fun get_phase name ctxt = phase_data.get (Context.Proof ctxt) 
      |> find_first (curry op = name o #1)

    fun init_phase (_,_,p) ctxt = #init p ctxt
    val init_phases = fold init_phase 

    structure autoref_state = Proof_Data (
      type T = bool
      fun init _ = false
    )

    (* TODO: Workaround to have enough data for solvers in context *)
    fun init_data ctxt = if autoref_state.get ctxt then
      ctxt
    else let
      val ctxt = init_phases (get_phases ctxt) ctxt
      val ctxt = autoref_state.put true ctxt
    in ctxt end

    fun declare_solver triggers name desc tac phi context = let
      val name_s = Morphism.binding phi name |>
        Context.cases Sign.full_name Proof_Context.full_name context
      
      fun tac' ctxt = 
        if autoref_state.get ctxt then 
          tac ctxt
        else 
          let
            val _ = warning ("Autoref-Solver " ^ name_s 
              ^ " invoked outside autoref context." 
              ^ " Initializing new context (slow)")
          in 
            tac (init_data ctxt) 
          end
    in
      Tagged_Solver.declare_solver triggers name desc tac' phi context
    end

    local
      fun handle_fail_tac pname p ctxt i j st = let
        val dbg_info = Config.get ctxt cfg_debug
        val keep_goal = Config.get ctxt cfg_keep_goal

        val prt_term = Syntax.pretty_term ctxt;
        fun pretty_subgoal (n, A) =
          Pretty.markup (Markup.subgoal "")
            [Pretty.str (" " ^ string_of_int n ^ ". "), prt_term A];
        fun pretty_subgoals () = let
          val (As,_) = Logic.strip_horn (Thm.prop_of st)
          val As = drop (i - 1) As |> take (j - i + 1)
        in 
          map pretty_subgoal (1 upto length As ~~ As) 
          |> Pretty.fbreaks |> Pretty.block
        end;

      in
        if dbg_info then 
          let
            val pt = #pretty_failure p ctxt i j st
            val _ = tracing ("Phase \"" ^ pname ^ "\" failed"  )
            val _ = tracing (Pretty.string_of pt)
            val _ = tracing "Remaining goals:"
            val _ = tracing (Pretty.string_of (pretty_subgoals ()))
          in () end
        else ();
        if keep_goal then Seq.single st else Seq.empty
      end

      fun ite_succeed_tac p tac1 tac2 ctxt i j st = 
        if #analyze p ctxt i j st then
          tac1 ctxt i j st
        else 
          tac2 ctxt i j st

      fun do_phase (pname,_,p) tac1 ctxt = let
        val do_trace = Config.get ctxt cfg_trace
        fun tr msg tac ctxt i j st = (if do_trace then
          tracing msg
        else (); tac ctxt i j st)

        fun ptac ctxt i j = DETERM (#tac p ctxt i j)
          THEN ((PRIMITIVE (Drule.zero_var_indexes)))

        fun timed_ptac ctxt i j = let
          val tac = ptac ctxt i j
        in fn st => let
            val start = Timing.start ()
            val res = tac st
            val timing = Timing.result start
            val _ = if do_trace then Timing.message timing |> tracing else () 
          in
            res
          end
        end

      in
        ( tr ("Phase \"" ^ pname ^ "\"") timed_ptac ctxt)
        THEN_INTERVAL 
          ite_succeed_tac p
            ( tr ("Success (Phase \"" ^ pname ^ "\")") tac1) 
            ( tr ("Fail (Phase \"" ^ pname ^ "\")") (handle_fail_tac pname p))
            ctxt
      end
        
      fun do_phases [] _ = (fn _ => fn _ => Seq.single)
        | do_phases (p::ps) ctxt = do_phase p (do_phases ps) ctxt


      fun is_sorted _ [] = true
        | is_sorted _ [_] = true
        | is_sorted ord (a::b::l) = 
            ord (a,b) <> GREATER andalso is_sorted ord (b::l)

    in
      fun phase_tac p ctxt = let
        val ctxt = init_phase p ctxt
      in
        SINGLE_INTERVAL
          (do_phase p (fn _ => fn _ => fn _ => all_tac) ctxt)
      end

      fun phases_tac ps ctxt = let
        val ctxt = init_phases ps ctxt
      in
        SINGLE_INTERVAL (do_phases ps ctxt)
      end

      fun all_phases_tac ctxt = phases_tac (get_phases ctxt) ctxt

      fun get_phase_err ctxt name = case get_phase name ctxt of
        NONE => error ("Unknown phase: " ^ name)
      | SOME p => p

      fun phase_tacN name ctxt = 
        phase_tac (get_phase_err ctxt name) ctxt

      fun phases_tacN names ctxt = let
        val ps = map (get_phase_err ctxt) names
        val _ = if is_sorted phase_order ps then () 
          else warning "Non-standard phase order"
          
      in
        phases_tac ps ctxt
      end 
  
    end
  end

*}

end
