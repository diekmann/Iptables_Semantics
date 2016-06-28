theory Select_Solve
imports Main Refine_Util
begin

(*
  Focus on subgoal, respect schematic variable instantiations.
  *** Be aware that this seems to be slower then to work with
    big subgoals! ***

*)

lemma retrofit_with_prems:
  fixes P Q R TAG
  assumes 1: "PROP P ==> PROP Q" (* Original goal state *)
  assumes 2: "PROP R ==> PROP TAG &&& PROP P" (* Result of first subgoal *)
  shows "PROP R ==> PROP Q" (* New goal state with &&&*)
proof -
  assume "PROP R"
  from this[THEN 2, THEN conjunctionD2] have "PROP P" .
  with 1 show "PROP Q" .
qed

lemma retrofit_no_prems:
  fixes P Q TAG
  assumes 1: "PROP P ==> PROP Q" (* Original goal state *)
  assumes 2: "PROP TAG &&& PROP P" (* Result of first subgoal *)
  shows "PROP Q" (* New goal state *)
proof -
  from 2 have "PROP P" by (rule conjunctionD2)
  thus "PROP Q" by (rule 1)
qed

consts NO_TAG :: "prop"
lemma NO_TAG: "TERM NO_TAG" .



ML {*
signature SELECT_SOLVE = sig
  val PREFER_SOLVED: tactic -> tactic
  val IF_SUBGOAL_SOLVED: tactic -> tactic -> tactic -> tactic
  val TRY_SOLVE_FWD: int -> tactic -> tactic
  val SELECT_FIRST: Proof.context -> tactic -> tactic
  val AS_FIRSTGOAL: tactic -> tactic'
  val REPEAT_SOLVE_FWD_SELECT: Proof.context -> int -> tactic' -> tactic' 
end

structure Select_Solve :SELECT_SOLVE = struct
  fun PREFER_SOLVED tac st = let
    val n = Thm.nprems_of st
    val res = tac st
    (*val res' = Seq.append 
      (Seq.filter (has_fewer_prems n) res)
      (Seq.filter (not o has_fewer_prems n) res)*)

    val res' = Seq.filter (has_fewer_prems n) res
  in
    res'
  end

  fun IF_SUBGOAL_SOLVED tac1 then_tac else_tac st = let
    val n = Thm.nprems_of st
  in
    (tac1 THEN COND (has_fewer_prems n) then_tac else_tac) st
  end

  fun TRY_SOLVE_FWD i tac st = 
    if i <= 0 then 
      Seq.single st 
    else
      IF_UNSOLVED (
        IF_SUBGOAL_SOLVED tac (TRY_SOLVE_FWD (i-1) tac) all_tac
      ) st

  fun TRY_SOLVE_ALL_NEW_FWD tac1 tac2 tac3 st = let
    val n = Thm.nprems_of st
  in 
    (
      tac1 THEN_ELSE 
        ( fn st' => let val n' = Thm.nprems_of st' in TRY_SOLVE_FWD (n' - n + 1) tac2 st' end,
          tac3)
    ) st 
  end


  fun SELECT_FIRST ctxt tac st = if Thm.nprems_of st < 2 then tac st
  else let
    (*val _ = print_tac "Focusing" st*)

    (* Extract first subgoal *)
    val (P,Q) = Thm.dest_implies (Thm.cprop_of st)

    (*val _ = "Extracted: " ^ @{make_string} P |> tracing*)

    (* Prepare tag *)
    local 
      fun intr_bal [] = @{thm NO_TAG}
        | intr_bal l = Conjunction.intr_balanced l

      val t = Thm.term_of P 

      val vars = Term.add_vars t []
      val tvars = Term.add_tvars t []
      val vtvars = fold (Term.add_tvarsT o #2) vars []
      val tvars = subtract op = vtvars tvars

      val tvars_tag = tvars
        |> map (Drule.mk_term o Thm.cterm_of ctxt o Logic.mk_type o TVar)
        |> intr_bal

      val vars_tag = vars
        |> map (Drule.mk_term o Thm.cterm_of ctxt o Var)
        |> intr_bal
    in
      val tag_thm = Conjunction.intr tvars_tag vars_tag
    end

    val TAG = Thm.cprop_of tag_thm

    (* Prepare new proof state *)
    val st' = Conjunction.mk_conjunction (TAG, P)
      |> Goal.init
      |> Conjunction.curry_balanced 2
      |> Thm.elim_implies tag_thm

    (*val _ = "New proof state: " ^ @{make_string} st' |> tracing*)

    (*val _ = print_tac "New state" st'*)

    (* Apply proof *)
    val seq = tac st'

    fun elim_implies thA thAB = 
      case try Thm.dest_implies (Thm.cprop_of thAB) of 
        SOME (A,_) => (
          A aconvc Thm.cprop_of thA
            orelse (
              (*tracing (@{make_string} (term_of A));
              tracing (@{make_string} (prop_of thA));*)
              raise CTERM ("implies_elim: No aconv",[A,Thm.cprop_of thA])
            );
          Thm.elim_implies thA thAB
        )
    | _ => raise THM ("implies_elim: No impl",0,[thAB,thA])

    fun retrofit st' = let
      val st' = Drule.incr_indexes st st'
      val n = Thm.nprems_of st'
      val thm = Conjunction.uncurry_balanced n st'
        |> Goal.conclude
        |> Conv.fconv_rule (Thm.beta_conversion true)
      (*val _ = "Proved: " ^ @{make_string} thm |> tracing*)
    in
      if n=0 then 
        let
          val (TAG',_) = Conjunction.dest_conjunction (Thm.cprop_of thm)
          val inst = Thm.match (TAG, TAG')
          val st = Thm.instantiate inst st 
            |> Conv.fconv_rule (Thm.beta_conversion true)
          val P = Thm.instantiate_cterm inst P
          val Q = Thm.instantiate_cterm inst Q
        in
          @{thm retrofit_no_prems}
          |> Thm.instantiate' [] [SOME P, SOME Q, SOME TAG'] 
          |> Conv.fconv_rule (Thm.beta_conversion true)
          |> elim_implies st
          |> elim_implies thm
        end
      else 
        let
          val (R,TP') = Thm.dest_implies (Thm.cprop_of thm)
          val (TAG',_) = Conjunction.dest_conjunction TP'
          val inst = Thm.match (TAG, TAG')
          val st = Thm.instantiate inst st
            |> Conv.fconv_rule (Thm.beta_conversion true)
          val P = Thm.instantiate_cterm inst P
          val Q = Thm.instantiate_cterm inst Q
        in 
          @{thm retrofit_with_prems}
          |> Thm.instantiate' [] [SOME P, SOME Q, SOME R, SOME TAG']
          |> Conv.fconv_rule (Thm.beta_conversion true)
          |> elim_implies st
          |> elim_implies thm
          |> Conjunction.curry_balanced n
        end
    end

  in
    Seq.map retrofit seq
  end

  fun AS_FIRSTGOAL tac i st = 
    if i <= Thm.nprems_of st then
      (PRIMITIVE (Thm.permute_prems 0 (i-1)) 
      THEN tac 
      THEN PRIMITIVE (Thm.permute_prems 0 (1-i))) st
    else Seq.empty

  fun REPEAT_SOLVE_FWD_SELECT ctxt bias tac = let
    fun BIASED_SELECT tac st = 
      if Thm.nprems_of st < 2 then tac st
      else let
        val s = Drule.size_of_thm st
        (*val _ = if s>100 then string_of_int s |> tracing else ()*)
      in
        if s < bias then 
          tac st 
        else let
          val s1 = Logic.dest_implies (Thm.prop_of st) |> #1 |> size_of_term
        in
          if 5 * s1 < 2 * s then
            SELECT_FIRST ctxt tac st
          else tac st
        end
      end


    fun sg_rec st = IF_UNSOLVED (BIASED_SELECT (
        PREFER_SOLVED (
          TRY_SOLVE_ALL_NEW_FWD (tac 1) sg_rec all_tac
        )
      )) st

  in
    AS_FIRSTGOAL sg_rec
  end
end

*}

end
