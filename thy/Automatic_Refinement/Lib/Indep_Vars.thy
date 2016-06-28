theory Indep_Vars
imports Main Refine_Util Mpat_Antiquot
begin

definition [simp]: "INDEP v \<equiv> True"
lemma INDEPI: "INDEP v" by simp

ML {*
  signature INDEP_VARS = sig
    val indep_tac: Proof.context -> tactic'
  end

  structure Indep_Vars: INDEP_VARS = struct

    local
      fun vsubterms (Abs (_,_,t)) = vsubterms t
        | vsubterms (t as (_$_)) = let
            val (f,args) = strip_comb t
            val args_vsts = map vsubterms args |> flat
          in
            case f of
              (Var (name,vT)) => [(name,vT,fastype_of t,args)]@args_vsts
            | _ => vsubterms f @ args_vsts
          end
        | vsubterms _ = []

      fun indep_vars ctxt t st = let
        val cert = Thm.cterm_of ctxt

        fun inst_of (name,vT,T,args) = let
          val Ts = map fastype_of args |> rev
          val t' = fold absdummy Ts (Var (name,T))
          val inst = ((name, vT), cert t')
        in inst end

        val inst = vsubterms t
          |> distinct (op = o apply2 #1)
          |> map inst_of

        val st' = Drule.instantiate_normalize ([],inst) st
          |> Conv.fconv_rule (Thm.beta_conversion true)
      in
        Seq.single st'
      end

      fun indep_tac_aux ctxt i st = case Logic.concl_of_goal (Thm.prop_of st) i of
        @{mpat "Trueprop (INDEP ?v)"}
          => (indep_vars ctxt v THEN resolve_tac ctxt @{thms INDEPI} i) st
      | _ => Seq.empty

    in
      (* Remove explicit parameters from schematic variable. *)
      fun indep_tac ctxt = IF_EXGOAL
        (CONVERSION Thm.eta_conversion THEN' indep_tac_aux ctxt)
    end
  end
*}

end
