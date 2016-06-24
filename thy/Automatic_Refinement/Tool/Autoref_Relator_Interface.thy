theory Autoref_Relator_Interface
imports Main Autoref_Id_Ops Autoref_Fix_Rel
begin

definition [simp]: "REL_INTF R I \<equiv> True"
lemma REL_INTFI: "REL_INTF R I" by simp


ML {*
  (* Keeping track of relator - interface bindings *)
  signature AUTOREF_RELATOR_INTERFACE = sig
    val mk_intfAPP: term -> term -> term

    val declare_rel_intf: thm -> Context.generic -> Context.generic
    val delete_rel_intf: thm -> Context.generic -> Context.generic
    val get_rel_intfs: Proof.context -> thm list

    val intf_of_rel: Proof.context -> term -> term
    val list_invented_intf: term -> term list
    val warn_invented_intf: Proof.context -> term -> unit

    val itype_of_rule: Proof.context -> thm -> (term * term) option

    val setup: theory -> theory
  end

  structure Autoref_Relator_Interface :AUTOREF_RELATOR_INTERFACE = struct

    structure relator_intf = Named_Thms (
      val name = @{binding autoref_rel_intf}
      val description = "Relator interface declaration"
    )
  
    val declare_rel_intf = relator_intf.add_thm
    val delete_rel_intf = relator_intf.del_thm
    val get_rel_intfs = relator_intf.get

    fun mk_intfAPP I J = let
      val JT = fastype_of J
      val rT = range_type JT
    in
      Const (@{const_name intfAPP},JT --> @{typ interface} --> rT) $ J $ I
    end

    fun intf_of_rel ctxt R = let
      fun dest_ri thm = case Thm.prop_of thm of
        @{mpat "Trueprop (REL_INTF ?R ?I)"} => SOME (R,I)
      | _ => NONE

      val rel_intfs = relator_intf.get ctxt
        |> map Drule.zero_var_indexes
        |> map_filter dest_ri

      val thy = Proof_Context.theory_of ctxt

      fun get_ri R = 
        find_first (fn (p,_) => Pattern.matches thy (p,R)) rel_intfs
      |> map_option #2

      val idx = Term.maxidx_of_term R + 1

      fun mk_i_of R T = 
        Const (@{const_name i_of_rel}, fastype_of R --> T)$R

      fun r @{mpat "\<langle>?Ra\<rangle>?Rf"} i = mk_intfAPP (r Ra 0) (r Rf (i+1))
        | r R i = (case get_ri R of 
            SOME I => I |> Logic.incr_indexes ([], [], idx)
          | NONE => let
              val T = replicate i @{typ interface} ---> @{typ interface}
            in 
              case R of
                Free (_,_) => mk_i_of R T
              | Var ((name,idx'),_) => Var ((name,idx+idx'+2),T)
              | _ => mk_i_of R T
            end
          )

    in
      r R 0
    |> Term_Subst.zero_var_indexes 
    end

    fun 
      list_invented_intf @{mpat "i_of_rel ?c"} = [c] 
    | list_invented_intf (f$x) =
        list_invented_intf f @ list_invented_intf x
    | list_invented_intf (Abs (_,_,t)) = list_invented_intf t
    | list_invented_intf _ = []

    fun warn_invented_intf ctxt I = case list_invented_intf I of
      [] => ()
    | l => Pretty.block [
        Pretty.str "No interfaces known for constant(s):",
        Pretty.brk 1,
        Pretty.block (Pretty.commas (map (Syntax.pretty_term ctxt) l))
      ] |> Pretty.string_of |> warning

    fun itype_of_rule ctxt thm = 
      case try (Autoref_Fix_Rel.constraint_of_thm ctxt) thm of
        NONE => NONE
      | SOME (_,(f,R)) => let
          val I = intf_of_rel ctxt R
        in
          SOME (f,I)
        end

  
    val setup = relator_intf.setup
  end
*}
setup Autoref_Relator_Interface.setup

attribute_setup autoref_rules = {*
  Scan.lift (Args.mode "overloaded")
  >> (fn overl => Thm.declaration_attribute (fn thm => fn context => let
    val context = Autoref_Rules.add_thm thm context
    val ctxt = Context.proof_of context
  in
    case Autoref_Relator_Interface.itype_of_rule ctxt thm of
      NONE => (warning "Strange autoref rule: Could not infer relator"; context)
    | SOME (c,I) => Autoref_Id_Ops.decl_derived_typing overl c I context
  end
  ))
*}

end
