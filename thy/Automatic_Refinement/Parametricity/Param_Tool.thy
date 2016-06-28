section {* Basic Parametricity Reasoning *}
theory Param_Tool
imports "Relators"
begin

  subsection {* Auxiliary Lemmas *}
  lemma tag_both: "\<lbrakk> (Let x f,Let x' f')\<in>R \<rbrakk> \<Longrightarrow> (f x,f' x')\<in>R" by simp
  lemma tag_rhs: "\<lbrakk> (c,Let x f)\<in>R \<rbrakk> \<Longrightarrow> (c,f x)\<in>R" by simp
  lemma tag_lhs: "\<lbrakk> (Let x f,a)\<in>R \<rbrakk> \<Longrightarrow> (f x,a)\<in>R" by simp

  lemma tagged_fun_relD_both: 
    "\<lbrakk> (f,f')\<in>A\<rightarrow>B; (x,x')\<in>A \<rbrakk> \<Longrightarrow> (Let x f,Let x' f')\<in>B"
    and tagged_fun_relD_rhs: "\<lbrakk> (f,f')\<in>A\<rightarrow>B; (x,x')\<in>A \<rbrakk> \<Longrightarrow> (f x,Let x' f')\<in>B"
    and tagged_fun_relD_lhs: "\<lbrakk> (f,f')\<in>A\<rightarrow>B; (x,x')\<in>A \<rbrakk> \<Longrightarrow> (Let x f,f' x')\<in>B"
    and tagged_fun_relD_none: "\<lbrakk> (f,f')\<in>A\<rightarrow>B; (x,x')\<in>A \<rbrakk> \<Longrightarrow> (f x,f' x')\<in>B"
    by (simp_all add: fun_relD)


  subsection {* ML-Setup*}

  ML {*
    signature PARAMETRICITY = sig
      type param_ruleT = {
        lhs: term,
        rhs: term,
        R: term,
        rhs_head: term,
        arity: int
      }
    
      val dest_param_term: term -> param_ruleT
      val dest_param_rule: thm -> param_ruleT
      val dest_param_goal: int -> thm -> param_ruleT

      val safe_fun_relD_tac: Proof.context -> tactic'

      val adjust_arity: int -> thm -> thm
      val adjust_arity_tac: int -> Proof.context -> tactic'
      val unlambda_tac: Proof.context -> tactic'
      val prepare_tac: Proof.context -> tactic'

      val fo_rule: thm -> thm

      (*** Basic tactics ***)
      val param_rule_tac: Proof.context -> thm -> tactic'
      val param_rules_tac: Proof.context -> thm list -> tactic'
      val asm_param_tac: Proof.context -> tactic'


      (*** Nets of parametricity rules ***)
      type param_net
      val net_empty: param_net
      val net_add: thm -> param_net -> param_net
      val net_del: thm -> param_net -> param_net
      val net_add_int: Context.generic -> thm -> param_net -> param_net
      val net_del_int: Context.generic -> thm -> param_net -> param_net
      val net_tac: param_net -> Proof.context -> tactic'
    
      (*** Default parametricity rules ***)
      val add_dflt: thm -> Context.generic -> Context.generic
      val add_dflt_attr: attribute
      val del_dflt: thm -> Context.generic -> Context.generic
      val del_dflt_attr: attribute
      val get_dflt: Proof.context -> param_net

      (** Configuration **)
      val cfg_use_asm: bool Config.T
      val cfg_single_step: bool Config.T

      (** Setup **)
      val setup: theory -> theory
    end

    structure Parametricity : PARAMETRICITY = struct
      type param_ruleT = {
        lhs: term,
        rhs: term,
        R: term,
        rhs_head: term,
        arity: int
      }

      fun dest_param_term t = 
        case 
          strip_all_body t |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop
        of 
          @{mpat "(?lhs,?rhs):?R"} => let 
            val (rhs_head,arity) = 
              case strip_comb rhs of
                (c as Const _,l) => (c,length l)
              | (c as Free _,l) => (c,length l)
              | (c as Abs _,l) => (c,length l)
              | _ => raise TERM ("dest_param_term: Head",[t])
          in 
            { lhs = lhs, rhs = rhs, R=R, rhs_head = rhs_head, arity = arity }
          end
        | t => raise TERM ("dest_param_term: Expected (_,_):_",[t])

      val dest_param_rule = dest_param_term o Thm.prop_of
      fun dest_param_goal i st = 
        if i > Thm.nprems_of st then
          raise THM ("dest_param_goal",i,[st])
        else
          dest_param_term (Logic.concl_of_goal (Thm.prop_of st) i)


      fun safe_fun_relD_tac ctxt = let
        fun t a b = fo_resolve_tac [a] ctxt THEN' resolve_tac ctxt [b]
      in
        DETERM o (
          t @{thm tag_both} @{thm tagged_fun_relD_both} ORELSE'
          t @{thm tag_rhs} @{thm tagged_fun_relD_rhs} ORELSE'
          t @{thm tag_lhs} @{thm tagged_fun_relD_lhs} ORELSE'
          resolve_tac ctxt @{thms tagged_fun_relD_none}
        )
      end

      fun adjust_arity i thm = 
        if i = 0 then thm 
        else if i<0 then funpow (~i) (fn thm => thm RS @{thm fun_relI}) thm
        else funpow i (fn thm => thm RS @{thm fun_relD}) thm

      fun NTIMES k tac = 
        if k <= 0 then K all_tac 
        else tac THEN' NTIMES (k-1) tac

      fun adjust_arity_tac n ctxt i st = 
        (if n = 0 then K all_tac
        else if n>0 then NTIMES n (DETERM o resolve_tac ctxt @{thms fun_relI})
        else NTIMES (~n) (safe_fun_relD_tac ctxt)) i st

      fun unlambda_tac ctxt i st = 
        case try (dest_param_goal i) st of
          NONE => Seq.empty
        | SOME g => let
            val n = Term.strip_abs (#rhs_head g) |> #1 |> length
          in NTIMES n (resolve_tac ctxt @{thms fun_relI}) i st end

      fun prepare_tac ctxt = 
        Subgoal.FOCUS (K (PRIMITIVE (Drule.eta_contraction_rule))) ctxt
        THEN' unlambda_tac ctxt


      fun could_param_rl rl i st = 
        if i > Thm.nprems_of st then NONE
        else (
          case (try (dest_param_goal i) st, try dest_param_term rl) of
            (SOME g, SOME r) =>
              if Term.could_unify (#rhs_head g, #rhs_head r) then
                SOME (#arity r - #arity g)
              else NONE
          | _ => NONE
        )

      fun param_rule_tac_aux ctxt rl i st = 
        case could_param_rl (Thm.prop_of rl) i st of
          SOME adj => (adjust_arity_tac adj ctxt THEN' resolve_tac ctxt [rl]) i st
        | _ => Seq.empty

      fun param_rule_tac ctxt rl = 
        prepare_tac ctxt THEN' param_rule_tac_aux ctxt rl

      fun param_rules_tac ctxt rls = 
        prepare_tac ctxt THEN' FIRST' (map (param_rule_tac_aux ctxt) rls)

      fun asm_param_tac_aux ctxt i st = 
        if i > Thm.nprems_of st then Seq.empty
        else let
          val prems = Logic.prems_of_goal (Thm.prop_of st) i |> tag_list 1
          
          fun tac (n,t) i st = case could_param_rl t i st of
            SOME adj => (adjust_arity_tac adj ctxt THEN' rprem_tac n ctxt) i st
          | NONE => Seq.empty
        in
          FIRST' (map tac prems) i st
        end

      fun asm_param_tac ctxt = prepare_tac ctxt THEN' asm_param_tac_aux ctxt
    
      type param_net = (param_ruleT * thm) Item_Net.T

      local
        val param_get_key = single o #rhs_head o #1
      in 
        val net_empty = Item_Net.init (Thm.eq_thm o apply2 #2) param_get_key
      end

      fun wrap_pr_op f context thm = case try (`dest_param_rule) thm of
        NONE => 
          let 
            val msg = "Ignoring invalid parametricity theorem: "
              ^ Thm.string_of_thm (Context.proof_of context) thm
            val _ = warning msg
          in I end
      | SOME p => f p
    
      val net_add_int = wrap_pr_op Item_Net.update 
      val net_del_int = wrap_pr_op Item_Net.remove

      val net_add = Item_Net.update o `dest_param_rule
      val net_del = Item_Net.remove o `dest_param_rule

      fun net_tac_aux net ctxt i st = 
        if i > Thm.nprems_of st then 
          Seq.empty 
        else
          let
            val g = dest_param_goal i st
            val rls = Item_Net.retrieve net (#rhs_head g)
        
            fun tac (r,thm) = 
              adjust_arity_tac (#arity r - #arity g) ctxt 
              THEN' DETERM o resolve_tac ctxt [thm]
          in 
            FIRST' (map tac rls) i st
          end

      fun net_tac net ctxt = prepare_tac ctxt THEN' net_tac_aux net ctxt

      structure dflt_rules = Generic_Data (
        type T = param_net
        val empty = net_empty
        val extend = I
        val merge = Item_Net.merge
      )
        
      fun add_dflt thm context = dflt_rules.map (net_add_int context thm) context
      fun del_dflt thm context = dflt_rules.map (net_del_int context thm) context
      val add_dflt_attr = Thm.declaration_attribute add_dflt
      val del_dflt_attr = Thm.declaration_attribute del_dflt

      val get_dflt = dflt_rules.get o Context.Proof

      val cfg_use_asm = 
        Attrib.setup_config_bool @{binding param_use_asm} (K true)
      val cfg_single_step = 
        Attrib.setup_config_bool @{binding param_single_step} (K false)

      local
        open Refine_Util

        val param_modifiers =
          [Args.add -- Args.colon >> K (Method.modifier add_dflt_attr @{here}),
           Args.del -- Args.colon >> K (Method.modifier del_dflt_attr @{here}),
           Args.$$$ "only" -- Args.colon >>
            K {init = Context.proof_map (dflt_rules.map (K net_empty)),
                attribute = add_dflt_attr, pos = @{here}}]

        val param_flags = 
           parse_bool_config "use_asm" cfg_use_asm
        || parse_bool_config "single_step" cfg_single_step

      in
          
        val parametricity_method = 
          parse_paren_lists param_flags |-- Method.sections param_modifiers >> 
          (fn _ => fn ctxt => 
            let
              val net2 = get_dflt ctxt
              val asm_tac = 
                if Config.get ctxt cfg_use_asm then 
                  asm_param_tac ctxt
                else K no_tac
   
              val RPT = 
                if Config.get ctxt cfg_single_step then I
                else REPEAT_ALL_NEW_FWD
  
            in
              SIMPLE_METHOD' (
                RPT (
                  (assume_tac ctxt 
                    ORELSE' net_tac net2 ctxt
                    ORELSE' asm_tac)
                ) 
              )
            end
          )
      end

      fun fo_rule thm = case Thm.concl_of thm of
            @{mpat "Trueprop ((_,_)\<in>_\<rightarrow>_)"} => fo_rule (thm RS @{thm fun_relD})
          | _ => thm 
          
      val param_fo_attr = Scan.succeed (Thm.rule_attribute [] (K fo_rule))

      val setup = I
        #> Attrib.setup @{binding param} 
            (Attrib.add_del add_dflt_attr del_dflt_attr)
            "declaration of parametricity theorem"
        #> Global_Theory.add_thms_dynamic (@{binding param}, 
             map #2 o Item_Net.content o dflt_rules.get)
        #> Method.setup @{binding parametricity} parametricity_method 
             "Parametricity solver"
        #> Attrib.setup @{binding param_fo} param_fo_attr 
             "Parametricity: Rule in first-order form"

    end
    *}

  setup Parametricity.setup



  subsection \<open>Convenience Tools\<close>

  ML {*
    (* Prefix p_ or wrong type supresses generation of relAPP *)
  
    fun cnv_relAPP t = let
      fun consider (Var ((name,_),T)) =
        if String.isPrefix "p_" name then false   
        else (
          case T of
            Type(@{type_name set},[Type(@{type_name prod},_)]) => true
          | _ => false)
      | consider _ = true
  
      fun strip_rcomb u : term * term list =
        let 
          fun stripc (x as (f$t, ts)) = 
            if consider t then stripc (f, t::ts) else x
          | stripc  x =  x
        in  stripc(u,[])  end;
  
      val (f,a) = strip_rcomb t
    in 
      Relators.list_relAPP a f
    end
  
    fun to_relAPP_conv ctxt = Refine_Util.f_tac_conv ctxt 
      cnv_relAPP 
      (ALLGOALS (simp_tac 
        (put_simpset HOL_basic_ss ctxt addsimps @{thms relAPP_def})))
  
  
    val to_relAPP_attr = Thm.rule_attribute [] (fn context => let
      val ctxt = Context.proof_of context
    in
      Conv.fconv_rule (Conv.arg1_conv (to_relAPP_conv ctxt))
    end)
  *}
  
  attribute_setup to_relAPP = {* Scan.succeed (to_relAPP_attr) *} 
    "Convert relator definition to prefix-form"


end
