theory Autoref_Translate
imports Autoref_Fix_Rel
begin

subsection {* Definitions *}
subsubsection {* APP and ABS Rules *}
lemma autoref_ABS: 
  "\<lbrakk> \<And>x x'. (x,x')\<in>Ra \<Longrightarrow> (c x, a x')\<in>Rr \<rbrakk> \<Longrightarrow> (c, \<lambda>'x. a x)\<in>Ra\<rightarrow>Rr"
  by auto
lemma autoref_APP:
  "\<lbrakk> (c,a)\<in>Ra\<rightarrow>Rr; (x,x')\<in>Ra \<rbrakk> \<Longrightarrow> (c$x, a $ x')\<in>Rr"
  by (auto dest: fun_relD)
(*lemma autoref_ANNOT:
  "\<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> (x,x':::R)\<in>R" by (auto simp: ANNOT_def)
*)

lemma autoref_beta: 
  assumes "(c,a x)\<in>R"
  shows "(c,(\<lambda>'x. a x)$x)\<in>R"
  using assms by auto

lemmas dflt_trans_rules = autoref_beta autoref_ABS autoref_APP

subsubsection {* Side Conditions *}
text {*
  Rules can have prefer and defer side-conditions. Prefer conditions must
  be solvable in order for the rule to apply, and defer conditions must
  hold after the rule has been applied and the recursive translations have been
  performed. Thus, prefer-conditions typically restrict on the abstract 
  expression, while defer conditions restrict the translated expression.

  In order to solve the actual side conditions, we use the 
  @{text "Tagged_Solver"}-infrastructure. The solvers are applied after 
  the @{text "PREFER"}/@{text "DEFER"} tag has been removed.
*}

text {*
  Tag to remove internal stuff from term.
  Before a prefer/defer side condition is evaluated, all terms inside these 
  tags are purged from autoref-specific annotations, i.e., operator-annotations,
  relator annotations, and tagged applications.
*}
definition [simp, autoref_tag_defs]: "REMOVE_INTERNAL x \<equiv> x" 

text {* Useful abbreviation to require some property that is not related
  to teh refinement framework *}
abbreviation "PREFER nt \<Phi> \<equiv> PREFER_tag (nt (REMOVE_INTERNAL \<Phi>))"
abbreviation "DEFER nt \<Phi> \<equiv> DEFER_tag (nt (REMOVE_INTERNAL \<Phi>))"

definition [simp]: "REMOVE_INTERNAL_EQ a b \<equiv> a=b"
lemma REMOVE_INTERNAL_EQI: "REMOVE_INTERNAL_EQ a a" by simp

lemma autoref_REMOVE_INTERNAL_EQ: 
  assumes "(c,a)\<in>R"
  assumes "REMOVE_INTERNAL_EQ c c'"
  shows "(c',a)\<in>R"
  using assms by simp

ML {*
  signature AUTOREF_TACTICALS = sig
    val is_prefer_cond: int -> thm -> bool
    val is_defer_cond: int -> thm -> bool

    val REPEAT_INTERVAL: tactic' -> itactic
    val COND'': (int -> thm -> bool) -> tactic' -> tactic' -> tactic'
    val REPEAT_ON_SUBGOAL: tactic' -> tactic'
    val IF_SOLVED: tactic' -> tactic' -> tactic' -> tactic'
  end

  structure Autoref_Tacticals :AUTOREF_TACTICALS = struct
    fun is_prefer_cond i st =
      case Logic.concl_of_goal (Thm.prop_of st) i of
        @{mpat "Trueprop (PREFER_tag _)"} => true
      | _ => false

    fun is_defer_cond i st =
      case Logic.concl_of_goal (Thm.prop_of st) i of
        @{mpat "Trueprop (DEFER_tag _)"} => true
      | _ => false

    fun REPEAT_INTERVAL tac i j st = let
      val n = Thm.nprems_of st - (j - i)
      fun r st = (
        COND 
          (has_fewer_prems n) 
          (all_tac) 
          (tac i THEN_ELSE (r,all_tac))
        ) st
    in
      r st
    end

    fun COND'' cond tac1 tac2 = IF_EXGOAL (fn i => fn st => 
      if cond i st then tac1 i st else tac2 i st
    )

    fun REPEAT_ON_SUBGOAL tac i = REPEAT_INTERVAL tac i i

    fun IF_SOLVED tac tac1 tac2 i st = let
      val n = Thm.nprems_of st
    in
      (tac i THEN COND (has_fewer_prems n) (tac1 i) (tac2 i)) st
    end
  end


  signature AUTOREF_TRANSLATE = sig
    type trans_net = (int * thm) Net.net

    val add_post_rule: thm -> Context.generic -> Context.generic
    val delete_post_rule: thm -> Context.generic -> Context.generic
    val get_post_rules: Proof.context -> thm list

    val compute_trans_net: Autoref_Fix_Rel.thm_pairs -> Proof.context
      -> trans_net

    val side_tac: Proof.context -> tactic'
    val side_dbg_tac: Proof.context -> tactic'

    val trans_step_only_tac: Proof.context -> tactic'
    val trans_dbg_step_tac: Proof.context -> tactic'
    val trans_step_tac: Proof.context -> tactic'
    val trans_tac: Proof.context -> itactic

    val trans_analyze: Proof.context -> int -> int -> thm -> bool
    val trans_pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T

    val trans_phase: Autoref_Phases.phase

    val setup: theory -> theory
  end


  structure Autoref_Translate :AUTOREF_TRANSLATE = struct
    type trans_net = (int * thm) Net.net


    (**************************)
    (*       Translation      *)
    (**************************)
    
    structure autoref_post_simps = Named_Thms ( 
      val name = @{binding autoref_post_simps}
      val description = "Refinement Framework: " ^
          "Automatic refinement post simplification rules" 
    );

    val add_post_rule = autoref_post_simps.add_thm
    val delete_post_rule = autoref_post_simps.del_thm
    val get_post_rules = autoref_post_simps.get


    fun compute_trans_net thm_pairs _ = 
      thm_pairs
      |> map #2
      |> (fn thms => thms @ @{thms dflt_trans_rules})
      |> Tactic.build_net 

    structure trans_netD = Autoref_Data (
      type T = trans_net
      fun compute ctxt = 
        compute_trans_net (Autoref_Fix_Rel.thm_pairsD_get ctxt) ctxt
      val prereq = [Autoref_Fix_Rel.thm_pairsD_init]
    )

    fun REMOVE_INTERNAL_conv ctxt = 
      Conv.top_sweep_conv (
        fn _ => fn ct => (case Thm.term_of ct of
          @{mpat "REMOVE_INTERNAL _"} => 
            Conv.rewr_conv @{thm REMOVE_INTERNAL_def}
            then_conv Autoref_Tagging.untag_conv ctxt
          | _ => Conv.no_conv) ct
      ) ctxt

    fun REMOVE_INTERNAL_tac ctxt = CONVERSION (REMOVE_INTERNAL_conv ctxt)

    fun side_tac ctxt =
      resolve_tac ctxt @{thms SIDEI}
      THEN' REMOVE_INTERNAL_tac ctxt
      THEN' Tagged_Solver.solve_tac ctxt

    fun side_dbg_tac ctxt = let
      val ctxt = Config.put Tagged_Solver.cfg_keep true ctxt
    in
      resolve_tac ctxt @{thms SIDEI}
      THEN' REMOVE_INTERNAL_tac ctxt
      THEN' TRY o Tagged_Solver.solve_tac ctxt
    end

    local
      open Autoref_Tacticals
      fun trans_rule_tac ctxt net = resolve_from_net_tac ctxt net
        THEN_ALL_NEW (TRY o match_tac ctxt [@{thm PRIO_TAGI}])

    in
      (* Do not even attempt to solve side conditions *)
      fun trans_step_only_tac ctxt = let
        val net = trans_netD.get ctxt
      in
        (
          COND'' is_defer_cond 
            (K no_tac)
            (assume_tac ctxt ORELSE' trans_rule_tac ctxt net)
        )
      end

      (* Leave unsolved side conditions *)
      fun trans_dbg_step_tac ctxt = let
        val net = trans_netD.get ctxt
        val s_tac = side_tac ctxt
      in DETERM o (
        COND'' is_defer_cond 
          (SOLVED' s_tac)
          (
            assume_tac ctxt
            ORELSE'
            (trans_rule_tac ctxt net 
              THEN_ALL_NEW_FWD 
                COND'' is_prefer_cond
                  (TRY o DETERM o SOLVED' s_tac)
                  (K all_tac)
            )
          )
        )
      end

      fun trans_step_tac ctxt = let
        val net = trans_netD.get ctxt
        val s_tac = side_tac ctxt
      in DETERM o (
        COND'' is_defer_cond 
          (SOLVED' s_tac)
          (
            assume_tac ctxt
            ORELSE'
            (trans_rule_tac ctxt net 
              THEN_ALL_NEW_FWD 
                COND'' is_prefer_cond
                  (DETERM o SOLVED' s_tac)
                  (K all_tac)
            )
          )
        )
      end

      fun trans_tac ctxt = let
        val ss = put_simpset HOL_basic_ss ctxt
          addsimps @{thms APP_def PROTECT_def ANNOT_def}
          addsimps get_post_rules ctxt
        val trans_opt_tac = 
          resolve_tac ctxt @{thms autoref_REMOVE_INTERNAL_EQ} 
          THEN' 
          IF_SOLVED (REPEAT_ON_SUBGOAL (trans_step_tac ctxt))
            (simp_tac ss THEN' resolve_tac ctxt @{thms REMOVE_INTERNAL_EQI})
            (K all_tac)
      in
        Seq.INTERVAL trans_opt_tac
      end

    end

    fun trans_analyze _ i j _ = j < i

    fun trans_pretty_failure ctxt i j st = 
      if j < i then Pretty.str "No failure"
      else let
        val goal = Logic.get_goal (Thm.prop_of st) i
        val concl = strip_all_body goal |> Logic.strip_imp_concl

        val msg = case concl of
          @{mpat "Trueprop (DEFER_tag _)"} 
            => Pretty.str "Could not solve defered side condition"
        | @{mpat "Trueprop ((_,_)\<in>_)"} 
            => Pretty.str "Could not refine subterm"
        | _ => Pretty.str "Internal: Unexpected goal"
      in 
        Pretty.block [
          msg,
          Pretty.fbrk,
          Syntax.pretty_term ctxt goal
        ]
      end

    val trans_phase = {
      init = trans_netD.init,
      tac = trans_tac,
      analyze = trans_analyze,
      pretty_failure = trans_pretty_failure
    }


    val setup = I
      #> autoref_post_simps.setup 

  end
*}

setup Autoref_Translate.setup


subsubsection {* Standard side-tactics *}

text {* Preconditions *}
definition [simp, autoref_tag_defs]: "PRECOND_tag P == P"
lemma PRECOND_tagI: "P ==> PRECOND_tag P" by simp
abbreviation "SIDE_PRECOND P == PREFER PRECOND_tag P"

declaration {*
  Tagged_Solver.declare_solver @{thms PRECOND_tagI} @{binding PRECOND} 
    "Refinement: Solve preconditions" 
    ( fn ctxt => SOLVED' (
        asm_full_simp_tac ctxt
        THEN_ALL_NEW clarsimp_tac ctxt
        THEN_ALL_NEW asm_full_simp_tac ctxt)
    )
*}

text {* Optional preconditions *}
definition [simp, autoref_tag_defs]: "PRECOND_OPT_tag P == P"
lemma PRECOND_OPT_tagI: "P ==> PRECOND_OPT_tag P" by simp
abbreviation "SIDE_PRECOND_OPT P == PREFER PRECOND_OPT_tag P"
declaration {*
  Tagged_Solver.declare_solver @{thms PRECOND_OPT_tagI} @{binding PRECOND_OPT} 
    "Refinement: Solve optional preconditions" 
    ( fn ctxt => SOLVED' (asm_full_simp_tac ctxt))
*}

end
