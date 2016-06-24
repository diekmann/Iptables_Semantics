section {* Relator Fixing *}
theory Autoref_Fix_Rel
imports Autoref_Id_Ops
begin

ML_val "2 upto 5"

subsubsection {* Priority tags *}
text {*
  Priority tags are used to influence the ordering of refinement theorems.
  A priority tag defines two numeric priorities, a major and a minor priority.
  The major priority is considered first, the minor priority last, i.e., after
  the homogenity and relator-priority criteria.
  The default value for both priorities is 0.
*}
definition PRIO_TAG :: "int \<Rightarrow> int \<Rightarrow> bool" 
  where [simp]: "PRIO_TAG ma mi \<equiv> True"
lemma PRIO_TAGI: "PRIO_TAG ma mi" by simp

abbreviation "MAJOR_PRIO_TAG i \<equiv> PRIO_TAG i 0"
abbreviation "MINOR_PRIO_TAG i \<equiv> PRIO_TAG 0 i"
abbreviation "DFLT_PRIO_TAG \<equiv> PRIO_TAG 0 0"

text {* Some standard tags *}
abbreviation "PRIO_TAG_OPTIMIZATION \<equiv> MINOR_PRIO_TAG 10"
  -- "Optimized version of an algorithm, with additional side-conditions"
abbreviation "PRIO_TAG_GEN_ALGO \<equiv> MINOR_PRIO_TAG (- 10)"
  -- "Generic algorithm, considered to be less efficient than default algorithm"


subsection {* Solving Relator Constraints *}
text {*
  In this phase, we try to instantiate the annotated relators, using
  the available refinement rules.
*}

definition CONSTRAINT :: "'a \<Rightarrow> ('c\<times>'a) set \<Rightarrow> bool" 
  where [simp]: "CONSTRAINT f R \<equiv> True"

lemma CONSTRAINTI: "CONSTRAINT f R" by auto

ML {*
  structure Autoref_Rules = Named_Thms ( 
    val name = @{binding autoref_rules_raw}
    val description = "Refinement Framework: " ^
        "Automatic refinement rules" 
  );
*}
setup Autoref_Rules.setup


text {* Generic algorithm tags have to be defined here, as we need them for
  relator fixing ! *}

definition PREFER_tag :: "bool \<Rightarrow> bool" 
  where [simp, autoref_tag_defs]: "PREFER_tag x \<equiv> x"
definition DEFER_tag :: "bool \<Rightarrow> bool" 
  where [simp, autoref_tag_defs]: "DEFER_tag x \<equiv> x"

lemma PREFER_tagI: "P \<Longrightarrow> PREFER_tag P" by simp
lemma DEFER_tagI: "P \<Longrightarrow> DEFER_tag P" by simp
lemmas SIDEI = PREFER_tagI DEFER_tagI

definition [simp, autoref_tag_defs]: "GEN_OP_tag P == P"
lemma GEN_OP_tagI: "P ==> GEN_OP_tag P" by simp
abbreviation "SIDE_GEN_OP P == PREFER_tag (GEN_OP_tag P)"
text {* Shortcut for assuming an operation in a generic algorithm lemma *}
abbreviation "GEN_OP c a R \<equiv> SIDE_GEN_OP ((c,OP a ::: R) \<in> R)"


definition TYREL :: "('a\<times>'b) set \<Rightarrow> bool" 
  where [simp]: "TYREL R \<equiv> True"
definition TYREL_DOMAIN :: "'a itself \<Rightarrow> bool" 
  where [simp]: "TYREL_DOMAIN i \<equiv> True"

lemma TYREL_RES: "\<lbrakk> TYREL_DOMAIN TYPE('a); TYREL (R::(_\<times>'a) set) \<rbrakk> \<Longrightarrow> TYREL R"
  .

lemma DOMAIN_OF_TYREL: "TYREL (R::(_\<times>'a) set) 
  \<Longrightarrow> TYREL_DOMAIN TYPE('a)" by simp

lemma TYRELI: "TYREL (R::(_\<times>'a) set)" by simp

lemma ty_REL: "TYREL (R::(_\<times>'a) set)" by simp


ML {*
  
  signature AUTOREF_FIX_REL = sig
    
    type constraint = (term * term) list * (term * term)
    type thm_pairs = (constraint option * thm) list 
    type hom_net = (int * thm) Net.net

    val thm_pairsD_init: Proof.context -> Proof.context
    val thm_pairsD_get: Proof.context -> thm_pairs

    val constraints_of_term: term -> (term * term) list
    val constraints_of_goal: int -> thm -> (term * term) list

    val mk_CONSTRAINT: term * term -> term 
    val mk_CONSTRAINT_rl: Proof.context -> constraint -> thm

    val insert_CONSTRAINTS_tac: Proof.context -> tactic'

    val constraint_of_thm: Proof.context -> thm -> constraint

    datatype prio_relpos = 
      PR_FIRST 
    | PR_LAST 
    | PR_BEFORE of string 
    | PR_AFTER of string

    val declare_prio: string -> term -> prio_relpos -> local_theory -> local_theory
    val delete_prio: string -> local_theory -> local_theory

    val print_prios: Proof.context -> unit

    val compute_hom_net: thm_pairs -> Proof.context -> hom_net

    val add_hom_rule: thm -> Context.generic -> Context.generic
    val del_hom_rule: thm -> Context.generic -> Context.generic
    val get_hom_rules: Proof.context -> thm list

    val add_tyrel_rule: thm -> Context.generic -> Context.generic
    val del_tyrel_rule: thm -> Context.generic -> Context.generic
    val get_tyrel_rules: Proof.context -> thm list


    val insert_tyrel_tac : Proof.context -> int -> int -> tactic'
    val solve_tyrel_tac : Proof.context -> tactic'
    val tyrel_tac : Proof.context -> itactic


    val internal_hom_tac: Proof.context -> itactic
    val internal_spec_tac: Proof.context -> itactic
    val internal_solve_tac: Proof.context -> itactic

    val guess_relators_tac: Proof.context -> itactic
  
    val pretty_constraint: Proof.context -> constraint -> Pretty.T
    val pretty_constraints: Proof.context -> constraint list -> Pretty.T

    val pretty_thm_pair: Proof.context -> (constraint option * thm) -> Pretty.T
    val pretty_thm_pairs: Proof.context -> thm_pairs -> Pretty.T

    val analyze: Proof.context -> int -> int -> thm -> bool
    val pretty_failure: Proof.context -> int -> int -> thm -> Pretty.T

    val try_solve_tac: Proof.context -> tactic'
    val solve_step_tac: Proof.context -> tactic'
    val phase: Autoref_Phases.phase

    val setup: theory -> theory
  end

  structure Autoref_Fix_Rel :AUTOREF_FIX_REL = struct

    type constraint = (term * term) list * (term * term)
    type thm_pairs = (constraint option * thm) list 
    type hom_net = (int * thm) Net.net


    (*********************)
    (*    Constraints    *)
    (*********************)
    local
      fun fix_loose_bvars env t = 
        if Term.is_open t then 
          let
            val frees = tag_list 0 env 
              |> map (fn (i,(n,T)) => Free (":"^string_of_int i ^ "_" ^ n,T)) 
          in
            subst_bounds (frees, t)
          end
        else t

      fun constraints env @{mpat "OP ?f ::: ?R"} = 
          ( Term.is_open R andalso raise TERM ("Loose bvar in relator",[R]);
            [(fix_loose_bvars env f,R)]
          )
        | constraints _ (Free _) = []
        | constraints _ (Bound _) = []
        | constraints env @{mpat "?f ::: _"} = constraints env f
        | constraints env @{mpat "?f$?x"} 
          = constraints env x @ constraints env f
        | constraints env @{mpat "PROTECT (\<lambda>x. PROTECT ?t)"} 
          = constraints ((x,x_T)::env) t
        | constraints _ @{mpat "PROTECT PROTECT"} = []
        | constraints _ t = raise TERM ("constraints_of_term",[t])
    in 
      val constraints_of_term = constraints [] 
    end

    fun constraints_of_goal i st =
      case Logic.concl_of_goal (Thm.prop_of st) i of
        @{mpat "Trueprop ((_,?a)\<in>_)"} => constraints_of_term a
      | _ => raise THM ("constraints_of_goal",i,[st])


    fun mk_CONSTRAINT (f,R) = let
      val fT = fastype_of f
      val RT = fastype_of R
      val res = Const (@{const_name CONSTRAINT},fT --> RT --> HOLogic.boolT)
        $f$R
    in 
      res
    end;

    (* Types of f and R must match! *)
    fun mk_CONSTRAINT_rl ctxt (ps,c) = let
      val ps = map (mk_CONSTRAINT #> HOLogic.mk_Trueprop) ps
      val c = mk_CONSTRAINT c |> HOLogic.mk_Trueprop
      val g = Logic.list_implies (ps,c)
    in
      (* FIXME use proper context *)
      Goal.prove_global (Proof_Context.theory_of ctxt) [] [] g
        (K (resolve_tac ctxt @{thms CONSTRAINTI} 1))
    end;

    (* Internal use for hom-patterns, f and R are unified *)
    fun mk_CONSTRAINT_rl_atom ctxt (f,R) = let
      val ts = map (SOME o Thm.cterm_of ctxt) [f,R]
      val idx = Term.maxidx_term f (Term.maxidx_of_term R) + 1
    in 
      infer_instantiate' ctxt ts (Thm.incr_indexes idx @{thm CONSTRAINTI})
    end;

    fun insert_CONSTRAINTS_tac ctxt i st = let
      val cs = constraints_of_goal i st 
      |> map (mk_CONSTRAINT #> HOLogic.mk_Trueprop #> Thm.cterm_of ctxt)
    in
      Refine_Util.insert_subgoals_tac cs i st
    end

    fun constraint_of_thm ctxt thm = let 
      exception NO_REL of term
      open Autoref_Tagging

      fun extract_entry t = 
        case Logic.strip_imp_concl (strip_all_body t) of
          @{mpat "Trueprop ((_,?f)\<in>_)"} => SOME (fst (strip_app f),t)
        | _ => NONE

      fun relator_of t = let
        (*val _ = tracing (Syntax.string_of_term @{context} t)*)

        val t = strip_all_body t
        val prems = Logic.strip_imp_prems t
        val concl = Logic.strip_imp_concl t
      in
        case concl of 
          @{mpat "Trueprop ((_,?t)\<in>?R)"} => let
            val (f,args) = strip_app t
          in
            case f of 
              @{mpat "OP ?f:::?rel"} => (f,rel)
            | _ => let
                val rels = map_filter extract_entry prems
                fun find_rel t = case filter (fn (t',_) => t=t') rels of
                  [(_,t)] => snd (relator_of t)
                | _ => raise NO_REL t

                val argrels = map find_rel args
                val rel = fold Relators.mk_fun_rel (rev argrels) R
              in
                (f,rel)
              end
          end
        | _ => raise THM ("constraint_of_thm: Invalid concl",~1,[thm])
      end

      val (f,rel) = relator_of (Thm.prop_of thm) 
        handle exc as (NO_REL t) => (
          warning (
            "Could not infer unique higher-order relator for "
            ^ "refinement rule: \n"
            ^ Thm.string_of_thm ctxt thm
            ^ "\n for argument: " 
            ^ Syntax.string_of_term ctxt t
          ); 
          reraise exc)

      (* Extract GEN_OP-tags *)
      fun 
        genop_cs @{mpat "Trueprop (SIDE_GEN_OP ((_,OP ?f ::: _) \<in> ?R))"} = 
          if has_Var f then NONE else SOME (f,R)
      | genop_cs _ = NONE

      val gen_ops = Thm.prems_of thm
        |> map_filter genop_cs

    in
      (gen_ops,(f,rel))
    end

    (*********************)
    (*    Priorities     *)
    (*********************)
    structure Rel_Prio_List = Prio_List (
      type item = string * term
      val eq = op = o apply2 fst 
    )

    structure Rel_Prio = Generic_Data (
      type T = Rel_Prio_List.T
      val empty = Rel_Prio_List.empty
      val merge = Rel_Prio_List.merge
      val extend = I
    )

    fun pretty_rel_prio ctxt (s,t) = Pretty.block [
      Pretty.str s, Pretty.str ":", Pretty.brk 1,
      Syntax.pretty_term ctxt t
    ]

    fun print_prios ctxt = let
      val rpl = Rel_Prio.get (Context.Proof ctxt)
    in
      (map (pretty_rel_prio ctxt) rpl)
      |> Pretty.big_list "Relator Priorities"
      |> Pretty.string_of
      |> warning
    end


    datatype prio_relpos = 
      PR_FIRST 
    | PR_LAST 
    | PR_BEFORE of string 
    | PR_AFTER of string

    fun declare_prio name pat0 relpos lthy = 
      let
        val pat1 = Proof_Context.cert_term lthy pat0
        val pat2 = singleton (Variable.export_terms (Variable.auto_fixes pat1 lthy) lthy) pat1
      in
        lthy |> Local_Theory.declaration {syntax = false, pervasive = false}
          (fn phi =>
            let val item = (name, Morphism.term phi pat2) in
              Rel_Prio.map (fn rpl =>
                case relpos of
                  PR_FIRST => Rel_Prio_List.add_first rpl item
                | PR_LAST => Rel_Prio_List.add_last rpl item
                | PR_BEFORE n => Rel_Prio_List.add_before rpl item (n,Term.dummy)
                | PR_AFTER n => Rel_Prio_List.add_after rpl item (n,Term.dummy)
              )
            end)
      end

    fun delete_prio name = Local_Theory.declaration {syntax = false, pervasive = false}
      (fn phi => Rel_Prio.map (Rel_Prio_List.delete (name, Term.dummy)))

    local
      fun relators_of R = let
        fun f @{mpat "?R1.0\<rightarrow>?R2.0"} = f R1 @ f R2
          | f R = [R]
      in
        f R |> map Refine_Util.anorm_term |> distinct op =
      end

      fun dest_prio_tag @{mpat "Trueprop (PRIO_TAG ?ma ?mi)"} = 
            apply2 (#2 o HOLogic.dest_number) (ma,mi)
        | dest_prio_tag t = raise TERM ("dest_prio_tag",[t])

      fun get_tagged_prios thm = let
        val prems = Thm.prems_of thm
        fun r [] = (0,0)
          | r (prem::prems) = (
              case try dest_prio_tag prem of
                NONE => r prems
              | SOME p => p
            ) 

      in
        r prems
      end

      fun prio_order_of ctxt (SOME (_,(_,R)),thm) = 
        let
          val rels = relators_of R
          val hom = length rels
          val (major_prio,minor_prio) = get_tagged_prios thm

          val rpl = Rel_Prio.get (Context.Proof ctxt)
          val matches = Pattern.matches (Proof_Context.theory_of ctxt)
          fun prefer ((_,p1),(_,p2)) = matches (p2,p1)
          fun prio_of R 
            = Rel_Prio_List.prio_of (fn (_,pat) => matches (pat,R)) prefer rpl 
              + 1
          val prio = fold (fn R => fn s => prio_of R + s) rels 0
        in
          (major_prio, (hom,(prio,minor_prio)))
        end
      | prio_order_of _ _ = raise Match

      val prio_order = 
        prod_ord
          (rev_order o int_ord)
          (prod_ord 
            int_ord
            (prod_ord (rev_order o int_ord) (rev_order o int_ord)))

      fun annotate_thm_pair ctxt (SOME (ps,(f,R)),thm) = 
        let
          open Autoref_Tagging  Conv

          fun warn () = warning ("Error annotating refinement theorem: "
            ^ Thm.string_of_thm ctxt thm
          )

          val R_cert = Thm.cterm_of ctxt R

          fun cnv ctxt ct = (case Thm.term_of ct of
            @{mpat "OP _ ::: _"} => all_conv
          | @{mpat "OP _"} => mk_rel_ANNOT_conv ctxt R_cert
          | @{mpat "_ $ _"} => arg1_conv (cnv ctxt)
          | _ => mk_OP_conv then_conv mk_rel_ANNOT_conv ctxt R_cert

          ) ct

          (*val _ = tracing ("ANNOT: " ^ @{make_string} thm)*)
          val thm = (fconv_rule (rhs_conv cnv ctxt)) thm
          val thm = case try (fconv_rule (rhs_conv cnv ctxt)) thm of
            NONE => (warn (); thm)
          | SOME thm => thm
          (*val _ = tracing ("RES: " ^ @{make_string} thm)*)

        in
          (SOME (ps,(f,R)),thm)
        end
      | annotate_thm_pair _ p = p

    in
      fun compute_thm_pairs ctxt = let
        val rules = Autoref_Rules.get ctxt
        fun add_o p = (prio_order_of ctxt p,p)

        val pairs = rules
          |> map (fn thm => (try (constraint_of_thm ctxt) thm,thm))
        val spairs = filter (is_some o #1) pairs
          |> map add_o 
          |> sort (prio_order o apply2 #1)
          |> map #2
        val npairs = filter (is_none o #1) pairs
      in
        spairs@npairs |> map (annotate_thm_pair ctxt)
      end
    end

    structure thm_pairsD = Autoref_Data (
      type T = thm_pairs
      val compute = compute_thm_pairs
      val prereq = []
    )

    val thm_pairsD_init = thm_pairsD.init
    val thm_pairsD_get = thm_pairsD.get

    structure hom_rules = Named_Sorted_Thms (
      val name = @{binding autoref_hom}
      val description = "Autoref: Homogenity rules"
      val sort = K I
      val transform = K (
        fn thm => case Thm.concl_of thm of 
          @{mpat "Trueprop (CONSTRAINT _ _)"} => [thm]
        | _ => raise THM ("Invalid homogenity rule",~1,[thm])
      )
    )
  
    val add_hom_rule = hom_rules.add_thm
    val del_hom_rule = hom_rules.del_thm
    val get_hom_rules = hom_rules.get

    local
      open Relators
      fun 
        repl @{mpat "?R\<rightarrow>?S"} ctab = let
          val (R,ctab) = repl R ctab
          val (S,ctab) = repl S ctab
        in (mk_fun_rel R S,ctab) end
      | repl R ctab = let
          val (args,R) = strip_relAPP R
          val (args,ctab) = fold_map repl args ctab 
          val (ctxt,tab) = ctab

          val (R,(ctxt,tab)) = case Termtab.lookup tab R of
            SOME R => (R,(ctxt,tab))
          | NONE => let
              val aT = fastype_of R |> strip_type |> #2 
                |> HOLogic.dest_setT |> HOLogic.dest_prodT |> #2
              val (cT,ctxt) = yield_singleton Variable.invent_types @{sort type} ctxt
              val cT = TFree cT
              val T = map fastype_of args ---> HOLogic.mk_setT (HOLogic.mk_prodT (cT,aT))
              val (R',ctxt) = yield_singleton Variable.variant_fixes "R" ctxt
              val R' = list_relAPP args (Free (R',T))
              val tab = Termtab.update (R,R') tab
            in (R',(ctxt,tab)) end
        in 
          (R,(ctxt,tab))   
        end

      fun hom_pat_of_rel ctxt R = let
        val (R,(ctxt',_)) = repl R (ctxt,Termtab.empty)
        val R = singleton (Variable.export_terms ctxt' ctxt) R
      in
        Refine_Util.anorm_term R
      end

    in
      fun compute_hom_net pairs ctxt = let
        val cs = map_filter #1 pairs
        val cs' = map (fn (_,(f,R)) => (f,hom_pat_of_rel ctxt R)) cs
        val thms = get_hom_rules ctxt @ map (mk_CONSTRAINT_rl_atom ctxt) cs'
        val thms = map (Thm.cprop_of #> Thm.trivial) thms
        val net = Tactic.build_net thms
      in
        net
      end
    end

    structure hom_netD = Autoref_Data (
      type T = hom_net
      fun compute ctxt = compute_hom_net (thm_pairsD.get ctxt) ctxt
      val prereq = [ thm_pairsD.init ]
    )

    structure tyrel_rules = Named_Sorted_Thms (
      val name = @{binding autoref_tyrel}
      val description = "Autoref: Type-based relator fixing rules"
      val sort = K I

      val transform = K (
        fn thm => case Thm.prop_of thm of 
          @{mpat "Trueprop (TYREL _)"} => [thm]
        | _ => raise THM ("Invalid tyrel-rule",~1,[thm])
      )
    )

    val add_tyrel_rule = tyrel_rules.add_thm
    val del_tyrel_rule = tyrel_rules.del_thm
    val get_tyrel_rules = tyrel_rules.get

    local
      (*fun rel_annots @{mpat "_ ::: ?R"} = [R]
        | rel_annots @{mpat "?f$?x"} = rel_annots f @ rel_annots x
        | rel_annots @{mpat "PROTECT (\<lambda>_. PROTECT ?t)"} = rel_annots t
        | rel_annots @{mpat "PROTECT PROTECT"} = []
        | rel_annots (Free _) = []
        | rel_annots (Bound _) = []
        | rel_annots t = raise TERM ("rel_annots",[t])
      *)

      fun add_relators t acc = let
        open Relators
        val (args,_) = strip_relAPP t
        val res = fold add_relators args acc
        val res = insert (op=) t res
      in
        res
      end
  
      fun add_relators_of_subgoal st i acc = 
        case Logic.concl_of_goal (Thm.prop_of st) i of
          @{mpat "Trueprop (CONSTRAINT _ ?R)"} => add_relators R acc
        | _ => acc
  
    in

      fun insert_tyrel_tac ctxt i j k st = let
        fun get_constraint t = let
          val T = fastype_of t
          val res = Const (@{const_name TYREL}, T --> HOLogic.boolT) $ t
        in
          res |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt
        end
        
        val relators = fold (add_relators_of_subgoal st) (i upto j) []
        val tyrels = map get_constraint relators
      in
        Refine_Util.insert_subgoals_tac tyrels k st
      end
    end

    fun solve_tyrel_tac ctxt = let
      fun mk_tac rl = resolve_tac ctxt @{thms TYREL_RES} 
        THEN' match_tac ctxt [rl RS @{thm DOMAIN_OF_TYREL}]
        THEN' resolve_tac ctxt [rl]

      val tac = FIRST' (map mk_tac (tyrel_rules.get ctxt))
    in
      DETERM o tac ORELSE' (TRY o resolve_tac ctxt @{thms TYRELI})
    end
    
    fun tyrel_tac ctxt i j =
      (insert_tyrel_tac ctxt i j
      THEN_ALL_NEW_FWD solve_tyrel_tac ctxt) i



    fun internal_hom_tac ctxt = let
      val hom_net = hom_netD.get ctxt
    in
      Seq.INTERVAL (TRY o DETERM o resolve_from_net_tac ctxt hom_net)    
    end

    fun internal_spec_tac ctxt = let
      val pairs = thm_pairsD.get ctxt
      val net = pairs
        |> map_filter (fst #> map_option (snd #> mk_CONSTRAINT_rl_atom ctxt))
        |> Tactic.build_net
    in 
      fn i => fn j => REPEAT (CHANGED 
        (Seq.INTERVAL (DETERM o Anti_Unification.specialize_net_tac ctxt net) i j)
      )
    end

    fun apply_to_constraints tac = let
      fun no_CONSTRAINT_tac i st = 
        case Logic.concl_of_goal (Thm.prop_of st) i of
          @{mpat "Trueprop (CONSTRAINT _ _)"} => Seq.empty
        | _ => Seq.single st  

    in
      Seq.INTERVAL (no_CONSTRAINT_tac ORELSE' tac)
    end

    fun internal_solve_tac ctxt = let
      val pairs = thm_pairsD.get ctxt
      val net = pairs
        |> map_filter (fst #> map_option (mk_CONSTRAINT_rl ctxt))
        |> Tactic.build_net

      val s_tac = SOLVED' (REPEAT_ALL_NEW (resolve_from_net_tac ctxt net))
    in 
      apply_to_constraints s_tac
      ORELSE_INTERVAL 
      apply_to_constraints (TRY o DETERM o s_tac)
    end

    fun guess_relators_tac ctxt = let
      val pairs = thm_pairsD.get ctxt
      val net = pairs
        |> map_filter (fst #> map_option (mk_CONSTRAINT_rl ctxt))
        |> Tactic.build_net

      val hom_net = hom_netD.get ctxt

      fun hom_tac i j = Seq.INTERVAL 
        (TRY o DETERM o resolve_from_net_tac ctxt hom_net) i j

      fun spec_tac i j = 
        REPEAT (CHANGED 
          (Seq.INTERVAL (DETERM o Anti_Unification.specialize_net_tac ctxt net) i j)
        )

      val solve_tac = let 
        val s_tac = SOLVED' (REPEAT_ALL_NEW (resolve_from_net_tac ctxt net))
      in   
        apply_to_constraints s_tac
        ORELSE_INTERVAL 
        apply_to_constraints (TRY o DETERM o s_tac)
      end
    in
      Seq.INTERVAL (insert_CONSTRAINTS_tac ctxt)
      THEN_INTERVAL hom_tac
      THEN_INTERVAL spec_tac
      THEN_INTERVAL (tyrel_tac ctxt)
      THEN_INTERVAL solve_tac
    end


    (*********************)
    (*  Pretty Printing  *)
    (*********************)

    fun pretty_constraint_atom ctxt (f,R) = Pretty.block 
      [ Syntax.pretty_term ctxt f,
        Pretty.str " :: ",
        Syntax.pretty_typ ctxt (fastype_of f),
        Pretty.str " ::: ",
        Syntax.pretty_term ctxt R]

    fun pretty_constraint ctxt (ps,(f,R)) = 
      case ps of 
        [] => pretty_constraint_atom ctxt (f,R)
      | _ => Pretty.block [
               map (pretty_constraint_atom ctxt) ps 
               |> Pretty.separate "; " 
               |> Pretty.enclose "\<lbrakk>" "\<rbrakk>",
               Pretty.brk 1, Pretty.str "\<Longrightarrow>", Pretty.brk 1,
               pretty_constraint_atom ctxt (f,R)
             ]


    fun pretty_constraints ctxt l = Pretty.big_list "Constraints" 
      (map (pretty_constraint ctxt) l)

    fun pretty_thm_pair ctxt (c,thm) = Pretty.block [
      case c of 
        NONE => Pretty.str "NONE"
      | SOME c => pretty_constraint ctxt c,
      Pretty.brk 2, Pretty.str "---", Pretty.brk 2,
      Thm.pretty_thm ctxt thm
    ]

    fun pretty_thm_pairs ctxt pairs = Pretty.big_list "Thm-Pairs"
      (map (pretty_thm_pair ctxt) pairs)

    local
      fun unifies ctxt (t1, t2) = Term.could_unify (t1, t2) andalso
        let
          val idx1 = Term.maxidx_of_term t1
          val t2 = Logic.incr_indexes ([], [], idx1 + 1) t2
          val idx2 = Term.maxidx_of_term t2
        in
          can (Pattern.unify (Context.Proof ctxt) (t1,t2)) (Envir.empty idx2)
        end

      fun analyze_possible_problems ctxt (f,R) = let

        fun strange_aux sf R = 
        ( 
          if sf then 
            let
              val T = fastype_of R
            in 
              case try (HOLogic.dest_prodT o HOLogic.dest_setT) T of
                SOME _ => []
              | NONE => [Pretty.block [
                  Pretty.str "Strange relator type, expected plain relation: ",
                  Syntax.pretty_term (Config.put show_types true ctxt) R
                ]]
            end
          else []
        ) @ ( 
          case R of
            @{mpat "\<langle>?R\<rangle>?S"} => strange_aux true R @ strange_aux false S
          | Var (_,T) => (
              case 
                try (HOLogic.dest_prodT o HOLogic.dest_setT) (#2 (strip_type T))
              of
                SOME (TFree _,_) => [Pretty.block [
                  Pretty.str "Fixed concrete type on schematic relator: ",
                  Syntax.pretty_term (Config.put show_types true ctxt) R
                ]]
              | _ => []
            )
          | _ => []
        )

        val strange = case strange_aux true R of 
          [] => NONE
        | l => SOME (Pretty.block l)

        val folded_relator = let
          fun 
            match (Type (name,args)) R = 
              let
                val (Rargs,Rhd) = Relators.strip_relAPP R
              in 
                if is_Var Rhd then []
                else if length args <> length Rargs then
                  [Pretty.block [ 
                    Pretty.str "Type/relator arity mismatch:",
                    Pretty.brk 1,
                    Pretty.block [
                      Pretty.str name, Pretty.str "/", 
                      Pretty.str (string_of_int (length args))
                    ],
                    Pretty.brk 1,Pretty.str "vs.",Pretty.brk 1,
                    Pretty.block [
                      Syntax.pretty_term ctxt Rhd, Pretty.str "/", 
                      Pretty.str (string_of_int (length Rargs))
                    ]
                  ]]
                else
                  args ~~ Rargs |> map (uncurry match) |> flat

              end
          | match _ _ = []   

        in 
          case match (fastype_of f) R of
            [] => NONE 
          | l => SOME (Pretty.block (Pretty.fbreaks l @ [Pretty.fbrk,
              Pretty.str ("Explanation: This may be due to using polymorphic "
              ^ "relators like Id on non-terminal types." 
              ^ "A problem usually occurs when "
              ^ "this relator has to be matched against a fully unfolded one."
              ^ "This warning is also issued on partially parametric relators "
              ^ "like br. However, the refinement rules are usually set up to "
              ^ "compensate for this, so this is probably not the cause for an "
              ^ "unsolved constraint")
            ]))
        end


        val issues = [strange, folded_relator]
          |> map_filter I
      in
        case issues of
          [] => NONE
        | l => SOME (Pretty.big_list "Possible problems" l)

      end

      fun pretty_try_candidates ctxt i st = if i > Thm.nprems_of st then
        Pretty.str "Goal number out of range"
      else
        case Logic.concl_of_goal (Thm.prop_of st) i of
          @{mpat "Trueprop (CONSTRAINT ?f ?R)"} =>
            let
              val pairs = thm_pairsD.get ctxt
              val st = Drule.zero_var_indexes st

              val pt_hd = Pretty.block [
                Pretty.str "Head: ", Pretty.fbrk,
                pretty_constraint_atom ctxt (f,R)
              ]

              fun isc (SOME (ps,(fp,R)),_) = 
                    if unifies ctxt (f,fp) then SOME (ps,(fp,R)) else NONE
                | isc _ = NONE

              val candidates = pairs |> map_filter isc

              fun try_c c = let
                val pt1 = Pretty.block [
                  Pretty.str "Trying ",
                  pretty_constraint ctxt c
                ]

                val rl = mk_CONSTRAINT_rl ctxt c 
                   |> Drule.zero_var_indexes
                val res = (SOLVED' (resolve_tac ctxt [rl])) i st
                  |> Seq.pull |> is_some

                val pt2 = (if res then Pretty.str "OK" else Pretty.str "ERR")
                  
              in
                Pretty.block [pt1,Pretty.fbrk,pt2]
              end

              val res = Pretty.block (
                Pretty.fbreaks [pt_hd,
                  Pretty.big_list "Solving Attempts" 
                    (map try_c candidates)]
              )

            in 
              res
            end
        | _ => Pretty.str "Unexpected goal format"


      exception ERR of Pretty.T
      fun analyze' ctxt i j st = let
        val As = Logic.strip_horn (Thm.prop_of st) |> #1 
          |> drop (i-1) |> take (j-i+1)
          |> map (strip_all_body #> Logic.strip_imp_concl)
        val Cs = map_filter (
            fn @{mpat "Trueprop (CONSTRAINT ?f ?R)"} => SOME (f,R)
             | @{mpat "Trueprop ((_,_)\<in>_)"} => NONE
             | t => raise ERR (Pretty.block [
                 Pretty.str "Internal: Unexpected goal format: ",
                 Syntax.pretty_term ctxt t
               ])
          ) As

        val Cs_problems = map (fn c => 
          case analyze_possible_problems ctxt c of
            NONE => pretty_constraint_atom ctxt c
          | SOME p => Pretty.block [pretty_constraint_atom ctxt c,Pretty.fbrk,p]
        ) Cs
 
        val Cs_pretty = Pretty.big_list "Constraints" Cs_problems
      in
        case Cs of [] => ()
        | _ => raise ERR (Pretty.block [
            Pretty.str 
              "Could not infer all relators, some constraints remaining",
            Pretty.fbrk,
            Cs_pretty,
            Pretty.fbrk,
            Pretty.block [
              Pretty.str "Trying to solve first constraint",
              Pretty.fbrk,
              pretty_try_candidates ctxt i st
            ]
          ])
      end

    in
      fun analyze ctxt i j st = can (analyze' ctxt i j) st

      fun pretty_failure ctxt i j st = 
        (analyze' ctxt i j st; Pretty.str "No failure") handle ERR p => p

      fun try_solve_tac ctxt i st =  
        if i > Thm.nprems_of st then
          (tracing "Goal number out of range"; Seq.empty)
        else
          case Logic.concl_of_goal (Thm.prop_of st) i of
            @{mpat "Trueprop (CONSTRAINT ?f ?R)"} =>
              let
                val pairs = thm_pairsD.get ctxt
                val st = Drule.zero_var_indexes st

                val pt = Pretty.block [
                  Pretty.str "Head: ", Pretty.fbrk,
                  pretty_constraint_atom ctxt (f,R)
                ]
                val _ = tracing (Pretty.string_of pt)

                val _ = case analyze_possible_problems ctxt (f,R) of
                  NONE => ()
                | SOME p => tracing (Pretty.string_of p)
            
                fun isc (SOME (ps,(fp,R)),_) = 
                      if unifies ctxt (f,fp) then SOME (ps,(fp,R)) else NONE
                  | isc _ = NONE

                val net = pairs
                  |> map_filter (fst #> map_option (mk_CONSTRAINT_rl ctxt))
                  |> Tactic.build_net


                val candidates = pairs |> map_filter isc

                fun try_c c = let
                  val _ = Pretty.block [
                    Pretty.str "Trying ",
                    pretty_constraint ctxt c
                  ] |> Pretty.string_of |> tracing

                  val rl = mk_CONSTRAINT_rl ctxt c 
                     |> Drule.zero_var_indexes
                  val res = (SOLVED' (resolve_tac ctxt [rl] 
                      THEN_ALL_NEW (REPEAT_ALL_NEW (resolve_from_net_tac ctxt net)))
                    ) i st
                    |> Seq.pull |> is_some

                  val _ = (if res then Pretty.str "OK" else Pretty.str "ERR")
                    |> Pretty.string_of |> tracing
                in
                  ()
                end

                val _ = map try_c candidates
              in 
                Seq.single st
              end

          | _ => Seq.empty


    end


    fun solve_step_tac ctxt = let
      val pairs = thm_pairsD.get ctxt
      val net = pairs
        |> map_filter (fst #> map_option (mk_CONSTRAINT_rl ctxt))
        |> Tactic.build_net
    in 
      resolve_from_net_tac ctxt net
    end

    val phase = {
      init = thm_pairsD.init #> hom_netD.init,
      tac = guess_relators_tac,
      analyze = analyze,
      pretty_failure = pretty_failure
    }


    val setup = hom_rules.setup #> tyrel_rules.setup
  end

*}

setup Autoref_Fix_Rel.setup

end
