section {* Anti-Unification *}
theory Anti_Unification
imports Refine_Util
begin
  text {* We implement a simple anti-unification.
    Currently, we do not handle lambdas, nor sorts, and avoid
    higher-order variables, i.e.,
    f x and g x will be unified to ?v, not ?v x, and existing higher-order
    patterns will be collapsed, e.g.: ?f x and ?f x will become ?v.
    *}

ML {*
  signature ANTI_UNIFICATION = sig
    type typ_env
    type term_env
    type env = typ_env * term_env

    val empty_typ: typ_env
    val empty_term: term_env
    val empty: env

    val anti_unifyT: typ * typ -> typ_env -> typ * typ_env
    val anti_unify_env: term * term -> env -> term * env
    val anti_unify: term * term -> term
    val anti_unify_list: term list -> term

    val specialize_tac: Proof.context -> thm list -> tactic'
    val specialize_net_tac: Proof.context -> (int * thm) Net.net -> tactic'
  end


  structure Anti_Unification :ANTI_UNIFICATION = struct
    structure Term2tab = Table (
      type key = term * term
      val ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord
    );

    structure Typ2tab = Table (
      type key = typ * typ
      val ord = prod_ord Term_Ord.typ_ord Term_Ord.typ_ord
    );

    type typ_env = (typ Typ2tab.table * int)
    type term_env = (term Term2tab.table * int)
    type env = typ_env * term_env

    val empty_typ = (Typ2tab.empty,0)
    val empty_term = (Term2tab.empty,0)
    val empty = (empty_typ,empty_term)

    fun tvar_pair p (vtab,idx) =
      case Typ2tab.lookup vtab p of
        NONE => let
          val tv = TVar (("T",idx),[])
          val vtab = Typ2tab.update (p,tv) vtab
        in
          (tv,(vtab,idx+1))
        end
      | SOME tv => (tv,(vtab,idx))

    fun anti_unifyT (TFree v1, TFree v2) dt =
        if v1 = v2 then (TFree v1,dt)
        else tvar_pair (TFree v1, TFree v2) dt
      | anti_unifyT (p as (Type (n1,l1), Type (n2,l2))) dt =
        if n1 = n2 andalso (length l1 = length l2) then
          let
            val (l,dt) = fold_map anti_unifyT (l1~~l2) dt
          in (Type (n1,l),dt) end
        else
          tvar_pair p dt
      | anti_unifyT p dt = tvar_pair p dt

    fun var_pair p (tdt,(vtab,idx)) =
      case Term2tab.lookup vtab p of
        NONE => let
          val (T,tdt) = anti_unifyT (apply2 fastype_of p) tdt
          val v = Var (("v",idx),T)
          val vtab = Term2tab.update (p,v) vtab
        in
          (v,(tdt,(vtab,idx+1)))
        end
      | SOME v => (v,(tdt,(vtab,idx)))

    fun anti_unify_env (p as (Free (n1,T1), Free (n2,T2))) (tdt,dt) =
        if n1 = n2 then
          let
            val (T,tdt) = anti_unifyT (T1,T2) tdt
          in (Free (n1,T),(tdt,dt)) end
        else
          var_pair p (tdt,dt)
      | anti_unify_env (p as (Const (n1,T1), Const (n2,T2))) (tdt,dt) =
        if n1 = n2 then
          let
            val (T,tdt) = anti_unifyT (T1,T2) tdt
          in (Const (n1,T),(tdt,dt)) end
        else
          var_pair p (tdt,dt)
      | anti_unify_env (p as (f1$x1,f2$x2)) dtp =
        let
          val (f,dtp) = anti_unify_env (f1,f2) dtp
        in
          if is_Var f then
            var_pair p dtp
          else let
            val (x,dtp) = anti_unify_env (x1,x2) dtp
          in (f$x,dtp) end
        end
      | anti_unify_env p dtp = var_pair p dtp

    fun anti_unify p = anti_unify_env p empty |> #1

    fun anti_unify_list l = let
      fun f [] _ = raise TERM ("anti_unify_list: Empty",[])
        | f [t] dt = (t,dt)
        | f (t1::t2::ts) dt = let
            val (t,dt) = anti_unify_env (t1,t2) dt
          in f (t::ts) dt end
    in
      f l empty |> #1
    end

    local
      fun specialize_aux_tac ctxt get_candidates i st = let
        val maxidx = Thm.maxidx_of st
        val concl = Logic.concl_of_goal (Thm.prop_of st) i
        val pre_candidates = get_candidates concl
          |> map (fn thm =>
               let
                 val tidx = Thm.maxidx_of thm
                 val t = Thm.incr_indexes (maxidx + 1) thm |> Thm.concl_of
               in (maxidx + tidx + 1,t) end)

        fun unifies (idx,t)
          = can (Pattern.unify (Context.Proof ctxt) (t, concl)) (Envir.empty idx)

        val candidates = filter unifies pre_candidates |> map #2
      in
        case candidates of
          [] => Seq.single st
        | _ => let
            val pattern = anti_unify_list candidates
              |> Thm.cterm_of ctxt |> Thm.trivial
          in
            resolve_tac ctxt [pattern] i st
          end
      end
    in
      fun specialize_tac ctxt thms = let
        fun get_candidates concl =
          filter (fn thm => Term.could_unify (Thm.concl_of thm, concl)) thms
      in
        specialize_aux_tac ctxt get_candidates
      end

      fun specialize_net_tac ctxt net = let
        fun get_candidates concl = Net.unify_term net concl |> map #2
      in
        specialize_aux_tac ctxt get_candidates
      end
    end



  end
*}

end
