section {* Relators *}
theory Relators
imports "../Lib/Refine_Lib"
begin

text {*
  We define the concept of relators. The relation between a concrete type and
  an abstract type is expressed by a relation of type @{text "('c\<times>'a) set"}.
  For each composed type, say @{text "'a list"}, we can define a {\em relator},
  that takes as argument a relation for the element type, and returns a relation
  for the list type. For most datatypes, there exists a {\em natural relator}.
  For algebraic datatypes, this is the relator that preserves the structure
  of the datatype, and changes the components. For example, 
  @{text "list_rel::('c\<times>'a) set \<Rightarrow> ('c list\<times>'a list) set"} is the natural 
  relator for lists. 

  However, relators can also be used to change the representation, and thus 
  relate an implementation with an abstract type. For example, the relator
  @{text "list_set_rel::('c\<times>'a) set \<Rightarrow> ('c list\<times>'a set) set"} relates lists
  with the set of their elements.

  In this theory, we define some basic notions for relators, and
  then define natural relators for all HOL-types, including the function type.
  For each relator, we also show a single-valuedness property, and initialize a
  solver for single-valued properties.
*}

subsection {* Basic Definitions *}

text {*
  For smoother handling of relator unification, we require relator arguments to
  be applied by a special operator, such that we avoid higher-order 
  unification problems. We try to set up some syntax to make this more 
  transparent, and give relators a type-like prefix-syntax.
*}

definition relAPP 
  :: "(('c1\<times>'a1) set \<Rightarrow> _) \<Rightarrow> ('c1\<times>'a1) set \<Rightarrow> _" 
  where "relAPP f x \<equiv> f x"

syntax "_rel_APP" :: "args \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>_" [0,900] 900)

translations
  "\<langle>x,xs\<rangle>R" == "\<langle>xs\<rangle>(CONST relAPP R x)"
  "\<langle>x\<rangle>R" == "CONST relAPP R x"


ML {*
  structure Refine_Relators_Thms = struct
    structure rel_comb_def_rules = Named_Thms ( 
      val name = @{binding refine_rel_defs}
      val description = "Refinement Framework: " ^
          "Relator definitions" 
    );
  end
*}

setup Refine_Relators_Thms.rel_comb_def_rules.setup

subsection {* Basic HOL Relators *}
subsubsection {* Function *}
definition fun_rel where 
  fun_rel_def_internal: "fun_rel A B \<equiv> { (f,f'). \<forall>(a,a')\<in>A. (f a, f' a')\<in>B }"
abbreviation fun_rel_syn (infixr "\<rightarrow>" 60) where "A\<rightarrow>B \<equiv> \<langle>A,B\<rangle>fun_rel"

lemma fun_rel_def[refine_rel_defs]: 
  "A\<rightarrow>B \<equiv> { (f,f'). \<forall>(a,a')\<in>A. (f a, f' a')\<in>B }"
  by (simp add: relAPP_def fun_rel_def_internal)

lemma fun_relI[intro!]: "\<lbrakk>\<And>a a'. (a,a')\<in>A \<Longrightarrow> (f a,f' a')\<in>B\<rbrakk> \<Longrightarrow> (f,f')\<in>A\<rightarrow>B"
  by (auto simp: fun_rel_def)

lemma fun_relD: 
  shows " ((f,f')\<in>(A\<rightarrow>B)) \<Longrightarrow> 
  (\<And>x x'. \<lbrakk> (x,x')\<in>A \<rbrakk> \<Longrightarrow> (f x, f' x')\<in>B)"
  apply rule
  by (auto simp: fun_rel_def)

lemma fun_relD1:
  assumes "(f,f')\<in>Ra\<rightarrow>Rr"
  assumes "f x = r"
  shows "\<forall>x'. (x,x')\<in>Ra \<longrightarrow> (r,f' x')\<in>Rr"
  using assms by (auto simp: fun_rel_def)

lemma fun_relD2:
  assumes "(f,f')\<in>Ra\<rightarrow>Rr"
  assumes "f' x' = r'"
  shows "\<forall>x. (x,x')\<in>Ra \<longrightarrow> (f x,r')\<in>Rr"
  using assms by (auto simp: fun_rel_def)

lemma fun_relE1:
  assumes "(f,f')\<in>Id \<rightarrow> Rv"
  assumes "t' = f' x"
  shows "(f x,t')\<in>Rv" using assms
  by (auto elim: fun_relD)

lemma fun_relE2:
  assumes "(f,f')\<in>Id \<rightarrow> Rv"
  assumes "t = f x"
  shows "(t,f' x)\<in>Rv" using assms
  by (auto elim: fun_relD)

subsubsection {* Terminal Types *}
abbreviation unit_rel :: "(unit\<times>unit) set" where "unit_rel == Id"

abbreviation "nat_rel \<equiv> Id::(nat\<times>_) set"
abbreviation "int_rel \<equiv> Id::(int\<times>_) set"
abbreviation "bool_rel \<equiv> Id::(bool\<times>_) set"

subsubsection {* Product *}
definition prod_rel where
  prod_rel_def_internal: "prod_rel R1 R2 
    \<equiv> { ((a,b),(a',b')) . (a,a')\<in>R1 \<and> (b,b')\<in>R2 }"

abbreviation prod_rel_syn (infixr "\<times>\<^sub>r" 70) where "a\<times>\<^sub>rb \<equiv> \<langle>a,b\<rangle>prod_rel" 

lemma prod_rel_def[refine_rel_defs]: 
  "(\<langle>R1,R2\<rangle>prod_rel) \<equiv> { ((a,b),(a',b')) . (a,a')\<in>R1 \<and> (b,b')\<in>R2 }"
  by (simp add: prod_rel_def_internal relAPP_def)

lemma prod_relI: "\<lbrakk>(a,a')\<in>R1; (b,b')\<in>R2\<rbrakk> \<Longrightarrow> ((a,b),(a',b'))\<in>\<langle>R1,R2\<rangle>prod_rel"
  by (auto simp: prod_rel_def)
lemma prod_relE: 
  assumes "(p,p')\<in>\<langle>R1,R2\<rangle>prod_rel"
  obtains a b a' b' where "p=(a,b)" and "p'=(a',b')" 
  and "(a,a')\<in>R1" and "(b,b')\<in>R2"
  using assms
  by (auto simp: prod_rel_def)

lemma prod_rel_simp[simp]: 
  "((a,b),(a',b'))\<in>\<langle>R1,R2\<rangle>prod_rel \<longleftrightarrow> (a,a')\<in>R1 \<and> (b,b')\<in>R2"
  by (auto intro: prod_relI elim: prod_relE)

subsubsection {*Option*}
definition option_rel where
  option_rel_def_internal:
  "option_rel R \<equiv> { (Some a,Some a') | a a'. (a,a')\<in>R } \<union> {(None,None)}"

lemma option_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>option_rel \<equiv> { (Some a,Some a') | a a'. (a,a')\<in>R } \<union> {(None,None)}"
  by (simp add: option_rel_def_internal relAPP_def)

lemma option_relI:
  "(None,None)\<in>\<langle>R\<rangle> option_rel"
  "\<lbrakk> (a,a')\<in>R \<rbrakk> \<Longrightarrow> (Some a, Some a')\<in>\<langle>R\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma option_relE:
  assumes "(x,x')\<in>\<langle>R\<rangle>option_rel"
  obtains "x=None" and "x'=None"
  | a a' where "x=Some a" and "x'=Some a'" and "(a,a')\<in>R"
  using assms by (auto simp: option_rel_def)

lemma option_rel_simp[simp]:
  "(None,a)\<in>\<langle>R\<rangle>option_rel \<longleftrightarrow> a=None"
  "(c,None)\<in>\<langle>R\<rangle>option_rel \<longleftrightarrow> c=None"
  "(Some x,Some y)\<in>\<langle>R\<rangle>option_rel \<longleftrightarrow> (x,y)\<in>R"
  by (auto intro: option_relI elim: option_relE)


subsubsection {* Sum *}
definition sum_rel where sum_rel_def_internal: 
  "sum_rel Rl Rr 
   \<equiv> { (Inl a, Inl a') | a a'. (a,a')\<in>Rl } \<union>
     { (Inr a, Inr a') | a a'. (a,a')\<in>Rr }"

lemma sum_rel_def[refine_rel_defs]: 
  "\<langle>Rl,Rr\<rangle>sum_rel \<equiv> 
     { (Inl a, Inl a') | a a'. (a,a')\<in>Rl } \<union>
     { (Inr a, Inr a') | a a'. (a,a')\<in>Rr }"
  by (simp add: sum_rel_def_internal relAPP_def)

lemma sum_rel_simp[simp]:
  "\<And>a a'. (Inl a, Inl a') \<in> \<langle>Rl,Rr\<rangle>sum_rel \<longleftrightarrow> (a,a')\<in>Rl"
  "\<And>a a'. (Inr a, Inr a') \<in> \<langle>Rl,Rr\<rangle>sum_rel \<longleftrightarrow> (a,a')\<in>Rr"
  "\<And>a a'. (Inl a, Inr a') \<notin> \<langle>Rl,Rr\<rangle>sum_rel"
  "\<And>a a'. (Inr a, Inl a') \<notin> \<langle>Rl,Rr\<rangle>sum_rel"
  unfolding sum_rel_def by auto

lemma sum_relI: 
  "(a,a')\<in>Rl \<Longrightarrow> (Inl a, Inl a') \<in> \<langle>Rl,Rr\<rangle>sum_rel"
  "(a,a')\<in>Rr \<Longrightarrow> (Inr a, Inr a') \<in> \<langle>Rl,Rr\<rangle>sum_rel"
  by simp_all
  
lemma sum_relE:
  assumes "(x,x')\<in>\<langle>Rl,Rr\<rangle>sum_rel"
  obtains 
    l l' where "x=Inl l" and "x'=Inl l'" and "(l,l')\<in>Rl"
  | r r' where "x=Inr r" and "x'=Inr r'" and "(r,r')\<in>Rr"
  using assms by (auto simp: sum_rel_def)


subsubsection {* Lists *}
definition list_rel where list_rel_def_internal:
  "list_rel R \<equiv> {(l,l'). list_all2 (\<lambda>x x'. (x,x')\<in>R) l l'}"

lemma list_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>list_rel \<equiv> {(l,l'). list_all2 (\<lambda>x x'. (x,x')\<in>R) l l'}"
  by (simp add: list_rel_def_internal relAPP_def)

lemma list_rel_induct[induct set,consumes 1, case_names Nil Cons]:
  assumes "(l,l')\<in>\<langle>R\<rangle> list_rel"
  assumes "P [] []"
  assumes "\<And>x x' l l'. \<lbrakk> (x,x')\<in>R; (l,l')\<in>\<langle>R\<rangle>list_rel; P l l' \<rbrakk> 
    \<Longrightarrow> P (x#l) (x'#l')"
  shows "P l l'"
  using assms unfolding list_rel_def
  apply simp
  by (rule list_all2_induct)

lemma list_rel_eq_listrel: "list_rel = listrel"
  apply (rule ext)
  apply safe
proof goal_cases
  case (1 x a b) thus ?case
    unfolding list_rel_def_internal
    apply simp
    apply (induct a b rule: list_all2_induct)
    apply (auto intro: listrel.intros)
    done
next
  case 2 thus ?case
    apply (induct)
    apply (auto simp: list_rel_def_internal)
    done
qed

lemma list_relI: 
  "([],[])\<in>\<langle>R\<rangle>list_rel"
  "\<lbrakk> (x,x')\<in>R; (l,l')\<in>\<langle>R\<rangle>list_rel \<rbrakk> \<Longrightarrow> (x#l,x'#l')\<in>\<langle>R\<rangle>list_rel"
  by (auto simp: list_rel_def)

lemma list_rel_simp[simp]:
  "([],l')\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> l'=[]"
  "(l,[])\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> l=[]"
  "([],[])\<in>\<langle>R\<rangle>list_rel"
  "(x#l,x'#l')\<in>\<langle>R\<rangle>list_rel \<longleftrightarrow> (x,x')\<in>R \<and> (l,l')\<in>\<langle>R\<rangle>list_rel"
  by (auto simp: list_rel_def)

lemma list_relE1:
  assumes "(l,[])\<in>\<langle>R\<rangle>list_rel" obtains "l=[]" using assms by auto

lemma list_relE2:
  assumes "([],l)\<in>\<langle>R\<rangle>list_rel" obtains "l=[]" using assms by auto

lemma list_relE3:
  assumes "(x#xs,l')\<in>\<langle>R\<rangle>list_rel" obtains x' xs' where 
  "l'=x'#xs'" and "(x,x')\<in>R" and "(xs,xs')\<in>\<langle>R\<rangle>list_rel"
  using assms 
  apply (cases l')
  apply auto
  done

lemma list_relE4:
  assumes "(l,x'#xs')\<in>\<langle>R\<rangle>list_rel" obtains x xs where 
  "l=x#xs" and "(x,x')\<in>R" and "(xs,xs')\<in>\<langle>R\<rangle>list_rel"
  using assms 
  apply (cases l)
  apply auto
  done

lemmas list_relE = list_relE1 list_relE2 list_relE3 list_relE4

lemma list_rel_imp_same_length: 
    "(l, l') \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> length l = length l'"
  unfolding list_rel_eq_listrel relAPP_def
  by (rule listrel_eq_len)

subsubsection {* Sets *}
text {* Pointwise refinement: The abstract set is the image of
  the concrete set, and the concrete set only contains elements that
  have an abstract counterpart *}
definition set_rel where set_rel_def_internal: 
  "set_rel R \<equiv> {(S,S'). S'=R``S \<and> S\<subseteq>Domain R}"

lemma set_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>set_rel \<equiv> {(S,S'). S'=R``S \<and> S\<subseteq>Domain R}"
  by (simp add: set_rel_def_internal relAPP_def)

lemma set_rel_simp[simp]: 
  "({},{})\<in>\<langle>R\<rangle>set_rel" 
  by (auto simp: set_rel_def)

lemma set_relD: "(s,s')\<in>\<langle>R\<rangle>set_rel \<Longrightarrow> x\<in>s \<Longrightarrow> \<exists>x'\<in>s'. (x,x')\<in>R"
  unfolding set_rel_def by blast

lemma set_relE[consumes 2]: 
  assumes "(s,s')\<in>\<langle>R\<rangle>set_rel" "x\<in>s"
  obtains x' where "x'\<in>s'" "(x,x')\<in>R"
  using set_relD[OF assms] ..

subsection {* Automation *} 
subsubsection {* A solver for relator properties *}
lemma relprop_triggers: 
  "\<And>R. single_valued R \<Longrightarrow> single_valued R" 
  "\<And>R. R=Id \<Longrightarrow> R=Id"
  "\<And>R. R=Id \<Longrightarrow> Id=R"
  "\<And>R. Range R = UNIV \<Longrightarrow> Range R = UNIV"
  "\<And>R. Range R = UNIV \<Longrightarrow> UNIV = Range R"
  "\<And>R R'. R\<subseteq>R' \<Longrightarrow> R\<subseteq>R'"
  by auto

ML {*
  structure relator_props = Named_Thms (
    val name = @{binding relator_props}
    val description = "Additional relator properties"
  )

  structure solve_relator_props = Named_Thms (
    val name = @{binding solve_relator_props}
    val description = "Relator properties that solve goal"
  )

*}
setup relator_props.setup
setup solve_relator_props.setup

declaration {*
  Tagged_Solver.declare_solver 
    @{thms relprop_triggers} 
    @{binding relator_props_solver}
    "Additional relator properties solver"
    (fn ctxt => (REPEAT_ALL_NEW (CHANGED o (
      match_tac ctxt (solve_relator_props.get ctxt) ORELSE'
      match_tac ctxt (relator_props.get ctxt)
    ))))
*}

declaration {*
  Tagged_Solver.declare_solver 
    []
    @{binding force_relator_props_solver}
    "Additional relator properties solver (instantiate schematics)"
    (fn ctxt => (REPEAT_ALL_NEW (CHANGED o (
      resolve_tac ctxt (solve_relator_props.get ctxt) ORELSE'
      match_tac ctxt (relator_props.get ctxt)
    ))))
*}

lemma 
  relprop_id_orient[relator_props]: "R=Id \<Longrightarrow> Id=R" and
  relprop_eq_refl[solve_relator_props]: "t = t"
  by auto

lemma 
  relprop_UNIV_orient[relator_props]: "R=UNIV \<Longrightarrow> UNIV=R"
  by auto

subsubsection {* ML-Level utilities *}

ML {*
  signature RELATORS = sig
    val mk_relT: typ * typ -> typ
    val dest_relT: typ -> typ * typ

    val mk_relAPP: term -> term -> term
    val list_relAPP: term list -> term -> term
    val strip_relAPP: term -> term list * term 

    val declare_natural_relator: 
      (string*string) -> Context.generic -> Context.generic
    val remove_natural_relator: string -> Context.generic -> Context.generic
    val natural_relator_of: Proof.context -> string -> string option

    val mk_natural_relator: Proof.context -> term list -> string -> term option
    val mk_fun_rel: term -> term -> term

    val setup: theory -> theory
  end

  structure Relators :RELATORS = struct
    val mk_relT = HOLogic.mk_prodT #> HOLogic.mk_setT

    fun dest_relT (Type (@{type_name set},[Type (@{type_name prod},[cT,aT])])) 
      = (cT,aT)
      | dest_relT ty = raise TYPE ("dest_relT",[ty],[])

    fun mk_relAPP x f = let
      val xT = fastype_of x
      val fT = fastype_of f
      val rT = range_type fT
    in 
      Const (@{const_name relAPP},fT-->xT-->rT)$f$x
    end

    val list_relAPP = fold mk_relAPP

    fun strip_relAPP R = let
      fun aux @{mpat "\<langle>?R\<rangle>?S"} l = aux S (R::l)
        | aux R l = (l,R)
    in aux R [] end

    structure natural_relators = Generic_Data (
      type T = string Symtab.table
      val empty = Symtab.empty
      val extend = I
      val merge = Symtab.join (fn _ => fn (_,cn) => cn)
    )

    fun declare_natural_relator tcp =
      natural_relators.map (Symtab.update tcp)

    fun remove_natural_relator tname =
      natural_relators.map (Symtab.delete_safe tname)

    fun natural_relator_of ctxt =
      Symtab.lookup (natural_relators.get (Context.Proof ctxt))

    (* [R1,\<dots>,Rn] T is mapped to \<langle>R1,\<dots>,Rn\<rangle> Trel *)
    fun mk_natural_relator ctxt args Tname = 
      case natural_relator_of ctxt Tname of
        NONE => NONE
      | SOME Cname => SOME let
          val argsT = map fastype_of args
          val (cTs, aTs) = map dest_relT argsT |> split_list
          val aT = Type (Tname,aTs)
          val cT = Type (Tname,cTs)
          val rT = mk_relT (cT,aT)
        in
          list_relAPP args (Const (Cname,argsT--->rT))
        end

    fun 
      natural_relator_from_term (t as Const (name,T)) = let
        fun err msg = raise TERM (msg,[t])
  
        val (argTs,bodyT) = strip_type T
        val (conTs,absTs) = argTs |> map (HOLogic.dest_setT #> HOLogic.dest_prodT) |> split_list
        val (bconT,babsT) = bodyT |> HOLogic.dest_setT |> HOLogic.dest_prodT
        val (Tcon,bconTs) = dest_Type bconT
        val (Tcon',babsTs) = dest_Type babsT
  
        val _ = Tcon = Tcon' orelse err "Type constructors do not match"
        val _ = conTs = bconTs orelse err "Concrete types do not match"
        val _ = absTs = babsTs orelse err "Abstract types do not match"

      in 
        (Tcon,name)
      end
    | natural_relator_from_term t = 
        raise TERM ("Expected constant",[t]) (* TODO: Localize this! *)

    local
      fun decl_natrel_aux t context = let
        fun warn msg = let
          val tP = 
            Context.cases Syntax.pretty_term_global Syntax.pretty_term 
              context t
          val m = Pretty.block [
            Pretty.str "Ignoring invalid natural_relator declaration:",
            Pretty.brk 1,
            Pretty.str msg,
            Pretty.brk 1,
            tP
          ] |> Pretty.string_of
          val _ = warning m
        in context end 
      in
        declare_natural_relator (natural_relator_from_term t) context
        handle 
          TERM (msg,_) => warn msg
        | exn => if Exn.is_interrupt exn then reraise exn else warn ""
      end
    in
      val natural_relator_attr = Scan.repeat1 Args.term >> (fn ts => 
        Thm.declaration_attribute ( fn _ => fold decl_natrel_aux ts)
      )
    end
  
    fun mk_fun_rel r1 r2 = let
      val (r1T,r2T) = (fastype_of r1,fastype_of r2)
      val (c1T,a1T) = dest_relT r1T
      val (c2T,a2T) = dest_relT r2T
      val (cT,aT) = (c1T --> c2T, a1T --> a2T)
      val rT = mk_relT (cT,aT)
    in 
      list_relAPP [r1,r2] (Const (@{const_name fun_rel},r1T-->r2T-->rT))
    end

    val setup = I
      #> Attrib.setup 
        @{binding natural_relator} natural_relator_attr "Declare natural relator"

  end
*}

setup Relators.setup

subsection {* Setup *}
subsubsection "Natural Relators"

declare [[natural_relator 
  unit_rel int_rel nat_rel bool_rel
  fun_rel prod_rel option_rel sum_rel list_rel
  ]]

(*declaration {* let open Relators in 
  fn _ =>
     declare_natural_relator (@{type_name unit},@{const_name unit_rel})
  #> declare_natural_relator (@{type_name fun},@{const_name fun_rel})
  #> declare_natural_relator (@{type_name prod},@{const_name prod_rel})
  #> declare_natural_relator (@{type_name option},@{const_name option_rel})
  #> declare_natural_relator (@{type_name sum},@{const_name sum_rel})
  #> declare_natural_relator (@{type_name list},@{const_name list_rel})
  
end
*}*)

ML_val {*
  Relators.mk_natural_relator 
    @{context} 
    [@{term "Ra::('c\<times>'a) set"},@{term "\<langle>Rb\<rangle>option_rel"}] 
    @{type_name prod}
  |> the
  |> Thm.cterm_of @{context}
;
  Relators.mk_fun_rel @{term "\<langle>Id\<rangle>option_rel"} @{term "\<langle>Id\<rangle>list_rel"}
  |> Thm.cterm_of @{context}
*}

subsubsection "Additional Properties"
lemmas [relator_props] = 
  single_valued_Id
  subset_refl
  refl

(* TODO: Move *)
lemma eq_UNIV_iff: "S=UNIV \<longleftrightarrow> (\<forall>x. x\<in>S)" by auto

lemma fun_rel_sv[relator_props]: 
  assumes RAN: "Range Ra = UNIV" 
  assumes SV: "single_valued Rv"
  shows "single_valued (Ra \<rightarrow> Rv)"
proof (intro single_valuedI ext impI allI)
  fix f g h x'
  assume R1: "(f,g)\<in>Ra\<rightarrow>Rv"
  and R2: "(f,h)\<in>Ra\<rightarrow>Rv"

  from RAN obtain x where AR: "(x,x')\<in>Ra" by auto
  from fun_relD[OF R1 AR] have "(f x,g x') \<in> Rv" .
  moreover from fun_relD[OF R2 AR] have "(f x,h x') \<in> Rv" .
  ultimately show "g x' = h x'" using SV by (auto dest: single_valuedD)
qed

lemmas [relator_props] = Range_Id

lemma fun_rel_id[relator_props]: "\<lbrakk>R1=Id; R2=Id\<rbrakk> \<Longrightarrow> R1 \<rightarrow> R2 = Id"
  by (auto simp: fun_rel_def)

lemma fun_rel_id_simp[simp]: "Id\<rightarrow>Id = Id" by tagged_solver

lemma fun_rel_comp_dist[relator_props]: 
  "(R1\<rightarrow>R2) O (R3\<rightarrow>R4) \<subseteq> ((R1 O R3) \<rightarrow> (R2 O R4))"
  by (auto simp: fun_rel_def)

lemma fun_rel_mono[relator_props]: "\<lbrakk> R1\<subseteq>R2; R3\<subseteq>R4 \<rbrakk> \<Longrightarrow> R2\<rightarrow>R3 \<subseteq> R1\<rightarrow>R4"
  by (force simp: fun_rel_def)

    
lemma prod_rel_sv[relator_props]: 
  "\<lbrakk>single_valued R1; single_valued R2\<rbrakk> \<Longrightarrow> single_valued (\<langle>R1,R2\<rangle>prod_rel)"
  by (auto intro: single_valuedI dest: single_valuedD simp: prod_rel_def)

lemma prod_rel_id[relator_props]: "\<lbrakk>R1=Id; R2=Id\<rbrakk> \<Longrightarrow> \<langle>R1,R2\<rangle>prod_rel = Id"
  by (auto simp: prod_rel_def)

lemma prod_rel_id_simp[simp]: "\<langle>Id,Id\<rangle>prod_rel = Id" by tagged_solver

lemma prod_rel_mono[relator_props]: 
"\<lbrakk> R2\<subseteq>R1; R3\<subseteq>R4 \<rbrakk> \<Longrightarrow> \<langle>R2,R3\<rangle>prod_rel \<subseteq> \<langle>R1,R4\<rangle>prod_rel"
  by (auto simp: prod_rel_def)

lemma prod_rel_range[relator_props]: "\<lbrakk>Range Ra=UNIV; Range Rb=UNIV\<rbrakk> 
  \<Longrightarrow> Range (\<langle>Ra,Rb\<rangle>prod_rel) = UNIV"
  apply (auto simp: prod_rel_def)
  by (metis Range_iff UNIV_I)+
 
lemma option_rel_sv[relator_props]:
  "\<lbrakk>single_valued R\<rbrakk> \<Longrightarrow> single_valued (\<langle>R\<rangle>option_rel)"
  by (auto intro: single_valuedI dest: single_valuedD simp: option_rel_def)

lemma option_rel_id[relator_props]: 
  "R=Id \<Longrightarrow> \<langle>R\<rangle>option_rel = Id" by (auto simp: option_rel_def)

lemma option_rel_id_simp[simp]: "\<langle>Id\<rangle>option_rel = Id" by tagged_solver

lemma option_rel_mono[relator_props]: "R\<subseteq>R' \<Longrightarrow> \<langle>R\<rangle>option_rel \<subseteq> \<langle>R'\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma option_rel_range: "Range R = UNIV \<Longrightarrow> Range (\<langle>R\<rangle>option_rel) = UNIV"
  apply (auto simp: option_rel_def Range_iff)
  by (metis Range_iff UNIV_I option.exhaust)

lemma sum_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rl; single_valued Rr\<rbrakk> \<Longrightarrow> single_valued (\<langle>Rl,Rr\<rangle>sum_rel)"
  by (auto intro: single_valuedI dest: single_valuedD simp: sum_rel_def)

lemma sum_rel_id[relator_props]: "\<lbrakk>Rl=Id; Rr=Id\<rbrakk> \<Longrightarrow> \<langle>Rl,Rr\<rangle>sum_rel = Id"
  apply (auto elim: sum_relE)
  apply (case_tac b)
  apply simp_all
  done

lemma sum_rel_id_simp[simp]: "\<langle>Id,Id\<rangle>sum_rel = Id" by tagged_solver

lemma sum_rel_mono[relator_props]:
  "\<lbrakk> Rl\<subseteq>Rl'; Rr\<subseteq>Rr' \<rbrakk> \<Longrightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<subseteq> \<langle>Rl',Rr'\<rangle>sum_rel"
  by (auto simp: sum_rel_def)

lemma sum_rel_range[relator_props]:
  "\<lbrakk> Range Rl=UNIV; Range Rr=UNIV \<rbrakk> \<Longrightarrow> Range (\<langle>Rl,Rr\<rangle>sum_rel) = UNIV"
  apply (auto simp: sum_rel_def Range_iff)
  by (metis Range_iff UNIV_I sumE)

lemma list_rel_sv_iff: 
  "single_valued (\<langle>R\<rangle>list_rel) \<longleftrightarrow> single_valued R"
  apply (intro iffI[rotated] single_valuedI allI impI)
  apply (clarsimp simp: list_rel_def)
proof -
  fix x y z
  assume SV: "single_valued R"
  assume "list_all2 (\<lambda>x x'. (x, x') \<in> R) x y" and
    "list_all2 (\<lambda>x x'. (x, x') \<in> R) x z"
  thus "y=z"
    apply (induct arbitrary: z rule: list_all2_induct)
    apply simp
    apply (case_tac z)
    apply force
    apply (force intro: single_valuedD[OF SV])
    done
next
  fix x y z
  assume SV: "single_valued (\<langle>R\<rangle>list_rel)"
  assume "(x,y)\<in>R" "(x,z)\<in>R"
  hence "([x],[y])\<in>\<langle>R\<rangle>list_rel" and "([x],[z])\<in>\<langle>R\<rangle>list_rel"
    by (auto simp: list_rel_def)
  with single_valuedD[OF SV] show "y=z" by blast
qed

lemma list_rel_sv[relator_props]: 
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>list_rel)" 
  by (simp add: list_rel_sv_iff)

lemma list_rel_id[relator_props]: "\<lbrakk>R=Id\<rbrakk> \<Longrightarrow> \<langle>R\<rangle>list_rel = Id"
  by (auto simp add: list_rel_def list_all2_eq[symmetric])

lemma list_rel_id_simp[simp]: "\<langle>Id\<rangle>list_rel = Id" by tagged_solver

lemma list_rel_mono[relator_props]: 
  assumes A: "R\<subseteq>R'" 
  shows "\<langle>R\<rangle>list_rel \<subseteq> \<langle>R'\<rangle>list_rel"
proof clarsimp
  fix l l'
  assume "(l,l')\<in>\<langle>R\<rangle>list_rel"
  thus "(l,l')\<in>\<langle>R'\<rangle>list_rel"
    apply induct
    using A
    by auto
qed

lemma list_rel_range[relator_props]:
  assumes A: "Range R = UNIV"
  shows "Range (\<langle>R\<rangle>list_rel) = UNIV"
proof (clarsimp simp: eq_UNIV_iff)
  fix l
  show "l\<in>Range (\<langle>R\<rangle>list_rel)"
    apply (induct l)
    using A[unfolded eq_UNIV_iff]
    by (auto simp: Range_iff intro: list_relI)
qed


lemma bijective_imp_sv:  
  "bijective R \<Longrightarrow> single_valued R"
  "bijective R \<Longrightarrow> single_valued (R\<inverse>)"
  by (simp_all add: bijective_alt)

(* TODO: Move *)
declare bijective_Id[relator_props]
declare bijective_Empty[relator_props]

text {* Pointwise refinement for set types: *}
lemma set_rel_sv[relator_props]: 
  "single_valued (\<langle>R\<rangle>set_rel)"
  by (auto intro: single_valuedI dest: single_valuedD simp: set_rel_def) []

lemma set_rel_id[relator_props]: "R=Id \<Longrightarrow> \<langle>R\<rangle>set_rel = Id"
  by (auto simp add: set_rel_def)

lemma set_rel_id_simp[simp]: "\<langle>Id\<rangle>set_rel = Id" by tagged_solver

lemma set_rel_csv[relator_props]:
  "\<lbrakk> single_valued (R\<inverse>) \<rbrakk> 
  \<Longrightarrow> single_valued ((\<langle>R\<rangle>set_rel)\<inverse>)"
  apply (rule single_valuedI)
  apply (simp only: converse_iff)

  apply (simp add: single_valued_def Image_def set_rel_def)
  apply (intro allI impI equalityI)
    apply (clarsimp, blast) []
    apply (clarsimp, drule (1) set_mp, blast) []
  done

subsection {* Invariant and Abstraction *}

text {*
  Quite often, a relation can be described as combination of an
  abstraction function and an invariant, such that the invariant describes valid
  values on the concrete domain, and the abstraction function maps valid 
  concrete values to its corresponding abstract value.
*}
definition build_rel where 
  "build_rel \<alpha> I \<equiv> {(c,a) . a=\<alpha> c \<and> I c}"
abbreviation "br\<equiv>build_rel"
lemmas br_def[refine_rel_defs] = build_rel_def

lemma brI[intro?]: "\<lbrakk> a=\<alpha> c; I c \<rbrakk> \<Longrightarrow> (c,a)\<in>br \<alpha> I"
  by (simp add: br_def)

lemma br_id[simp]: "br id (\<lambda>_. True) = Id"
  unfolding build_rel_def by auto

lemma br_chain: 
  "(build_rel \<beta> J) O (build_rel \<alpha> I) = build_rel (\<alpha>\<circ>\<beta>) (\<lambda>s. J s \<and> I (\<beta> s))"
  unfolding build_rel_def by auto

lemma br_sv[simp, intro!,relator_props]: "single_valued (br \<alpha> I)"
  unfolding build_rel_def 
  apply (rule single_valuedI)
  apply auto
  done

lemma converse_br_sv_iff[simp]: 
  "single_valued (converse (br \<alpha> I)) \<longleftrightarrow> inj_on \<alpha> (Collect I)"
  by (auto intro!: inj_onI single_valuedI dest: single_valuedD inj_onD
    simp: br_def) []

lemmas [relator_props] = single_valued_relcomp

lemma br_comp_alt: "br \<alpha> I O R = { (c,a) . I c \<and> (\<alpha> c,a)\<in>R }"
  by (auto simp add: br_def)

lemma br_comp_alt': 
  "{(c,a) . a=\<alpha> c \<and> I c} O R = { (c,a) . I c \<and> (\<alpha> c,a)\<in>R }"
  by auto

lemma single_valued_as_brE:
  assumes "single_valued R"
  obtains \<alpha> invar where "R=br \<alpha> invar"
  apply (rule that[of "\<lambda>x. THE y. (x,y)\<in>R" "\<lambda>x. x\<in>Domain R"])
  using assms unfolding br_def
  by (auto dest: single_valuedD 
    intro: the_equality[symmetric] theI)

lemma sv_add_invar: 
  "single_valued R \<Longrightarrow> single_valued {(c, a). (c, a) \<in> R \<and> I c}"
  by (auto dest: single_valuedD intro: single_valuedI)



subsection {* Miscellanneous *}
lemma rel_cong: "(f,g)\<in>Id \<Longrightarrow> (x,y)\<in>Id \<Longrightarrow> (f x, g y)\<in>Id" by simp
lemma rel_fun_cong: "(f,g)\<in>Id \<Longrightarrow> (f x, g x)\<in>Id" by simp
lemma rel_arg_cong: "(x,y)\<in>Id \<Longrightarrow> (f x, f y)\<in>Id" by simp

end
