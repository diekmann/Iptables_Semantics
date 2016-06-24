section {* Standard HOL Bindings *}
theory Autoref_Bindings_HOL
imports "Tool/Autoref_Tool"
begin


  subsection "Structural Expansion"
  text {*
    In some situations, autoref imitates the operations on typeclasses and
    the typeclass hierarchy. This may result in structural mismatches, e.g.,
    a hashcode side-condition may look like:
      @{text [display] "is_hashcode (prod_eq op= op=) hashcode"}

    This cannot be discharged by the rule
      @{text [display] "is_hashcode op= hashcode"}
    
    In order to handle such cases, we introduce a set of simplification lemmas
    that expand the structure of an operator as far as possible.
    These lemmas are integrated into a tagged solver, that can prove equality
    between operators modulo structural expansion.
    *}

definition [simp]: "STRUCT_EQ_tag x y \<equiv> x = y"
lemma STRUCT_EQ_tagI: "x=y \<Longrightarrow> STRUCT_EQ_tag x y" by simp

ML {*
  structure Autoref_Struct_Expand = struct
    structure autoref_struct_expand = Named_Thms (
      val name = @{binding autoref_struct_expand}
      val description = "Autoref: Structural expansion lemmas"
    )

    fun expand_tac ctxt = let
      val ss = put_simpset HOL_basic_ss ctxt addsimps autoref_struct_expand.get ctxt
    in
      SOLVED' (asm_simp_tac ss)
    end


    val setup = autoref_struct_expand.setup
    val decl_setup = fn phi =>
      Tagged_Solver.declare_solver @{thms STRUCT_EQ_tagI} @{binding STRUCT_EQ} 
        "Autoref: Equality modulo structural expansion" 
        (expand_tac) phi

  end
*}

setup Autoref_Struct_Expand.setup
declaration Autoref_Struct_Expand.decl_setup


text {* Sometimes, also relators must be expanded. Usually to check them to be the identity relator *}
definition [simp]: "REL_IS_ID R \<equiv> R=Id"
definition [simp]: "REL_FORCE_ID R \<equiv> R=Id"
lemma REL_IS_ID_trigger: "R=Id \<Longrightarrow> REL_IS_ID R" by simp
lemma REL_FORCE_ID_trigger: "R=Id \<Longrightarrow> REL_FORCE_ID R" by simp

declaration {* Tagged_Solver.add_triggers 
  "Relators.relator_props_solver" @{thms REL_IS_ID_trigger} *}

declaration {* Tagged_Solver.add_triggers 
  "Relators.force_relator_props_solver" @{thms REL_FORCE_ID_trigger} *}

abbreviation "PREFER_id R \<equiv> PREFER REL_IS_ID R"



  
  (* TODO: Most of these are parametricity theorems! *)

  lemmas [autoref_rel_intf] = REL_INTFI[of fun_rel i_fun]

  subsection "Booleans"
  consts
    i_bool :: interface

  lemmas [autoref_rel_intf] = REL_INTFI[of bool_rel i_bool]

  lemma [autoref_itype]:
    "True ::\<^sub>i i_bool"
    "False ::\<^sub>i i_bool"
    "conj ::\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool"
    "op \<longleftrightarrow> ::\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool"
    "op \<longrightarrow> ::\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool"
    "disj ::\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool"
    "Not ::\<^sub>i i_bool \<rightarrow>\<^sub>i i_bool"
    "case_bool ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i I"
    "old.rec_bool ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_bool \<rightarrow>\<^sub>i I"
    by auto

  lemma autoref_bool[autoref_rules]:
    "(x,x)\<in>bool_rel"
    "(conj,conj)\<in>bool_rel\<rightarrow>bool_rel\<rightarrow>bool_rel"
    "(disj,disj)\<in>bool_rel\<rightarrow>bool_rel\<rightarrow>bool_rel"
    "(Not,Not)\<in>bool_rel\<rightarrow>bool_rel"
    "(case_bool,case_bool)\<in>R\<rightarrow>R\<rightarrow>bool_rel\<rightarrow>R"
    "(old.rec_bool,old.rec_bool)\<in>R\<rightarrow>R\<rightarrow>bool_rel\<rightarrow>R"
    "(op \<longleftrightarrow>, op \<longleftrightarrow>)\<in>bool_rel\<rightarrow>bool_rel\<rightarrow>bool_rel"
    "(op \<longrightarrow>, op \<longrightarrow>)\<in>bool_rel\<rightarrow>bool_rel\<rightarrow>bool_rel"
    by (auto split: bool.split simp: rec_bool_is_case)


  subsection "Standard Type Classes"


context begin interpretation autoref_syn .
  text {*
    We allow these operators for all interfaces.
    *}
  lemma [autoref_itype]:
    "op < ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_bool"
    "op \<le> ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_bool"
    "op = ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_bool"
    "op + ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I"
    "op - ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I"
    "op div ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I"
    "op mod ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I"
    "op * ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I"
    "0 ::\<^sub>i I"
    "1 ::\<^sub>i I"
    "numeral x ::\<^sub>i I"
    "uminus ::\<^sub>i I \<rightarrow>\<^sub>i I"
    by auto

  lemma pat_num_generic[autoref_op_pat]:
    "0 \<equiv> OP 0 :::\<^sub>i I"
    "1 \<equiv> OP 1 :::\<^sub>i I"
    "numeral x \<equiv> (OP (numeral x) :::\<^sub>i I)"
    by simp_all

  lemma [autoref_rules]: 
    assumes "PRIO_TAG_GEN_ALGO"
    shows "(op <, op <) \<in> Id\<rightarrow>Id\<rightarrow>bool_rel"
    and "(op \<le>, op \<le>) \<in> Id\<rightarrow>Id\<rightarrow>bool_rel"
    and "(op =, op =) \<in> Id\<rightarrow>Id\<rightarrow>bool_rel"
    and "(numeral x,OP (numeral x) ::: Id) \<in> Id"
    and "(uminus,uminus) \<in> Id \<rightarrow> Id"
    and "(0,0) \<in> Id"
    and "(1,1) \<in> Id"
    by auto

  subsection "Functional Combinators"
  lemma [autoref_itype]: "id ::\<^sub>i I \<rightarrow>\<^sub>i I" by simp
  lemma autoref_id[autoref_rules]: "(id,id)\<in>R\<rightarrow>R" by auto

  term "op o"
  lemma [autoref_itype]: "op \<circ> ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb) \<rightarrow>\<^sub>i (Ic \<rightarrow>\<^sub>i Ia) \<rightarrow>\<^sub>i Ic \<rightarrow>\<^sub>i Ib" 
    by simp
  lemma autoref_comp[autoref_rules]: 
    "(op o, op o) \<in> (Ra \<rightarrow> Rb) \<rightarrow> (Rc \<rightarrow> Ra) \<rightarrow> Rc \<rightarrow> Rb"
    by (auto dest: fun_relD)

  lemma [autoref_itype]: "If ::\<^sub>i i_bool \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i I" by simp
  lemma autoref_If[autoref_rules]: "(If,If)\<in>Id\<rightarrow>R\<rightarrow>R\<rightarrow>R" by auto
  lemma autoref_If_cong[autoref_rules]:
    assumes "(c',c)\<in>Id"
    assumes "REMOVE_INTERNAL c \<Longrightarrow> (t',t)\<in>R"
    assumes "\<not> REMOVE_INTERNAL c \<Longrightarrow> (e',e)\<in>R"
    shows "(If c' t' e',(OP If ::: Id\<rightarrow>R\<rightarrow>R\<rightarrow>R)$c$t$e)\<in>R"
    using assms by (auto)

  lemma [autoref_itype]: "Let ::\<^sub>i Ix \<rightarrow>\<^sub>i (Ix\<rightarrow>\<^sub>iIy) \<rightarrow>\<^sub>i Iy" by auto
  lemma autoref_Let[autoref_rules]: 
    "(Let,Let)\<in>Ra \<rightarrow> (Ra\<rightarrow>Rr) \<rightarrow> Rr"
    by (auto dest: fun_relD)

end

  subsection "Unit"
  consts i_unit :: interface
  lemmas [autoref_rel_intf] = REL_INTFI[of unit_rel i_unit]

  (*lemma [autoref_itype]: "(a::unit) ::\<^sub>i i_unit" by simp*)
  lemma [autoref_rules]: "((),())\<in>unit_rel" by simp

  subsection "Nat"
    consts i_nat :: interface
    lemmas [autoref_rel_intf] = REL_INTFI[of nat_rel i_nat]

context begin interpretation autoref_syn .
    lemma pat_num_nat[autoref_op_pat]:
      "0::nat \<equiv> OP 0 :::\<^sub>i i_nat"
      "1::nat \<equiv> OP 1 :::\<^sub>i i_nat"
      "(numeral x)::nat \<equiv> (OP (numeral x) :::\<^sub>i i_nat)"
      by simp_all
   
    lemma autoref_nat[autoref_rules]:
      "(0, 0::nat) \<in> nat_rel"
      "(Suc, Suc) \<in> nat_rel \<rightarrow> nat_rel"
      "(1, 1::nat) \<in> nat_rel"
      "(numeral n::nat,numeral n::nat) \<in> nat_rel"
      "(op <, op <::nat \<Rightarrow> _) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
      "(op \<le>, op \<le>::nat \<Rightarrow> _) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
      "(op =, op =::nat \<Rightarrow> _) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
      "(op +::nat\<Rightarrow>_,op +)\<in>nat_rel\<rightarrow>nat_rel\<rightarrow>nat_rel"
      "(op -::nat\<Rightarrow>_,op -)\<in>nat_rel\<rightarrow>nat_rel\<rightarrow>nat_rel"
      "(op div::nat\<Rightarrow>_,op div)\<in>nat_rel\<rightarrow>nat_rel\<rightarrow>nat_rel"
      "(op *, op *)\<in>nat_rel\<rightarrow>nat_rel\<rightarrow>nat_rel"
      "(op mod, op mod)\<in>nat_rel\<rightarrow>nat_rel\<rightarrow>nat_rel"
      by auto
    
    lemma autoref_case_nat[autoref_rules]: 
      "(case_nat,case_nat)\<in>Ra \<rightarrow> (Id \<rightarrow> Ra) \<rightarrow> Id \<rightarrow> Ra"
      apply (intro fun_relI)
      apply (auto split: nat.split dest: fun_relD)
      done

    lemma autoref_rec_nat: "(rec_nat,rec_nat) \<in> R \<rightarrow> (Id \<rightarrow> R \<rightarrow> R) \<rightarrow> Id \<rightarrow> R"
      apply (intro fun_relI)
    proof goal_cases
      case (1 s s' f f' n n') thus ?case
        apply (induct n' arbitrary: n s s')
        apply (fastforce simp: fun_rel_def)+
        done
    qed
end

  subsection "Int"
    consts i_int :: interface
    lemmas [autoref_rel_intf] = REL_INTFI[of int_rel i_int]

context begin interpretation autoref_syn .
    lemma pat_num_int[autoref_op_pat]:
      "0::int \<equiv> OP 0 :::\<^sub>i i_int"
      "1::int \<equiv> OP 1 :::\<^sub>i i_int"
      "(numeral x)::int \<equiv> (OP (numeral x) :::\<^sub>i i_int)"
      "(neg_numeral x)::int \<equiv> (OP (neg_numeral x) :::\<^sub>i i_int)"
      by simp_all

    (*lemma [autoref_itype]:
      "(op < :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_bool"
      "(op \<le> :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_bool"
      "(op = :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_bool"
      "(op + :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_int"
      "(op - :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_int"
      "(op div :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int \<rightarrow>\<^sub>i i_int"
      "(uminus :: int \<Rightarrow> _) ::\<^sub>i i_int \<rightarrow>\<^sub>i i_int"
      by auto*)

    lemma autoref_int[autoref_rules (overloaded)]:
      "(0, 0::int) \<in> int_rel"
      "(1, 1::int) \<in> int_rel"
      "(numeral n::int,numeral n::int) \<in> int_rel"
      "(op <, op <::int \<Rightarrow> _) \<in> int_rel \<rightarrow> int_rel \<rightarrow> bool_rel"
      "(op \<le>, op \<le>::int \<Rightarrow> _) \<in> int_rel \<rightarrow> int_rel \<rightarrow> bool_rel"
      "(op =, op =::int \<Rightarrow> _) \<in> int_rel \<rightarrow> int_rel \<rightarrow> bool_rel"
      "(op +::int\<Rightarrow>_,op +)\<in>int_rel\<rightarrow>int_rel\<rightarrow>int_rel"
      "(op -::int\<Rightarrow>_,op -)\<in>int_rel\<rightarrow>int_rel\<rightarrow>int_rel"
      "(op div::int\<Rightarrow>_,op div)\<in>int_rel\<rightarrow>int_rel\<rightarrow>int_rel"
      "(uminus,uminus)\<in>int_rel\<rightarrow>int_rel"
      "(op *, op *)\<in>int_rel\<rightarrow>int_rel\<rightarrow>int_rel"
      "(op mod, op mod)\<in>int_rel\<rightarrow>int_rel\<rightarrow>int_rel"
      by auto
end
  
  subsection "Product"
    consts i_prod :: "interface \<Rightarrow> interface \<Rightarrow> interface"
    lemmas [autoref_rel_intf] = REL_INTFI[of prod_rel i_prod]

context begin interpretation autoref_syn .
    (*
    lemma [autoref_itype]:
      "Pair ::\<^sub>i Ia \<rightarrow>\<^sub>i Ib \<rightarrow>\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod"
      "case_prod ::\<^sub>i (Ia \<rightarrow>\<^sub>i Ib \<rightarrow>\<^sub>i I) \<rightarrow>\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i I"
      "old.rec_prod ::\<^sub>i (Ia \<rightarrow>\<^sub>i Ib \<rightarrow>\<^sub>i I) \<rightarrow>\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i I"
      "fst ::\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i Ia"
      "snd ::\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i Ib"
      "(op = :: _\<times>_ \<Rightarrow> _) ::\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i \<langle>Ia,Ib\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i i_bool"
      by auto
      *)

    lemma prod_refine[autoref_rules]:
      "(Pair,Pair)\<in>Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel"
      "(case_prod,case_prod) \<in> (Ra \<rightarrow> Rb \<rightarrow> Rr) \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rr"
      "(old.rec_prod,old.rec_prod) \<in> (Ra \<rightarrow> Rb \<rightarrow> Rr) \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rr"
      "(fst,fst)\<in>\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Ra"
      "(snd,snd)\<in>\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rb"
      by (auto dest: fun_relD split: prod.split 
        simp: prod_rel_def rec_prod_is_case)

    definition "prod_eq eqa eqb x1 x2 \<equiv> 
      case x1 of (a1,b1) \<Rightarrow> case x2 of (a2,b2) \<Rightarrow> eqa a1 a2 \<and> eqb b1 b2"

    lemma prod_eq_autoref[autoref_rules (overloaded)]:
      "\<lbrakk>GEN_OP eqa op = (Ra\<rightarrow>Ra\<rightarrow>Id); GEN_OP eqb op = (Rb\<rightarrow>Rb\<rightarrow>Id)\<rbrakk> 
      \<Longrightarrow> (prod_eq eqa eqb,op =) \<in> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Id"
      unfolding prod_eq_def[abs_def]
      by (fastforce dest: fun_relD)

    lemma prod_eq_expand[autoref_struct_expand]: "op = = prod_eq op= op="
      unfolding prod_eq_def[abs_def]
      by (auto intro!: ext)
end

  subsection "Option"
    consts i_option :: "interface \<Rightarrow> interface"
    lemmas [autoref_rel_intf] = REL_INTFI[of option_rel i_option]

context begin interpretation autoref_syn .
    (*
    lemma [autoref_itype]:
      "None ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_option"
      "Some ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_option"
      "the ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i I"
      "case_option ::\<^sub>i I \<rightarrow>\<^sub>i (Iv\<rightarrow>\<^sub>iI) \<rightarrow>\<^sub>i \<langle>Iv\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i I"
      "rec_option ::\<^sub>i I \<rightarrow>\<^sub>i (Iv\<rightarrow>\<^sub>iI) \<rightarrow>\<^sub>i \<langle>Iv\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i I"
      "(op = :: _ option \<Rightarrow> _) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i i_bool"
      by auto
      *)

    lemma autoref_opt[autoref_rules]:
      "(None,None)\<in>\<langle>R\<rangle>option_rel"
      "(Some,Some)\<in>R \<rightarrow> \<langle>R\<rangle>option_rel"
      "(case_option,case_option)\<in>Rr\<rightarrow>(R \<rightarrow> Rr)\<rightarrow>\<langle>R\<rangle>option_rel \<rightarrow> Rr"
      "(rec_option,rec_option)\<in>Rr\<rightarrow>(R \<rightarrow> Rr)\<rightarrow>\<langle>R\<rangle>option_rel \<rightarrow> Rr"
      by (auto split: option.split 
        simp: option_rel_def case_option_def[symmetric]
        dest: fun_relD)

    lemma autoref_the[autoref_rules]:
      assumes "SIDE_PRECOND (x\<noteq>None)"
      assumes "(x',x)\<in>\<langle>R\<rangle>option_rel"
      shows "(the x', (OP the ::: \<langle>R\<rangle>option_rel \<rightarrow> R)$x) \<in> R"
      using assms
      by (auto simp: option_rel_def)

    lemma autoref_the_default[autoref_rules]:
      "(the_default, the_default) \<in> R \<rightarrow> \<langle>R\<rangle>option_rel \<rightarrow> R"
      by parametricity

    definition [simp]: "is_None a \<equiv> case a of None \<Rightarrow> True | _ \<Rightarrow> False"
    lemma pat_isNone[autoref_op_pat]:
      "a=None \<equiv> (OP is_None :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i i_bool)$a"
      "None=a \<equiv> (OP is_None :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_option \<rightarrow>\<^sub>i i_bool)$a"
      by (auto intro!: eq_reflection split: option.splits)
    lemma autoref_is_None[autoref_rules]: 
      "(is_None,is_None)\<in>\<langle>R\<rangle>option_rel \<rightarrow> Id"
      by (auto split: option.splits)

    definition "option_eq eq v1 v2 \<equiv> 
      case (v1,v2) of 
        (None,None) \<Rightarrow> True
      | (Some x1, Some x2) \<Rightarrow> eq x1 x2
      | _ \<Rightarrow> False"

    lemma option_eq_autoref[autoref_rules (overloaded)]:
      "\<lbrakk>GEN_OP eq op = (R\<rightarrow>R\<rightarrow>Id)\<rbrakk> 
      \<Longrightarrow> (option_eq eq,op =) \<in> \<langle>R\<rangle>option_rel \<rightarrow> \<langle>R\<rangle>option_rel \<rightarrow> Id"
      unfolding option_eq_def[abs_def]
      by (auto dest: fun_relD split: option.splits elim!: option_relE)

    lemma option_eq_expand[autoref_struct_expand]: 
      "op = = option_eq op="
      by (auto intro!: ext simp: option_eq_def split: option.splits)
end

  subsection "Sum-Types"
  consts i_sum :: "interface \<Rightarrow> interface \<Rightarrow> interface"
  lemmas [autoref_rel_intf] = REL_INTFI[of sum_rel i_sum]

context begin interpretation autoref_syn .
  (*lemma [autoref_itype]:
    "(op = :: _+_ \<Rightarrow> _) ::\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum \<rightarrow>\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum \<rightarrow>\<^sub>i i_bool"
    "Inl ::\<^sub>i Il \<rightarrow>\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum"
    "Inr ::\<^sub>i Ir \<rightarrow>\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum"
    "case_sum ::\<^sub>i (Il\<rightarrow>\<^sub>iI) \<rightarrow>\<^sub>i (Ir \<rightarrow>\<^sub>i I) \<rightarrow>\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum \<rightarrow>\<^sub>i I"
    "old.rec_sum ::\<^sub>i (Il\<rightarrow>\<^sub>iI) \<rightarrow>\<^sub>i (Ir \<rightarrow>\<^sub>i I) \<rightarrow>\<^sub>i \<langle>Il,Ir\<rangle>\<^sub>ii_sum \<rightarrow>\<^sub>i I"
    by auto*)

  lemma autoref_sum[autoref_rules]:
    "(Inl,Inl) \<in> Rl \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel"
    "(Inr,Inr) \<in> Rr \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel"
    "(case_sum,case_sum) \<in> (Rl \<rightarrow> R) \<rightarrow> (Rr \<rightarrow> R) \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> R"
    "(old.rec_sum,old.rec_sum) \<in> (Rl \<rightarrow> R) \<rightarrow> (Rr \<rightarrow> R) \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> R"
    by (fastforce split: sum.split dest: fun_relD 
      simp: rec_sum_is_case)+

  definition "sum_eq eql eqr s1 s2 \<equiv> 
    case (s1,s2) of 
      (Inl x1, Inl x2) \<Rightarrow> eql x1 x2
    | (Inr x1, Inr x2) \<Rightarrow> eqr x1 x2
    | _ \<Rightarrow> False"

  lemma sum_eq_autoref[autoref_rules (overloaded)]:
    "\<lbrakk>GEN_OP eql op = (Rl\<rightarrow>Rl\<rightarrow>Id); GEN_OP eqr op = (Rr\<rightarrow>Rr\<rightarrow>Id)\<rbrakk> 
    \<Longrightarrow> (sum_eq eql eqr,op =) \<in> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> Id"
    unfolding sum_eq_def[abs_def]
    by (fastforce dest: fun_relD elim!: sum_relE)

  lemma sum_eq_expand[autoref_struct_expand]: "op = = sum_eq op= op="
    by (auto intro!: ext simp: sum_eq_def split: sum.splits)

  lemmas [autoref_rules] = is_Inl_param is_Inr_param

  lemma autoref_sum_Projl[autoref_rules]: 
    "\<lbrakk>SIDE_PRECOND (is_Inl s); (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> 
    \<Longrightarrow> (Sum_Type.sum.projl s', (OP Sum_Type.sum.projl ::: \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> Ra)$s)\<in>Ra"
    by simp parametricity

  lemma autoref_sum_Projr[autoref_rules]: 
    "\<lbrakk>SIDE_PRECOND (is_Inr s); (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> 
    \<Longrightarrow> (Sum_Type.sum.projr s', (OP Sum_Type.sum.projr ::: \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> Rb)$s)\<in>Rb"
    by simp parametricity

end

subsection "List"
  consts i_list :: "interface \<Rightarrow> interface"
  lemmas [autoref_rel_intf] = REL_INTFI[of list_rel i_list]

context begin interpretation autoref_syn .
  (*
  term nth
  lemma [autoref_itype]:
    "(op = :: _ list \<Rightarrow> _) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i i_bool"
    "[] ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "op # ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "op @ ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "case_list ::\<^sub>i Ir \<rightarrow>\<^sub>i (I\<rightarrow>\<^sub>i\<langle>I\<rangle>\<^sub>ii_list\<rightarrow>\<^sub>iIr) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Ir"
    "rec_list ::\<^sub>i Ir \<rightarrow>\<^sub>i (I\<rightarrow>\<^sub>i\<langle>I\<rangle>\<^sub>ii_list\<rightarrow>\<^sub>iIr\<rightarrow>\<^sub>iIr) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Ir"
    "map ::\<^sub>i (I1\<rightarrow>\<^sub>iI2) \<rightarrow>\<^sub>i \<langle>I1\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I2\<rangle>\<^sub>ii_list"
    "foldl ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb\<rightarrow>\<^sub>iIa) \<rightarrow>\<^sub>i Ia \<rightarrow>\<^sub>i \<langle>Ib\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Ia"
    "foldr ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb\<rightarrow>\<^sub>iIb) \<rightarrow>\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Ib \<rightarrow>\<^sub>i Ib"
    "fold ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb\<rightarrow>\<^sub>iIb) \<rightarrow>\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Ib \<rightarrow>\<^sub>i Ib"
    "take ::\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "drop ::\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "length ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i i_nat"
    "nth ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i i_nat \<rightarrow>\<^sub>i I"
    "hd ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i I"
    "tl ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    "last ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i I"
    "butlast ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list"
    by auto
    *)

  lemma autoref_append[autoref_rules]: 
    "(append, append)\<in>\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    by (auto simp: list_rel_def list_all2_appendI)

  lemma refine_list[autoref_rules]:
    "(Nil,Nil)\<in>\<langle>R\<rangle>list_rel"
    "(Cons,Cons)\<in>R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    "(case_list,case_list)\<in>Rr\<rightarrow>(R\<rightarrow>\<langle>R\<rangle>list_rel\<rightarrow>Rr)\<rightarrow>\<langle>R\<rangle>list_rel\<rightarrow>Rr"
    apply (force dest: fun_relD split: list.split)+
    done

  lemma autoref_rec_list[autoref_rules]: "(rec_list,rec_list) 
    \<in> Ra \<rightarrow> (Rb \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> Ra \<rightarrow> Ra) \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> Ra"
  proof (intro fun_relI, goal_cases)
    case prems: (1 a a' f f' l l')
    from prems(3) show ?case
      using prems(1,2)
      apply (induct arbitrary: a a')
      apply simp
      apply (fastforce dest: fun_relD)
      done
  qed

  lemma refine_map[autoref_rules]: 
    "(map,map)\<in>(R1\<rightarrow>R2) \<rightarrow> \<langle>R1\<rangle>list_rel \<rightarrow> \<langle>R2\<rangle>list_rel"
    using [[autoref_sbias = -1]]
    unfolding map_rec[abs_def]
    by autoref

  lemma refine_fold[autoref_rules]: 
    "(fold,fold)\<in>(Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs \<rightarrow> Rs"
    "(foldl,foldl)\<in>(Rs\<rightarrow>Re\<rightarrow>Rs) \<rightarrow> Rs \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs"
    "(foldr,foldr)\<in>(Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs \<rightarrow> Rs"
    unfolding List.fold_def List.foldr_def List.foldl_def
    by (autoref)+

  schematic_goal autoref_take[autoref_rules]: "(take,take)\<in>(?R::(_\<times>_) set)"
    unfolding take_def by autoref
  schematic_goal autoref_drop[autoref_rules]: "(drop,drop)\<in>(?R::(_\<times>_) set)"
    unfolding drop_def by autoref
  schematic_goal autoref_length[autoref_rules]: 
    "(length,length)\<in>(?R::(_\<times>_) set)"
    unfolding size_list_overloaded_def size_list_def 
    by (autoref)

  lemma autoref_nth[autoref_rules]: 
    assumes "(l,l')\<in>\<langle>R\<rangle>list_rel"
    assumes "(i,i')\<in>Id"
    assumes "SIDE_PRECOND (i' < length l')"
    shows "(nth l i,(OP nth ::: \<langle>R\<rangle>list_rel \<rightarrow> Id \<rightarrow> R)$l'$i')\<in>R"
    unfolding ANNOT_def
    using assms
    apply (induct arbitrary: i i')
    apply simp
    apply (case_tac i')
    apply auto
    done

  fun list_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
    "list_eq eq [] [] \<longleftrightarrow> True"
  | "list_eq eq (a#l) (a'#l') 
       \<longleftrightarrow> (if eq a a' then list_eq eq l l' else False)"
  | "list_eq _ _ _ \<longleftrightarrow> False"

  lemma autoref_list_eq_aux: "
    (list_eq,list_eq) \<in> 
      (R \<rightarrow> R \<rightarrow> Id) \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> Id"
  proof (intro fun_relI, goal_cases)
    case (1 eq eq' l1 l1' l2 l2')
    thus ?case
      apply -
      apply (induct eq' l1' l2' arbitrary: l1 l2 rule: list_eq.induct)
      apply simp
      apply (case_tac l1)
      apply simp
      apply (case_tac l2)
      apply (simp)
      apply (auto dest: fun_relD) []
      apply (case_tac l1)
      apply simp
      apply simp
      apply (case_tac l2)
      apply simp
      apply simp
      done
  qed

  lemma list_eq_expand[autoref_struct_expand]: "(op =) = (list_eq op =)"
  proof (intro ext)
    fix l1 l2 :: "'a list"
    show "(l1 = l2) \<longleftrightarrow> list_eq op = l1 l2"
      apply (induct "op = :: 'a \<Rightarrow> _" l1 l2 rule: list_eq.induct)
      apply simp_all
      done
  qed

  lemma autoref_list_eq[autoref_rules (overloaded)]:
    "GEN_OP eq op = (R\<rightarrow>R\<rightarrow>Id) \<Longrightarrow> (list_eq eq, op =) 
    \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> Id"
    unfolding autoref_tag_defs
    apply (subst list_eq_expand)
    apply (parametricity add: autoref_list_eq_aux)
    done

  lemma autoref_hd[autoref_rules]:
    "\<lbrakk> SIDE_PRECOND (l'\<noteq>[]); (l,l') \<in> \<langle>R\<rangle>list_rel \<rbrakk> \<Longrightarrow>
      (hd l,(OP hd ::: \<langle>R\<rangle>list_rel \<rightarrow> R)$l') \<in> R"
    apply (simp add: ANNOT_def)
    apply (cases l')
    apply simp
    apply (cases l)
    apply auto
    done

  lemma autoref_tl[autoref_rules]:
    "(tl,tl) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    unfolding tl_def[abs_def]
    by autoref

  definition [simp]: "is_Nil a \<equiv> case a of [] \<Rightarrow> True | _ \<Rightarrow> False"

  lemma is_Nil_pat[autoref_op_pat]:
    "a=[] \<equiv> (OP is_Nil :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i i_bool)$a"
    "[]=a \<equiv> (OP is_Nil :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i i_bool)$a"
    by (auto intro!: eq_reflection split: list.splits)

  lemma autoref_is_Nil[param,autoref_rules]: 
    "(is_Nil,is_Nil)\<in>\<langle>R\<rangle>list_rel \<rightarrow> bool_rel"
    by (auto split: list.splits)

  lemma conv_to_is_Nil: 
    "l=[] \<longleftrightarrow> is_Nil l"
    "[]=l \<longleftrightarrow> is_Nil l"
    unfolding is_Nil_def by (auto split: list.split)

  lemma autoref_butlast[param, autoref_rules]: 
    "(butlast,butlast) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    unfolding butlast_def conv_to_is_Nil
    by parametricity

  definition [simp]: "op_list_singleton x \<equiv> [x]"
  lemma op_list_singleton_pat[autoref_op_pat]:
    "[x] \<equiv> (OP op_list_singleton :::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list)$x" by simp
  lemma autoref_list_singleton[autoref_rules]: 
    "(\<lambda>a. [a],op_list_singleton) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel"
    by auto

  definition [simp]: "op_list_append_elem s x \<equiv> s@[x]"

  lemma pat_list_append_elem[autoref_op_pat]: 
    "s@[x] \<equiv> (OP op_list_append_elem :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_list)$s$x" 
    by (simp add: relAPP_def)

  lemma autoref_list_append_elem[autoref_rules]: 
    "(\<lambda>s x. s@[x], op_list_append_elem) \<in> \<langle>R\<rangle>list_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>list_rel"
    unfolding op_list_append_elem_def[abs_def] by parametricity


  declare param_rev[autoref_rules]

  declare param_all_interval_nat[autoref_rules]
  lemma [autoref_op_pat]: 
    "(\<forall>i<u. P i) \<equiv> OP List.all_interval_nat P 0 u"
    "(\<forall>i\<le>u. P i) \<equiv> OP List.all_interval_nat P 0 (Suc u)"
    "(\<forall>i<u. l\<le>i \<longrightarrow> P i) \<equiv> OP List.all_interval_nat P l u"
    "(\<forall>i\<le>u. l\<le>i \<longrightarrow> P i) \<equiv> OP List.all_interval_nat P l (Suc u)"
    by (auto intro!: eq_reflection simp: List.all_interval_nat_def)


  lemmas [autoref_rules] = param_dropWhile param_takeWhile

end

subsection "Examples"

text {* Be careful to make the concrete type a schematic type variable.
  The default behaviour of @{text "schematic_lemma"} makes it a fixed variable,
  that will not unify with the infered term! *}
schematic_goal 
  "(?f::?'c,[1,2,3]@[4::nat])\<in>?R"
  by autoref

schematic_goal 
  "(?f::?'c,[1::nat,
    2,3,4,5,6,7,8,9,0,1,43,5,5,435,5,1,5,6,5,6,5,63,56
  ]
  )\<in>?R"
  apply (autoref)
  done

schematic_goal 
  "(?f::?'c,[1,2,3] = [])\<in>?R"
  by autoref

text {*
  When specifying custom refinement rules on the fly, be careful with
  the type-inference between @{text "notes"} and @{text "shows"}. It's
  too easy to ,,decouple'' the type @{text "'a"} in the autoref-rule and
  the actual goal, as shown below!
*}

schematic_goal 
  notes [autoref_rules] = IdI[where 'a="'a"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])\<in>?R"
  txt {* The autoref-rule is bound with type @{text "'a::typ"}, while
    the goal statement has @{text "'a::numeral"}! *}
  apply (autoref (keep_goal))
  txt {* We get an unsolved goal, as it finds no rule to translate 
    @{text "a"} *}
  oops

text {* Here comes the correct version. Note the duplicate sort annotation
  of type @{text "'a"}: *}
schematic_goal 
  notes [autoref_rules_raw] = IdI[where 'a="'a::numeral"]
  notes [autoref_itype] = itypeI[where 't="'a::numeral" and I=i_std]
  shows "(?f::?'c, hd [a,b,c::'a::numeral])\<in>?R"
  by (autoref)

text {* Special cases of equality: Note that we do not require equality
  on the element type! *}
schematic_goal 
  (*notes [autoref_itype] = itypeI[of a "\<langle>I\<rangle>\<^sub>ii_option"]*)
  assumes [autoref_rules]: "(ai,a)\<in>\<langle>R\<rangle>option_rel"
  shows "(?f::?'c, a = None)\<in>?R"
  apply (autoref (keep_goal))
  done


schematic_goal 
  (*notes [autoref_itype] = itypeI[of a "\<langle>I\<rangle>\<^sub>ii_list"]*)
  assumes [autoref_rules]: "(ai,a)\<in>\<langle>R\<rangle>list_rel"  
  shows "(?f::?'c, [] = a)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  shows "(?f::?'c, [1,2] = [2,3::nat])\<in>?R"
  apply (autoref (keep_goal))
  done


end
