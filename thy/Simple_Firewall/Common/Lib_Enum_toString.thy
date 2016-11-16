section\<open>Enum toString Functions\<close>
theory Lib_Enum_toString
imports Main "../../IP_Addresses/Lib_List_toString"
begin

fun bool_toString :: "bool \<Rightarrow> string" where
  "bool_toString True = ''True''" |
  "bool_toString False = ''False''"

subsection\<open>Enum set to string\<close>
  fun enum_set_get_one :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a option" where
    "enum_set_get_one []     S = None" |
    "enum_set_get_one (s#ss) S = (if s \<in> S then Some s else enum_set_get_one ss S)"

  lemma enum_set_get_one_empty: "enum_set_get_one ss {} = None"
    by(induction ss) simp_all
  
  lemma enum_set_get_one_None: "S \<subseteq> set ss \<Longrightarrow> enum_set_get_one ss S = None \<longleftrightarrow> S = {}"
    apply(induction ss)
     apply(simp; fail)
    apply(simp)
    apply(intro conjI)
     apply blast
    by fast
 
  lemma enum_set_get_one_Some: "S \<subseteq> set ss \<Longrightarrow> enum_set_get_one ss S = Some x \<Longrightarrow> x \<in> S"
    apply(induction ss)
     apply(simp; fail)
    apply(simp split: if_split_asm)
    apply(blast)
    done
  corollary enum_set_get_one_enum_Some: "enum_set_get_one enum_class.enum S = Some x \<Longrightarrow> x \<in> S"
    using enum_set_get_one_Some[where ss=enum_class.enum, simplified enum_UNIV] by auto

  lemma enum_set_get_one_Ex_Some: "S \<subseteq> set ss \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>x. enum_set_get_one ss S = Some x"
    apply(induction ss)
     apply(simp; fail)
    apply(simp split: if_split_asm)
    apply(blast)
    done
  corollary enum_set_get_one_enum_Ex_Some:
    "S \<noteq> {} \<Longrightarrow> \<exists>x. enum_set_get_one enum_class.enum S = Some x"
    using enum_set_get_one_Ex_Some[where ss=enum_class.enum, simplified enum_UNIV] by auto
  
  function enum_set_to_list :: "('a::enum) set \<Rightarrow> 'a list" where
    "enum_set_to_list S = (if S = {} then [] else
      case enum_set_get_one Enum.enum S of None \<Rightarrow> []
                                        |  Some a \<Rightarrow> a#enum_set_to_list (S - {a}))"
  by(pat_completeness) auto
  
  termination enum_set_to_list
    apply(relation "measure (\<lambda>(S). card S)")
     apply(simp_all add: card_gt_0_iff)
    apply(drule enum_set_get_one_enum_Some)
    apply(subgoal_tac "finite S")
     prefer 2
     apply force
    apply (meson card_Diff1_less)
    done

  (*this definition is simpler*)
  lemma enum_set_to_list_simps: "enum_set_to_list S =
      (case enum_set_get_one (Enum.enum) S of None \<Rightarrow> []
                                           |  Some a \<Rightarrow> a#enum_set_to_list (S - {a}))"
   by(simp add: enum_set_get_one_empty)
  declare enum_set_to_list.simps[simp del]

  lemma enum_set_to_list: "set (enum_set_to_list A) = A"
    apply(induction A rule: enum_set_to_list.induct)
    apply(case_tac "S = {}")
     apply(simp add: enum_set_to_list.simps; fail)
    apply(simp)
    apply(subst enum_set_to_list_simps)
    apply(simp)
    apply(drule enum_set_get_one_enum_Ex_Some)
    apply(clarify)
    apply(simp)
    apply(drule enum_set_get_one_enum_Some)
    by blast
  
lemma "list_toString bool_toString (enum_set_to_list {True, False}) = ''[False, True]''" by eval

end
