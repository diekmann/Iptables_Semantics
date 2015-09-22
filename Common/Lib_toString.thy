theory Lib_toString
imports Main
begin


section{*toString Functions*}

(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"
definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"


definition list_separated_toString :: "string \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_separated_toString sep toStr ls = concat (splice (map toStr ls) (replicate (length ls - 1) sep))  "

definition list_toString :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_toString toStr ls = ''[''@ list_separated_toString '', '' toStr ls @'']''"

lemma "list_toString string_of_nat [1,2,3] = ''[1, 2, 3]''" by eval

(*HACK: rewrite quotes such that they are better printable by Isabelle*)
definition quote_rewrite :: "string \<Rightarrow> string" where
  "quote_rewrite \<equiv> map (\<lambda>c. if c = Char Nibble2 Nibble2 then CHR ''~'' else c)"
value "quote_rewrite (''foo''@[Char Nibble2 Nibble2])"


fun bool_toString :: "bool \<Rightarrow> string" where
  "bool_toString True = ''True''" |
  "bool_toString False = ''False''"

subsection{*Enum set to string*}
  fun enum_set_get_one :: "'a list \<Rightarrow> 'a set \<Rightarrow> ('a option \<times> 'a set option)" where
    "enum_set_get_one []     S = (None, None)" |
    "enum_set_get_one (s#ss) S = (if s \<in> S then (Some s, Some (S - {s})) else enum_set_get_one ss S)"

  lemma enum_one_in_set_toString_finite_card_le: "finite S \<Longrightarrow> (x, Some S') = enum_set_get_one ss S \<Longrightarrow> card S' < card S"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    by (metis card_gt_0_iff diff_less equals0D lessI)

  lemma enum_one_in_set_toString_empty: "enum_set_get_one ss {} = (None, None)"
    by(induction ss) simp_all
  
  lemma enum_one_in_set_toString_None: "enum_set_get_one ss S = (x, None) \<Longrightarrow> S \<subseteq> set ss \<Longrightarrow> S = {}"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    by blast
  
  lemma enum_one_in_set_toString_Some_singleton: "enum_set_get_one ss S = (x, Some {}) \<Longrightarrow> S \<subseteq> set ss \<Longrightarrow> \<exists>a. S = {a} \<and> Some a = x"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
     apply blast
    by blast

  lemma enum_one_in_set_toString_Some: "enum_set_get_one ss S = (x, Some S') \<Longrightarrow> S \<subseteq> set ss \<Longrightarrow> \<exists>a. S' = S - {a} \<and> Some a = x"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
     apply blast
    by blast
  
  function enum_set_to_list :: "('a::enum) set \<Rightarrow> 'a list" where
    "enum_set_to_list S = (if S = {} then [] else
      case enum_set_get_one (Enum.enum) S of (_, None) \<Rightarrow> []
                                          |  (Some a, Some S') \<Rightarrow> a#enum_set_to_list S')"
  by(pat_completeness) auto
  
  termination enum_set_to_list
    apply(relation "measure (\<lambda>(S). card S)")
     apply(simp_all add: card_gt_0_iff enum_one_in_set_toString_finite_card_le)
    done


  lemma "(S::'a::enum set) \<subseteq> set enum_class.enum"
    by(simp add: enum_UNIV)

  (*this definition is simpler*)
  lemma enum_set_to_list_simps: "enum_set_to_list S =
      (case enum_set_get_one (Enum.enum) S of (_, None) \<Rightarrow> []
                                           |  (Some a, Some S') \<Rightarrow> a#enum_set_to_list  S')"
   apply(simp)
   apply(intro conjI impI)
    apply(case_tac "enum_set_get_one enum_class.enum S")
    apply(rename_tac a b)
    apply(case_tac b)
     apply(simp split: option.split; fail)
    apply(simp)
    apply (metis card_0_eq enum_one_in_set_toString_finite_card_le finite.emptyI not_less0)
   done
  declare enum_set_to_list.simps[simp del]

  (*lemma "finite S \<Longrightarrow> length (enum_set_toString_list toStr S) = card S"
  apply(induction S rule: finite.induct)
   apply(simp add: enum_set_toString_list.simps)
  apply(simp)
  apply(subst enum_set_toString_list_simps)
  (*apply(simp add: enum_set_toString_list_simps split: split_if_asm)*)
  apply(rename_tac A a)
  apply(case_tac "enum_one_in_set_toString toStr enum_class.enum (insert a A)")
  apply(rename_tac x y)
  apply(case_tac y)
   apply(simp)
   apply(drule enum_one_in_set_toString_None[where ss=enum_class.enum, simplified enum_UNIV], simp)
   apply(simp)
  apply(simp)
  apply(rename_tac y')
  apply(drule enum_one_in_set_toString_Some[where ss=enum_class.enum, simplified enum_UNIV], simp)
  apply(clarify)
  apply(case_tac "a \<in> A")
   apply(simp)
   apply (simp add: insert_absorb)
   
   
  apply(simp)
  apply(clarify)
  apply(drule enum_one_in_set_toString_Some[where ss=enum_class.enum, simplified enum_UNIV], simp)
  apply(clarify)
  apply(rename_tac a')
  apply(simp)
  apply(case_tac "a = a'")
   apply(simp)
  
   using enum_one_in_set_toString_Some_singleton[where ss=enum_class.enum, simplified enum_UNIV]
   enum_one_in_set_toString_None[where ss=enum_class.enum, simplified enum_UNIV] *)

  (*apply(induction toStr S rule: enum_set_toString_list.induct)*)
  (*  apply(simp)
    apply(clarify)
    apply(case_tac "enum_one_in_set_toString toStr enum_class.enum S")
    apply(rename_tac a b)
    apply(case_tac b)
     apply(simp)
     apply(drule enum_one_in_set_toString_None)
      apply(simp add: enum_UNIV;fail)
     apply(simp; fail)
    apply(simp)
    apply(clarify)
    apply(intro conjI)
     apply(simp)
     using enum_one_in_set_toString_Some_singleton[where ss=enum_class.enum, simplified enum_UNIV] apply fastforce
    apply(clarify)
    apply(simp)
   oops*)
   

lemma "list_toString bool_toString (enum_set_to_list {True, False}) = ''[False, True]''" by eval

end
