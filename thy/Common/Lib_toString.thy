theory Lib_toString
imports Main
begin


section\<open>toString Functions\<close>

(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"
definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

lemma "string_of_nat 123456 = ''123456''" by eval





fun intersperse :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
"intersperse _ [] = []" |
"intersperse a [x] = x" |
"intersperse a (x#xs) = x @ a # intersperse a xs"


(*this is similar to space_implode or Data.List.intersperse (in Haskell)*)
definition list_separated_toString :: "string \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_separated_toString sep toStr ls = concat (splice (map toStr ls) (replicate (length ls - 1) sep))"

text\<open>A slightly more efficient code equation, which is actually not really faster\<close>
fun list_separated_toString_helper :: "string \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_separated_toString_helper sep toStr [] = ''''" |
  "list_separated_toString_helper sep toStr [l] = toStr l" |
  "list_separated_toString_helper sep toStr (l#ls) = (toStr l)@sep@list_separated_toString_helper sep toStr ls"
lemma list_separated_toString_helper: "list_separated_toString = list_separated_toString_helper"
proof -
  { fix sep and toStr::"('a \<Rightarrow> char list)" and ls
    have "list_separated_toString sep toStr ls = list_separated_toString_helper sep toStr ls"
      by(induction sep toStr ls rule: list_separated_toString_helper.induct) (simp_all add: list_separated_toString_def)
  } thus ?thesis by(simp add: fun_eq_iff)
qed

lemma list_separated_toString_intersperse:
  "intersperse sep (map f xs) = list_separated_toString [sep] f xs"
  apply(simp add: list_separated_toString_helper)
  apply(induction "[sep]" f xs rule: list_separated_toString_helper.induct)
    by simp+

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

subsection\<open>Enum set to string\<close>
  fun enum_set_get_one :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a option" where
    "enum_set_get_one []     S = None" |
    "enum_set_get_one (s#ss) S = (if s \<in> S then Some s else enum_set_get_one ss S)"

  lemma enum_set_get_one_empty: "enum_set_get_one ss {} = None"
    by(induction ss) simp_all
  
  lemma enum_set_get_one_None: "S \<subseteq> set ss \<Longrightarrow> enum_set_get_one ss S = None \<longleftrightarrow> S = {}"
    apply(induction ss)
     apply(simp)
    apply(simp)
    apply rule
     apply blast
    by fast
 
  lemma enum_set_get_one_Some: "S \<subseteq> set ss \<Longrightarrow> enum_set_get_one ss S = Some x \<Longrightarrow> x \<in> S"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    apply(blast)
    done
  corollary enum_set_get_one_enum_Some: "enum_set_get_one enum_class.enum S = Some x \<Longrightarrow> x \<in> S"
    using enum_set_get_one_Some[where ss=enum_class.enum, simplified enum_UNIV] by auto

  lemma enum_set_get_one_Ex_Some: "S \<subseteq> set ss \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>x. enum_set_get_one ss S = Some x"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    apply(blast)
    done
  corollary enum_set_get_one_enum_Ex_Some: "S \<noteq> {} \<Longrightarrow> \<exists>x. enum_set_get_one enum_class.enum S = Some x"
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
   apply(simp)
   apply(intro conjI impI)
   apply(simp add: enum_set_get_one_empty)
   done
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
