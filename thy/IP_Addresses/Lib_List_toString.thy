theory Lib_List_toString
imports Lib_Numbers_toString
begin


section\<open>Printing Lists\<close>

fun intersperse :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
"intersperse _ [] = []" |
"intersperse a [x] = x" |
"intersperse a (x#xs) = x @ a # intersperse a xs"

(*this is similar to space_implode or Data.List.intersperse (in Haskell)*)
definition list_separated_toString :: "string \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_separated_toString sep toStr ls = concat (splice (map toStr ls) (replicate (length ls - 1) sep))"

text\<open>A slightly more efficient code equation, which is actually not really faster (in certain languages)\<close>
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

end
