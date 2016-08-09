section\<open>Option to List and Option to Set\<close>
theory Option_Helpers
imports Main
begin

text\<open>Those are just syntactic helpers.\<close>

definition option2set :: "'a option \<Rightarrow> 'a set" where
  "option2set n \<equiv> (case n of None \<Rightarrow> {} | Some s \<Rightarrow> {s})"

definition option2list :: "'a option \<Rightarrow> 'a list" where
  "option2list n \<equiv> (case n of None \<Rightarrow> [] | Some s \<Rightarrow> [s])"

lemma set_option2list[simp]: "set (option2list k) = option2set k"
  unfolding option2list_def option2set_def by (simp split: option.splits)

lemma option2list_simps[simp]: "option2list (Some x) = [x]" "option2list (None) = []"
  unfolding option2list_def option.simps by(fact refl)+

lemma option2set_None: "option2set None = {}"
  by(simp add: option2set_def)

lemma option2list_map: "option2list (map_option f n) = map f (option2list n)"
  by(simp add: option2list_def split: option.split)

lemma option2set_map: "option2set (map_option f n) = f ` option2set n"
  by(simp add: option2set_def split: option.split)

end