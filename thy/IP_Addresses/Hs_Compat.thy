theory Hs_Compat
imports Main
begin

section\<open>Definitions inspired by the Haskell World.\<close>

definition uncurry :: "('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a"
where
  "uncurry f a \<equiv> (case a of (x,y) \<Rightarrow> f x y)"
lemma uncurry_simp[simp]: "uncurry f (a,b) = f a b" 
  by(simp add: uncurry_def)
lemma uncurry_curry_id: "uncurry \<circ> curry = id" "curry \<circ> uncurry = id" 
  by(simp_all add: fun_eq_iff)
lemma uncurry_split: "P (uncurry f prod) \<longleftrightarrow> (\<forall>x1 x2. prod = (x1, x2) \<longrightarrow> P (f x1 x2))"
  by(cases prod) simp
lemma uncurry_split_asm: "P (uncurry f a) \<longleftrightarrow> \<not>(\<exists>x y. a = (x,y) \<and> \<not>P (f x y))" 
  by(simp split: uncurry_split)
lemmas uncurry_splits = uncurry_split uncurry_split_asm

lemma uncurry_case_stmt: "(case x of (a, b) \<Rightarrow> f a b) = uncurry f x"
  by(cases x, simp)

end
