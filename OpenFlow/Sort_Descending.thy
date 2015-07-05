theory Sort_Descending
imports Main
begin

section{* sorting descending *}
  context linorder
  begin
  fun sorted_descending :: "'a list \<Rightarrow> bool" where
    "sorted_descending [] \<longleftrightarrow> True" |
    "sorted_descending (a#as) \<longleftrightarrow> (\<forall>x \<in> set as. a \<ge> x) \<and> sorted_descending as"
  
  definition sort_descending_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
    "sort_descending_key f xs \<equiv> rev (sort_key f xs)"
  end
  lemma sorted_descending_Cons: "sorted_descending (x#xs) \<longleftrightarrow> sorted_descending xs \<and> (\<forall>y\<in>set xs. y \<le> x)"
  by(induction xs) auto
  
  lemma sorted_descending_tail: "sorted_descending (xs@[x]) \<longleftrightarrow> sorted_descending xs \<and> (\<forall>y\<in>set xs. x \<le> y)"
  by(induction xs) auto
  
  lemma sorted_descending: "sorted_descending (rev xs) \<longleftrightarrow> sorted xs"
  apply(induction xs)
   apply(simp)
  apply(simp add: sorted_Cons sorted_descending_tail)
  done
  
  lemma sort_descending: "sorted_descending (sort_descending_key (\<lambda>x. x) xs)"
    by(simp add: sort_descending_key_def sorted_descending)

end