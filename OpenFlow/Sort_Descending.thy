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

  lemma sort_descending_key_distinct: "distinct xs \<Longrightarrow> distinct (sort_descending_key f xs)"
    by(simp add: sort_descending_key_def)

  lemma sorted_descending_sort_descending_key: "sorted_descending (map f (sort_descending_key f xs))"
    apply(simp add: sort_descending_key_def)
    using sorted_descending by (metis rev_map sorted_sort_key)

  lemma sorted_descending_split: "sorted_descending (map f l) \<Longrightarrow> \<exists>m n. l = m @ n \<and> (\<forall>e \<in> set m. f (hd m) = f e) \<and> (\<forall>e \<in> set n. f e < f (hd m))"
  proof(induction l)
  	case Nil thus ?case by simp
  next
  	case (Cons a as)
  	from Cons(2) have "sorted_descending (map f as)" by simp
  	note mIH = Cons(1)[OF this]
  	thus ?case (is ?kees)
  	proof(cases as)
  		case Nil
  		show ?kees unfolding Nil by force
  	next
  		case (Cons aa ass)
  		show ?kees
  		proof(cases "f a = f aa")
  			case True
  			from mIH obtain m n where mn: "as = m @ n" "(\<forall>e\<in>set m. f (hd m) = f e)" "(\<forall>e\<in>set n. f e < f (hd m))" by blast
  			have "a # as = a # m @ n" using mn(1) by simp
  			moreover have "\<forall>e\<in>set (a # m). f (hd (a # m)) = f e" unfolding list.sel(1) using True mn(2) using Cons sorry
  			ultimately show "\<exists>m n. a # as = m @ n \<and> (\<forall>e\<in>set m. f (hd m) = f e) \<and> (\<forall>e\<in>set n. f e < f (hd m))" using mn(3) sorry
  		next
  			case False
  			with Cons.prems have "\<forall>e\<in>set as. f e < f a" sorry
  			moreover have "a # as = [a] @ as \<and> (\<forall>e\<in>set [a]. f (hd [a]) = f e)" sorry
  			show ?kees
  			sorry
  		qed
  	qed
  qed
  	
end