theory GroupF
imports Main
begin

text{*Grouping elements of a list according to a function.*}


fun groupF ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
  "groupF f [] = []" |
  "groupF f (x#xs) = (x#(filter (\<lambda>y. f x = f y) xs))#(groupF f (filter (\<lambda>y. f x \<noteq> f y) xs))"



(*trying a more efficient implementation of groupF*)
context
begin
  private fun select_p_tuple :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)" where
    "select_p_tuple p x (ts,fs) = (if p x then (x#ts, fs) else (ts, x#fs))"
  
  private definition partition_tailrec :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)" where
    "partition_tailrec p xs = foldr (select_p_tuple p) xs ([],[])"
  
  private lemma partition_tailrec: "partition_tailrec f as =  (filter f as,  filter (\<lambda>x. \<not>f x) as)"
  proof - 
    {fix ts_accu fs_accu
      have "foldr (select_p_tuple f) as (ts_accu, fs_accu) = (filter f as @ ts_accu,  filter (\<lambda>x. \<not>f x) as @ fs_accu)"
      by(induction as arbitrary: ts_accu fs_accu) simp_all
    } thus ?thesis unfolding partition_tailrec_def by simp
  qed
  
  private lemma "groupF f (x#xs) = (let (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs in (x#ts)#(groupF f fs))"
  by(simp add: partition_tailrec)
  
  (*is this more efficient?*)
  private function groupF_code ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
    "groupF_code f [] = []" |
    "groupF_code f (x#xs) = (let (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs in (x#ts)#(groupF_code f fs))"
  apply(pat_completeness)
  apply(auto)
  done
  
  private termination groupF_code
    apply(relation "measure (\<lambda>(f,as). length (filter (\<lambda>x. (\<lambda>y. f x = f y) x) as))")
     apply(simp; fail)
    apply(simp add: partition_tailrec)
    using le_imp_less_Suc length_filter_le by blast
  
  lemma groupF_code[code]: "groupF f as = groupF_code f as"
    by(induction f as rule: groupF_code.induct) (simp_all add: partition_tailrec)
  
  export_code groupF in SML
end

lemma groupF_lem:
  defines "same f A \<equiv> (\<forall>a1 \<in> set A. \<forall>a2 \<in> set A. f a1 = f a2)"
  shows "\<forall>A \<in> set (groupF f xs). same f A"
  proof(induction f xs rule: groupF.induct)
    case 1 thus ?case by simp
  next
    case (2 f x xs)
      have groupF_fst: "groupF f (x # xs) = (x # [y\<leftarrow>xs . f x = f y]) # groupF f [y\<leftarrow>xs . f x \<noteq> f y]" by force
      have step: " \<forall>A\<in>set [x # [y\<leftarrow>xs . f x = f y]]. same f A" unfolding same_def by fastforce
      with 2 show ?case unfolding groupF_fst by fastforce
  qed

lemma groupF_set_lem: "set (concat (groupF f xs)) = set xs"
  proof(induction f xs rule: groupF.induct)
  case 2 thus ?case by (simp) blast
  qed(simp)

lemma groupF_set_lem1: "\<forall>X \<in> set (groupF f xs). \<forall>x \<in> set X. x \<in> set xs"
  using groupF_set_lem by fastforce

lemma groupF_lem_not: "A \<in> set (groupF f xs) \<Longrightarrow> B \<in> set (groupF f xs) \<Longrightarrow> A \<noteq> B \<Longrightarrow>
     \<forall>a \<in> set A. \<forall>b \<in> set B. f a \<noteq> f b"
  proof(induction f xs rule: groupF.induct)
  case 1 thus ?case by simp
  next
  case 2 thus ?case
    apply -
    apply(subst (asm) groupF.simps)+
    using groupF_set_lem1 by fastforce (*1s*)
  qed

lemma groupF_cong: fixes xs::"'a list" and f1::"'a \<Rightarrow> 'b" and f2::"'a \<Rightarrow> 'c"
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set xs. (f1 x = f1 y \<longleftrightarrow> f2 x = f2 y)"
  shows "groupF f1 xs = groupF f2 xs"
  using assms proof(induction f1 xs rule: groupF.induct)
    case goal2 thus ?case using filter_cong[of xs xs "\<lambda>y. f x = f y" "\<lambda>y. f2 x = f2 y"]
                                filter_cong[of xs xs "\<lambda>y. f x \<noteq> f y" "\<lambda>y. f2 x \<noteq> f2 y"] by auto
  qed (simp)


end