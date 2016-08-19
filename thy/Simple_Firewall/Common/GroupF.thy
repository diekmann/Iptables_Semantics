section\<open>Group by Function\<close>
theory GroupF
imports Main
begin

text\<open>Grouping elements of a list according to a function.\<close>

fun groupF ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
  "groupF f [] = []" |
  "groupF f (x#xs) = (x#(filter (\<lambda>y. f x = f y) xs))#(groupF f (filter (\<lambda>y. f x \<noteq> f y) xs))"

text\<open>trying a more efficient implementation of @{term groupF}\<close>
context
begin
  private fun select_p_tuple :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)"
  where
    "select_p_tuple p x (ts,fs) = (if p x then (x#ts, fs) else (ts, x#fs))"
  
  private definition partition_tailrec :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)"
  where
    "partition_tailrec p xs = foldr (select_p_tuple p) xs ([],[])"
  
  private lemma partition_tailrec: "partition_tailrec f as =  (filter f as,  filter (\<lambda>x. \<not>f x) as)"
  proof - 
    {fix ts_accu fs_accu
      have "foldr (select_p_tuple f) as (ts_accu, fs_accu) =
              (filter f as @ ts_accu,  filter (\<lambda>x. \<not>f x) as @ fs_accu)"
      by(induction as arbitrary: ts_accu fs_accu) simp_all
    } thus ?thesis unfolding partition_tailrec_def by simp
  qed
  
  private lemma
    "groupF f (x#xs) = (let (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs in (x#ts)#(groupF f fs))"
  by(simp add: partition_tailrec)
  
  (*is this more efficient?*)
  private function groupF_code ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
    "groupF_code f [] = []" |
    "groupF_code f (x#xs) = (let
                               (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs
                             in
                               (x#ts)#(groupF_code f fs))"
  by(pat_completeness) auto
  
  private termination groupF_code
    apply(relation "measure (\<lambda>(f,as). length (filter (\<lambda>x. (\<lambda>y. f x = f y) x) as))")
     apply(simp; fail)
    apply(simp add: partition_tailrec)
    using le_imp_less_Suc length_filter_le by blast
  
  lemma groupF_code[code]: "groupF f as = groupF_code f as"
    by(induction f as rule: groupF_code.induct) (simp_all add: partition_tailrec)
  
  export_code groupF checking SML
end

lemma groupF_concat_set: "set (concat (groupF f xs)) = set xs"
  proof(induction f xs rule: groupF.induct)
  case 2 thus ?case by (simp) blast
  qed(simp)

lemma groupF_Union_set: "(\<Union>x \<in> set (groupF f xs). set x) = set xs"
  proof(induction f xs rule: groupF.induct)
  case 2 thus ?case by (simp) blast
  qed(simp)

lemma groupF_set: "\<forall>X \<in> set (groupF f xs). \<forall>x \<in> set X. x \<in> set xs"
  using groupF_concat_set by fastforce

lemma groupF_equality:
  defines "same f A \<equiv> \<forall>a1 \<in> set A. \<forall>a2 \<in> set A. f a1 = f a2"
  shows "\<forall>A \<in> set (groupF f xs). same f A"
  proof(induction f xs rule: groupF.induct)
    case 1 thus ?case by simp
  next
    case (2 f x xs)
      have groupF_fst:
        "groupF f (x # xs) = (x # [y\<leftarrow>xs . f x = f y]) # groupF f [y\<leftarrow>xs . f x \<noteq> f y]" by force
      have step: " \<forall>A\<in>set [x # [y\<leftarrow>xs . f x = f y]]. same f A" unfolding same_def by fastforce
      with 2 show ?case unfolding groupF_fst by fastforce
  qed

lemma groupF_nequality: "A \<in> set (groupF f xs) \<Longrightarrow> B \<in> set (groupF f xs) \<Longrightarrow> A \<noteq> B \<Longrightarrow>
     \<forall>a \<in> set A. \<forall>b \<in> set B. f a \<noteq> f b"
  proof(induction f xs rule: groupF.induct)
  case 1 thus ?case by simp
  next
  case 2 thus ?case
    apply -
    apply(subst (asm) groupF.simps)+
    using groupF_set by fastforce (*1s*)
  qed

lemma groupF_cong: fixes xs::"'a list" and f1::"'a \<Rightarrow> 'b" and f2::"'a \<Rightarrow> 'c"
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set xs. (f1 x = f1 y \<longleftrightarrow> f2 x = f2 y)"
  shows "groupF f1 xs = groupF f2 xs"
  using assms proof(induction f1 xs rule: groupF.induct)
    case (2 f x xs) thus ?case using filter_cong[of xs xs "\<lambda>y. f x = f y" "\<lambda>y. f2 x = f2 y"]
                                     filter_cong[of xs xs "\<lambda>y. f x \<noteq> f y" "\<lambda>y. f2 x \<noteq> f2 y"] by auto
  qed (simp)

lemma groupF_empty: "groupF f xs \<noteq> [] \<longleftrightarrow> xs \<noteq> []"
  by(induction f xs rule: groupF.induct) auto
lemma groupF_empty_elem: "x \<in> set (groupF f xs) \<Longrightarrow> x \<noteq> []"
  by(induction f xs rule: groupF.induct) auto

lemma groupF_distinct: "distinct xs \<Longrightarrow> distinct (concat (groupF f xs))"
  proof(induction f xs rule: groupF.induct)
  case (2 f x xs) thus ?case
    apply (simp)
    apply(intro conjI)
     apply (meson filter_is_subset groupF_set subsetCE)
    apply(subgoal_tac "UNION (set (groupF f [a\<leftarrow>xs . f x \<noteq> f a])) set = set [a\<leftarrow>xs . f x \<noteq> f a]")
     prefer 2
     apply (metis (no_types) groupF_concat_set set_concat)
    by auto
  qed(simp)


text\<open>It is possible to use
    @{term "map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) P))"}
  instead of
    @{term "groupF f P"}
  for the following reasons:
    @{const groupF} executes its compare function (first parameter) very often;
    it always tests for @{term "(f x = f y)"}.
    The function @{term f} may be really expensive.
    At least polyML does not share the result of @{term f} but (probably) always recomputes (part of) it.
    The optimization pre-computes @{term f} and tells @{const groupF} to use
    a really cheap function (@{const snd}) to compare.
    The following lemma tells that those are equal.\<close>
  (* is this also faster for Haskell?*)

lemma groupF_tuple: "groupF f xs = map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) xs))"
  proof(induction f xs rule: groupF.induct)
  case (1 f) thus ?case by simp
  next
  case (2 f x xs)
    have g1: "[y\<leftarrow>xs . f x = f y] = map fst [y\<leftarrow>map (\<lambda>x. (x, f x)) xs . f x = snd y]"
      proof(induction xs arbitrary: f x)
      case Cons thus ?case by fastforce
      qed(simp)
    have g2: "(map (\<lambda>x. (x, f x)) [y\<leftarrow>xs . f x \<noteq> f y]) = [y\<leftarrow>map (\<lambda>x. (x, f x)) xs . f x \<noteq> snd y]"
      proof(induction xs)
      case Cons thus ?case by fastforce
      qed(simp)
    from 2 g1 g2 show ?case by simp
  qed
end