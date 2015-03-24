theory Negation_Type_DNF
imports Fixed_Action Negation_Type_Matching "../Datatype_Selectors"
begin

section{*Negation Type DNF -- Draft*}

(*Just a draft. needed for packet_set*)

type_synonym 'a dnf = "(('a negation_type) list) list"

fun cnf_to_bool :: "('a \<Rightarrow> bool) \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "cnf_to_bool _ [] \<longleftrightarrow> True" |
  "cnf_to_bool f (Pos a#as) \<longleftrightarrow> (f a) \<and> cnf_to_bool f as" |
  "cnf_to_bool f (Neg a#as) \<longleftrightarrow> (\<not> f a) \<and> cnf_to_bool f as"

fun dnf_to_bool :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dnf \<Rightarrow> bool" where
  "dnf_to_bool _ [] \<longleftrightarrow> False" |
  "dnf_to_bool f (as#ass) \<longleftrightarrow> (cnf_to_bool f as) \<or> (dnf_to_bool f ass)"

lemma cnf_to_bool_append: "cnf_to_bool \<gamma> (a1 @ a2) \<longleftrightarrow> cnf_to_bool \<gamma> a1 \<and> cnf_to_bool \<gamma> a2"
  by(induction \<gamma> a1 rule: cnf_to_bool.induct) (simp_all)
lemma dnf_to_bool_append: "dnf_to_bool \<gamma> (a1 @ a2) \<longleftrightarrow> dnf_to_bool \<gamma> a1 \<or> dnf_to_bool \<gamma> a2"
  by(induction a1) (simp_all)

definition dnf_and :: "'a dnf \<Rightarrow> 'a dnf \<Rightarrow> 'a dnf" where
  "dnf_and cnf1 cnf2 = [andlist1 @ andlist2. andlist1 <- cnf1, andlist2 <- cnf2]"

value "dnf_and ([[a,b], [c,d]]) ([[v,w], [x,y]])"


lemma dnf_and_correct: "dnf_to_bool \<gamma> (dnf_and d1 d2) \<longleftrightarrow> dnf_to_bool \<gamma> d1 \<and> dnf_to_bool \<gamma> d2"
 apply(simp add: dnf_and_def)
 apply(induction d1)
 apply(simp_all)
 apply(induction d2)
 apply(simp_all)
 apply(simp add: cnf_to_bool_append dnf_to_bool_append)
 apply(case_tac "cnf_to_bool \<gamma> a")
 apply(simp_all)
 apply(case_tac [!] "cnf_to_bool \<gamma> aa")
 apply(simp_all)
apply (smt2 concat.simps(1) dnf_to_bool.simps(1) list.simps(8))
apply (smt2 concat.simps(1) dnf_to_bool.simps(1) list.simps(8))
by (smt2 concat.simps(1) dnf_to_bool.simps(1) list.simps(8))

 
text{*inverting a DNF*}

text{*Example*}
lemma "(\<not> ((a1 \<and> a2) \<or> b \<or> c)) = ((\<not>a1 \<and> \<not> b \<and> \<not> c) \<or> (\<not>a2 \<and> \<not> b \<and> \<not> c))" by blast
lemma "(\<not> ((a1 \<and> a2) \<or> (b1 \<and> b2) \<or> c)) = ((\<not>a1 \<and> \<not> b1 \<and> \<not> c) \<or> (\<not>a2 \<and> \<not> b1 \<and> \<not> c) \<or> (\<not>a1 \<and> \<not> b2 \<and> \<not> c) \<or> (\<not>a2 \<and> \<not> b2 \<and> \<not> c))" by blast

fun listprepend :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "listprepend [] ns = []" |
  "listprepend (a#as) ns = (map (\<lambda>xs. a#xs) ns) @ (listprepend as ns)"

lemma "listprepend [a,b] [as, bs] = [a#as, a#bs, b#as, b#bs]" by simp

lemma map_a_and: "dnf_to_bool \<gamma> (map (op # a) ds) \<longleftrightarrow> dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds"
  apply(induction ds)
   apply(simp_all)
  apply(case_tac a)
   apply(simp_all)
   apply blast+
  done

text{*this is how @{const listprepend} works: *}
lemma "\<not> dnf_to_bool \<gamma> (listprepend [] ds)" by(simp)
lemma "dnf_to_bool \<gamma> (listprepend [a] ds) \<longleftrightarrow> dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds" 
by(simp add: map_a_and)
lemma "dnf_to_bool \<gamma> (listprepend [a, b] ds) \<longleftrightarrow> (dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds) \<or> (dnf_to_bool \<gamma> [[b]] \<and> dnf_to_bool \<gamma> ds)" 
by(simp add: map_a_and dnf_to_bool_append)


text{*We use @{text "\<exists>"} to model the big @{text "\<or>"} operation*}
lemma listprepend_correct: "dnf_to_bool \<gamma> (listprepend as ds) \<longleftrightarrow> (\<exists>a\<in> set as. dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds)"
  apply(induction as)
   apply(simp)
  apply(simp)
  apply(rename_tac a as)
  apply(simp add: map_a_and cnf_to_bool_append dnf_to_bool_append)
  by blast
lemma listprepend_correct': "dnf_to_bool \<gamma> (listprepend as ds) \<longleftrightarrow> (dnf_to_bool \<gamma> (map (\<lambda>a. [a]) as) \<and> dnf_to_bool \<gamma> ds)"
  apply(induction as)
   apply(simp)
  apply(simp)
  apply(rename_tac a as)
  apply(simp add: map_a_and cnf_to_bool_append dnf_to_bool_append)
  by blast

lemma cnf_invert_singelton: "cnf_to_bool \<gamma> [invert a] \<longleftrightarrow> \<not> cnf_to_bool \<gamma> [a]" by(cases a, simp_all)

lemma cnf_singleton_false: "(\<exists>a'\<in>set as. \<not> cnf_to_bool \<gamma> [a']) \<longleftrightarrow> \<not> cnf_to_bool \<gamma> as"
  by(induction \<gamma> as rule: cnf_to_bool.induct) (simp_all)

fun dnf_not :: "'a dnf \<Rightarrow> 'a dnf" where
  "dnf_not [] = [[]]" | (*False goes to True*)
  "dnf_not (ns#nss) = listprepend (map invert ns) (dnf_not nss)"

lemma dnf_not_correct: "dnf_to_bool \<gamma> (dnf_not d) \<longleftrightarrow> \<not> dnf_to_bool \<gamma> d"
  apply(induction d)
   apply(simp_all)
  apply(simp add: listprepend_correct)
  apply(simp add: cnf_invert_singelton cnf_singleton_false)
  done


end
