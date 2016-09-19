section\<open>Negation Type DNF\<close>
theory Negation_Type_DNF
imports Negation_Type
begin


(*Just a draft. needed for packet_set*)

type_synonym 'a dnf = "(('a negation_type) list) list"

fun cnf_to_bool :: "('a \<Rightarrow> bool) \<Rightarrow> 'a negation_type list \<Rightarrow> bool" where
  "cnf_to_bool _ [] \<longleftrightarrow> True" |
  "cnf_to_bool f (Pos a#as) \<longleftrightarrow> (f a) \<and> cnf_to_bool f as" |
  "cnf_to_bool f (Neg a#as) \<longleftrightarrow> (\<not> f a) \<and> cnf_to_bool f as"

fun dnf_to_bool :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dnf \<Rightarrow> bool" where
  "dnf_to_bool _ [] \<longleftrightarrow> False" |
  "dnf_to_bool f (as#ass) \<longleftrightarrow> (cnf_to_bool f as) \<or> (dnf_to_bool f ass)"

text\<open>representing @{const True}\<close>
definition dnf_True :: "'a dnf" where
  "dnf_True \<equiv> [[]]"
lemma dnf_True: "dnf_to_bool f dnf_True"
  unfolding dnf_True_def by(simp)

text\<open>representing @{const False}\<close>
definition dnf_False :: "'a dnf" where
  "dnf_False \<equiv> []"
lemma dnf_False: "\<not> dnf_to_bool f dnf_False"
  unfolding dnf_False_def by(simp)

lemma cnf_to_bool_append: "cnf_to_bool \<gamma> (a1 @ a2) \<longleftrightarrow> cnf_to_bool \<gamma> a1 \<and> cnf_to_bool \<gamma> a2"
  by(induction \<gamma> a1 rule: cnf_to_bool.induct) (simp_all)
lemma dnf_to_bool_append: "dnf_to_bool \<gamma> (a1 @ a2) \<longleftrightarrow> dnf_to_bool \<gamma> a1 \<or> dnf_to_bool \<gamma> a2"
  by(induction a1) (simp_all)

definition dnf_and :: "'a dnf \<Rightarrow> 'a dnf \<Rightarrow> 'a dnf" where
  "dnf_and cnf1 cnf2 = [andlist1 @ andlist2. andlist1 <- cnf1, andlist2 <- cnf2]"

value "dnf_and ([[a,b], [c,d]]) ([[v,w], [x,y]])"

lemma cnf_to_bool_set: "cnf_to_bool f cnf \<longleftrightarrow> (\<forall> c \<in> set cnf. (case c of Pos a \<Rightarrow> f a | Neg a \<Rightarrow> \<not> f a))"
  proof(induction cnf)
  case Nil thus ?case by simp
  next
  case Cons thus ?case by (simp split: negation_type.split)
  qed
lemma dnf_to_bool_set: "dnf_to_bool \<gamma> dnf \<longleftrightarrow> (\<exists> d \<in> set dnf. cnf_to_bool \<gamma> d)"
  proof(induction dnf)
  case Nil thus ?case by simp
  next
  case (Cons d d1) thus ?case by(simp)
  qed

lemma dnf_to_bool_seteq: "set ` set d1 = set ` set d2 \<Longrightarrow> dnf_to_bool \<gamma> d1 \<longleftrightarrow> dnf_to_bool \<gamma> d2"
  proof -
    assume assm: "set ` set d1 = set ` set d2"
    have helper1: "\<And>P d. (\<exists>d\<in>set d. \<forall>c\<in>set d. P c) \<longleftrightarrow> (\<exists>d\<in>set ` set d. \<forall>c\<in>d. P c)" by blast
    from assm show ?thesis
      apply(simp add: dnf_to_bool_set cnf_to_bool_set)
      apply(subst helper1)
      apply(subst helper1)
      apply(simp)
      done
  qed

lemma dnf_and_correct: "dnf_to_bool \<gamma> (dnf_and d1 d2) \<longleftrightarrow> dnf_to_bool \<gamma> d1 \<and> dnf_to_bool \<gamma> d2"
 apply(simp add: dnf_and_def)
 apply(induction d1)
  apply(simp)
 apply(simp add: dnf_to_bool_append)
 apply(simp add: dnf_to_bool_set cnf_to_bool_set)
 by (meson UnCI UnE)

lemma dnf_and_symmetric: "dnf_to_bool \<gamma> (dnf_and d1 d2) \<longleftrightarrow> dnf_to_bool \<gamma> (dnf_and d2 d1)"
  using dnf_and_correct by blast

 
subsubsection\<open>inverting a DNF\<close>
  text\<open>Example\<close>
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
  
  text\<open>this is how @{const listprepend} works:\<close>
  lemma "\<not> dnf_to_bool \<gamma> (listprepend [] ds)" by(simp)
  lemma "dnf_to_bool \<gamma> (listprepend [a] ds) \<longleftrightarrow> dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds" by(simp add: map_a_and)
  lemma "dnf_to_bool \<gamma> (listprepend [a, b] ds) \<longleftrightarrow> (dnf_to_bool \<gamma> [[a]] \<and> dnf_to_bool \<gamma> ds) \<or> (dnf_to_bool \<gamma> [[b]] \<and> dnf_to_bool \<gamma> ds)" 
    by(simp add: map_a_and dnf_to_bool_append)
  
  
  text\<open>We use @{text "\<exists>"} to model the big @{text "\<or>"} operation\<close>
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
  
  lemma dnf_not: "dnf_to_bool \<gamma> (dnf_not d) \<longleftrightarrow> \<not> dnf_to_bool \<gamma> d"
    apply(induction d)
     apply(simp_all)
    apply(simp add: listprepend_correct)
    apply(simp add: cnf_invert_singelton cnf_singleton_false)
    done

subsubsection\<open>Optimizing\<close>
  (*there is probably a way better way to represent the set in the Collection framework
    A list of lists can be quite inefficient
    A better datastructure can help as we actually only use a set of sets*)
  definition optimize_dfn :: "'a dnf \<Rightarrow> 'a dnf" where
    "optimize_dfn dnf = map remdups (remdups dnf)"

  lemma "dnf_to_bool f (optimize_dfn dnf) = dnf_to_bool f dnf"
    unfolding optimize_dfn_def
    apply(rule dnf_to_bool_seteq)
    apply(simp)
    by (metis image_cong image_image set_remdups)

end
