section\<open>Repeat finitely Until it Stabilizes\<close>
theory Repeat_Stabilize
imports Main
begin

text\<open>Repeating something a number of times\<close>


text\<open>Iterating a function at most @{term n} times (first parameter) until it stabilizes.\<close>
fun repeat_stabilize :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "repeat_stabilize 0 _ v = v" |
  "repeat_stabilize (Suc n) f v = (let v_new = f v in if v = v_new then v else repeat_stabilize n f v_new)"

lemma repeat_stabilize_funpow: "repeat_stabilize n f v = (f^^n) v"
  proof(induction n arbitrary: v)
  case (Suc n)
    have "f v = v \<Longrightarrow> (f^^n) v = v" by(induction n) simp_all
    with Suc show ?case by(simp add: Let_def funpow_swap1)
  qed(simp)

lemma repeat_stabilize_induct: "(P m) \<Longrightarrow> (\<And>m. P m \<Longrightarrow> P (f m)) \<Longrightarrow> P (repeat_stabilize n f m)"
  apply(simp add: repeat_stabilize_funpow)
  apply(induction n)
   by(simp)+


end