section {* Relations interpreted as Directed Graphs *}
theory Digraph_Basic
imports   
  "Misc"
  "Refine_Util"
  "~~/src/HOL/Library/Omega_Words_Fun"
begin

text \<open>
  This theory contains some basic graph theory on directed graphs which are 
  modeled as a relation between nodes. 

  The theory here is very fundamental, and 
  also used by non-directly graph-related applications like the theory of 
  tail-recursion in the Refinement Framework. Thus, we decided to put it 
  in the basic theories of the refinement framework.
\<close>


text {* Directed graphs are modeled as a relation on nodes *}
type_synonym 'v digraph = "('v\<times>'v) set"

locale digraph = fixes E :: "'v digraph"

subsection {* Paths *}
text {* Path are modeled as list of nodes, the last node of a path is not included
  into the list. This formalization allows for nice concatenation and splitting
  of paths. *}
inductive path :: "'v digraph \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" for E where
  path0: "path E u [] u"
| path_prepend: "\<lbrakk> (u,v)\<in>E; path E v l w \<rbrakk> \<Longrightarrow> path E u (u#l) w"

lemma path1: "(u,v)\<in>E \<Longrightarrow> path E u [u] v"
  by (auto intro: path.intros)

lemma path_empty_conv[simp]:
  "path E u [] v \<longleftrightarrow> u=v"
  by (auto intro: path0 elim: path.cases)

inductive_cases path_uncons: "path E u (u'#l) w"
inductive_simps path_cons_conv: "path E u (u'#l) w"

lemma path_no_edges[simp]: "path {} u p v \<longleftrightarrow> (u=v \<and> p=[])"
  by (cases p) (auto simp: path_cons_conv)

lemma path_conc: 
  assumes P1: "path E u la v" 
  assumes P2: "path E v lb w"
  shows "path E u (la@lb) w"
  using P1 P2 apply induct 
  by (auto intro: path.intros)
  
lemma path_append:
  "\<lbrakk> path E u l v; (v,w)\<in>E \<rbrakk> \<Longrightarrow> path E u (l@[v]) w"
  using path_conc[OF _ path1] .

lemma path_unconc:
  assumes "path E u (la@lb) w"
  obtains v where "path E u la v" and "path E v lb w"
  using assms 
  thm path.induct
  apply (induct u "la@lb" w arbitrary: la lb rule: path.induct)
  apply (auto intro: path.intros elim!: list_Cons_eq_append_cases)
  done

lemma path_conc_conv: 
  "path E u (la@lb) w \<longleftrightarrow> (\<exists>v. path E u la v \<and> path E v lb w)"
  by (auto intro: path_conc elim: path_unconc)

lemma (in -) path_append_conv: "path E u (p@[v]) w \<longleftrightarrow> (path E u p v \<and> (v,w)\<in>E)"
  by (simp add: path_cons_conv path_conc_conv)

lemmas path_simps = path_empty_conv path_cons_conv path_conc_conv


lemmas path_trans[trans] = path_prepend path_conc path_append
lemma path_from_edges: "\<lbrakk>(u,v)\<in>E; (v,w)\<in>E\<rbrakk> \<Longrightarrow> path E u [u] v" 
  by (auto simp: path_simps)


lemma path_edge_cases[case_names no_use split]: 
  assumes "path (insert (u,v) E) w p x"
  obtains 
    "path E w p x" 
  | p1 p2 where "path E w p1 u" "path (insert (u,v) E) v p2 x"
  using assms
  apply induction
  apply simp
  apply (clarsimp)
  apply (metis path_simps path_cons_conv)
  done

lemma path_edge_rev_cases[case_names no_use split]: 
  assumes "path (insert (u,v) E) w p x"
  obtains 
    "path E w p x" 
  | p1 p2 where "path (insert (u,v) E) w p1 u" "path E v p2 x"
  using assms
  apply (induction p arbitrary: x rule: rev_induct)
  apply simp
  apply (clarsimp simp: path_cons_conv path_conc_conv)
  apply (metis path_simps path_append_conv)
  done


lemma path_mono: 
  assumes S: "E\<subseteq>E'" 
  assumes P: "path E u p v" 
  shows "path E' u p v"
  using P
  apply induction
  apply simp
  using S
  apply (auto simp: path_cons_conv)
  done

lemma path_is_rtrancl: 
  assumes "path E u l v"
  shows "(u,v)\<in>E\<^sup>*"
  using assms 
  by induct auto

lemma rtrancl_is_path:
  assumes "(u,v)\<in>E\<^sup>*"
  obtains l where "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)

lemma path_is_trancl: 
  assumes "path E u l v"
  and "l\<noteq>[]"
  shows "(u,v)\<in>E\<^sup>+"
  using assms 
  apply induct
  apply auto []
  apply (case_tac l)
  apply auto
  done

lemma trancl_is_path:
  assumes "(u,v)\<in>E\<^sup>+"
  obtains l where "l\<noteq>[]" and "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)

lemma path_nth_conv: "path E u p v \<longleftrightarrow> (let p'=p@[v] in
  u=p'!0 \<and>
  (\<forall>i<length p' - 1. (p'!i,p'!Suc i)\<in>E))"
  apply (induct p arbitrary: v rule: rev_induct)
  apply (auto simp: path_conc_conv path_cons_conv nth_append)
  done

lemma path_mapI:
  assumes "path E u p v"
  shows "path (pairself f ` E) (f u) (map f p) (f v)"
  using assms
  apply induction
  apply (simp)
  apply (force simp: path_cons_conv)
  done

lemma path_restrict: 
  assumes "path E u p v" 
  shows "path (E \<inter> set p \<times> insert v (set (tl p))) u p v"
  using assms
proof induction
  print_cases
  case (path_prepend u v p w)
  from path_prepend.IH have "path (E \<inter> set (u#p) \<times> insert w (set p)) v p w"
    apply (rule path_mono[rotated])
    by (cases p) auto
  thus ?case using `(u,v)\<in>E`
    by (cases p) (auto simp add: path_cons_conv)
qed auto

lemma path_restrict_closed:
  assumes CLOSED: "E``D \<subseteq> D"
  assumes I: "v\<in>D" and P: "path E v p v'"
  shows "path (E\<inter>D\<times>D) v p v'"
  using P CLOSED I
  by induction (auto simp: path_cons_conv)


lemma path_set_induct:
  assumes "path E u p v" and "u\<in>I" and "E``I \<subseteq> I"
  shows "set p \<subseteq> I"
  using assms
  by (induction rule: path.induct) auto

lemma path_nodes_reachable: "path E u p v \<Longrightarrow> insert v (set p) \<subseteq> E\<^sup>*``{u}"
  apply (auto simp: in_set_conv_decomp path_cons_conv path_conc_conv)
  apply (auto dest!: path_is_rtrancl)
  done

lemma path_nodes_edges: "path E u p v \<Longrightarrow> set p \<subseteq> fst`E"
  by (induction rule: path.induct) auto

lemma path_tl_nodes_edges: 
  assumes "path E u p v"
  shows "set (tl p) \<subseteq> fst`E \<inter> snd`E"
proof -
  from path_nodes_edges[OF assms] have "set (tl p) \<subseteq> fst`E"
    by (cases p) auto

  moreover have "set (tl p) \<subseteq> snd`E"
    using assms
    apply (cases)
    apply simp
    apply simp
    apply (erule path_set_induct[where I = "snd`E"])
    apply auto
    done
  ultimately show ?thesis
    by auto
qed

lemma path_loop_shift: 
  assumes P: "path E u p u"
  assumes S: "v\<in>set p"
  obtains p' where "set p' = set p" "path E v p' v"
proof -
  from S obtain p1 p2 where [simp]: "p = p1@v#p2" by (auto simp: in_set_conv_decomp)
  from P obtain v' where A: "path E u p1 v" "(v, v') \<in> E" "path E v' p2 u" 
    by (auto simp: path_simps)
  hence "path E v (v#p2@p1) v" by (auto simp: path_simps)
  thus ?thesis using that[of "v#p2@p1"] by auto
qed

lemma path_hd:
  assumes "p \<noteq> []" "path E v p w"
  shows "hd p = v"
  using assms
  by (auto simp: path_cons_conv neq_Nil_conv)


lemma path_last_is_edge:
  assumes "path E x p y"
  and "p \<noteq> []"
  shows "(last p, y) \<in> E"
  using assms
  by (auto simp: neq_Nil_rev_conv path_simps)

lemma path_member_reach_end:
  assumes P: "path E x p y"
  and v: "v \<in> set p"
  shows "(v,y) \<in> E\<^sup>+"
  using assms 
  by (auto intro!: path_is_trancl simp: in_set_conv_decomp path_simps)

lemma path_tl_induct[consumes 2, case_names single step]:
  assumes P: "path E x p y"
  and NE: "x \<noteq> y"
  and S: "\<And>u. (x,u) \<in> E \<Longrightarrow> P x u"
  and ST: "\<And>u v. \<lbrakk>(x,u) \<in> E\<^sup>+; (u,v) \<in> E; P x u\<rbrakk> \<Longrightarrow> P x v"
  shows "P x y \<and> (\<forall> v \<in> set (tl p). P x v)"
proof -
  from P NE have "p \<noteq> []" by auto
  thus ?thesis using P
  proof (induction p arbitrary: y rule: rev_nonempty_induct)
    case (single u) hence "(x,y) \<in> E" by (simp add: path_cons_conv)
    with S show ?case by simp
  next
    case (snoc u us) hence "path E x us u" by (simp add: path_append_conv)
    with snoc path_is_trancl have 
      "P x u" "(x,u) \<in> E\<^sup>+" "\<forall>v \<in> set (tl us). P x v" 
      by simp_all
    moreover with snoc have "\<forall>v \<in> set (tl (us@[u])). P x v" by simp
    moreover from snoc have "(u,y) \<in> E" by (simp add: path_append_conv)
    ultimately show ?case by (auto intro: ST)
  qed
qed


lemma path_restrict_tl: 
  "\<lbrakk> u\<notin>R; path (E \<inter> UNIV \<times> -R) u p v \<rbrakk> \<Longrightarrow> path (rel_restrict E R) u p v"
  apply (induction p arbitrary: u)
  apply (auto simp: path_simps rel_restrict_def)
  done

lemma path1_restr_conv: "path (E\<inter>UNIV \<times> -R) u (x#xs) v 
  \<longleftrightarrow> (\<exists>w. w\<notin>R \<and> x=u \<and> (u,w)\<in>E \<and> path (rel_restrict E R) w xs v)"
proof -
  have 1: "rel_restrict E R \<subseteq> E \<inter> UNIV \<times> - R" by (auto simp: rel_restrict_def)

  show ?thesis
    by (auto simp: path_simps intro: path_restrict_tl path_mono[OF 1])
qed



lemma dropWhileNot_path:
  assumes "p \<noteq> []"
  and "path E w p x"
  and "v \<in> set p"
  and "dropWhile (op \<noteq> v) p = c"
  shows "path E v c x"
  using assms
proof (induction arbitrary: w c rule: list_nonempty_induct)
  case (single p) thus ?case by (auto simp add: path_simps)
next
  case (cons p ps) hence [simp]: "w = p" by (simp add: path_cons_conv)
  show ?case
  proof (cases "p=v")
    case True with cons show ?thesis by simp
  next
    case False with cons have "c = dropWhile (op\<noteq> v) ps" by simp
    moreover from cons.prems obtain y where "path E y ps x" 
      using path_uncons by metis
    moreover from cons.prems False have "v \<in> set ps" by simp
    ultimately show ?thesis using cons.IH by metis
  qed
qed

lemma takeWhileNot_path:
  assumes "p \<noteq> []"
  and "path E w p x"
  and "v \<in> set p"
  and "takeWhile (op \<noteq> v) p = c"
  shows "path E w c v"
  using assms
proof (induction arbitrary: w c rule: list_nonempty_induct)
  case (single p) thus ?case by (auto simp add: path_simps)
next
  case (cons p ps) hence [simp]: "w = p" by (simp add: path_cons_conv)
  show ?case
  proof (cases "p=v")
    case True with cons show ?thesis by simp
  next
    case False with cons obtain c' where 
      "c' = takeWhile (op \<noteq> v) ps" and 
      [simp]: "c = p#c'"
      by simp_all
    moreover from cons.prems obtain y where 
      "path E y ps x" and "(w,y) \<in> E" 
      using path_uncons by metis+
    moreover from cons.prems False have "v \<in> set ps" by simp
    ultimately have "path E y c' v" using cons.IH by metis
    with `(w,y) \<in> E` show ?thesis by (auto simp add: path_cons_conv)
  qed
qed


subsection {* Infinite Paths *}
definition ipath :: "'q digraph \<Rightarrow> 'q word \<Rightarrow> bool"
  -- "Predicate for an infinite path in a digraph"
  where "ipath E r \<equiv> \<forall>i. (r i, r (Suc i))\<in>E"


lemma ipath_conc_conv: 
  "ipath E (u \<frown> v) \<longleftrightarrow> (\<exists>a. path E a u (v 0) \<and> ipath E v)"
  apply (auto simp: conc_def ipath_def path_nth_conv nth_append)
  apply (metis add_Suc_right diff_add_inverse not_add_less1)
  by (metis Suc_diff_Suc diff_Suc_Suc not_less_eq)

lemma ipath_iter_conv:
  assumes "p\<noteq>[]"
  shows "ipath E (p\<^sup>\<omega>) \<longleftrightarrow> (path E (hd p) p (hd p))"
proof (cases p)
  case Nil thus ?thesis using assms by simp
next
  case (Cons u p') hence PLEN: "length p > 0" by simp
  show ?thesis proof 
    assume "ipath E (iter (p))"
    hence "\<forall>i. (iter (p) i, iter (p) (Suc i)) \<in> E"
      unfolding ipath_def by simp
    hence "(\<forall>i<length p. (p!i,(p@[hd p])!Suc i)\<in>E)" 
      apply (simp add: assms)
      apply safe
      apply (drule_tac x=i in spec)
      apply simp
      apply (case_tac "Suc i = length p")
      apply (simp add: Cons)
      apply (simp add: nth_append)
      done
    thus "path E (hd p) p (hd p)"
      by (auto simp: path_nth_conv Cons nth_append nth_Cons')
  next
    assume "path E (hd p) p (hd p)"
    thus "ipath E (iter p)"
      apply (auto simp: path_nth_conv ipath_def assms Let_def)
      apply (drule_tac x="i mod length p" in spec)
      apply (auto simp: nth_append assms split: split_if_asm)
      apply (metis less_not_refl mod_Suc)
      by (metis PLEN diff_self_eq_0 mod_Suc nth_Cons_0 
        semiring_numeral_div_class.pos_mod_bound)
  qed
qed

lemma ipath_to_rtrancl:
  assumes R: "ipath E r"
  assumes I: "i1\<le>i2"
  shows "(r i1,r i2)\<in>E\<^sup>*"
  using I
proof (induction i2)
  case (Suc i2)
  show ?case proof (cases "i1=Suc i2")
    assume "i1\<noteq>Suc i2"
    with Suc have "(r i1,r i2)\<in>E\<^sup>*" by auto
    also from R have "(r i2,r (Suc i2))\<in>E" unfolding ipath_def by auto
    finally show ?thesis .
  qed simp
qed simp
    
lemma ipath_to_trancl:
  assumes R: "ipath E r"
  assumes I: "i1<i2"
  shows "(r i1,r i2)\<in>E\<^sup>+"
proof -
  from R have "(r i1,r (Suc i1))\<in>E"
    by (auto simp: ipath_def)
  also have "(r (Suc i1),r i2)\<in>E\<^sup>*"
    using ipath_to_rtrancl[OF R,of "Suc i1" i2] I by auto
  finally (rtrancl_into_trancl2) show ?thesis .
qed

lemma run_limit_two_connectedI:
  assumes A: "ipath E r" 
  assumes B: "a \<in> limit r" "b\<in>limit r"
  shows "(a,b)\<in>E\<^sup>+"
proof -
  from B have "{a,b} \<subseteq> limit r" by simp
  with A show ?thesis
    by (metis ipath_to_trancl two_in_limit_iff)
qed


lemma ipath_subpath:
  assumes P: "ipath E r"
  assumes LE: "l\<le>u"
  shows "path E (r l) (map r [l..<u]) (r u)"
  using LE
proof (induction "u-l" arbitrary: u l)
  case (Suc n)
  note IH=Suc.hyps(1)
  from `Suc n = u-l` `l\<le>u` obtain u' where [simp]: "u=Suc u'" 
    and A: "n=u'-l" "l \<le> u'" 
    by (cases u) auto
    
  note IH[OF A]
  also from P have "(r u',r u)\<in>E"
    by (auto simp: ipath_def)
  finally show ?case using `l \<le> u'` by (simp add: upt_Suc_append)
qed auto  

lemma ipath_restrict_eq: "ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r \<longleftrightarrow> ipath E r"
  unfolding ipath_def
  by (auto simp: relpow_fun_conv rtrancl_power)
lemma ipath_restrict: "ipath E r \<Longrightarrow> ipath (E \<inter> (E\<^sup>*``{r 0} \<times> E\<^sup>*``{r 0})) r"
  by (simp add: ipath_restrict_eq)


lemma ipathI[intro?]: "\<lbrakk>\<And>i. (r i, r (Suc i)) \<in> E\<rbrakk> \<Longrightarrow> ipath E r"
  unfolding ipath_def by auto

lemma ipathD: "ipath E r \<Longrightarrow> (r i, r (Suc i)) \<in> E"
  unfolding ipath_def by auto

lemma ipath_in_Domain: "ipath E r \<Longrightarrow> r i \<in> Domain E"
  unfolding ipath_def by auto

lemma ipath_in_Range: "\<lbrakk>ipath E r; i\<noteq>0\<rbrakk> \<Longrightarrow> r i \<in> Range E"
  unfolding ipath_def by (cases i) auto

lemma ipath_suffix: "ipath E r \<Longrightarrow> ipath E (suffix i r)"
  unfolding suffix_def ipath_def by auto

subsection {* Strongly Connected Components *}

text {* A strongly connected component is a maximal mutually connected set 
  of nodes *}
definition is_scc :: "'q digraph \<Rightarrow> 'q set \<Rightarrow> bool"
  where "is_scc E U \<longleftrightarrow> U\<times>U\<subseteq>E\<^sup>* \<and> (\<forall>V. V\<supset>U \<longrightarrow> \<not> (V\<times>V\<subseteq>E\<^sup>*))"

lemma scc_non_empty[simp]: "\<not>is_scc E {}" unfolding is_scc_def by auto

lemma scc_non_empty'[simp]: "is_scc E U \<Longrightarrow> U\<noteq>{}" unfolding is_scc_def by auto

lemma is_scc_closed: 
  assumes SCC: "is_scc E U"
  assumes MEM: "x\<in>U"
  assumes P: "(x,y)\<in>E\<^sup>*" "(y,x)\<in>E\<^sup>*"
  shows "y\<in>U"
proof -
  from SCC MEM P have "insert y U \<times> insert y U \<subseteq> E\<^sup>*"
    unfolding is_scc_def
    apply clarsimp
    apply rule
    apply clarsimp_all
    apply (erule disjE1)
    apply clarsimp
    apply (metis in_mono mem_Sigma_iff rtrancl_trans)
    apply auto []
    apply (erule disjE1)
    apply clarsimp
    apply (metis in_mono mem_Sigma_iff rtrancl_trans)
    apply auto []
    done
  with SCC show ?thesis unfolding is_scc_def by blast
qed

lemma is_scc_connected:
  assumes SCC: "is_scc E U"
  assumes MEM: "x\<in>U" "y\<in>U"
  shows "(x,y)\<in>E\<^sup>*"
  using assms unfolding is_scc_def by auto

text {* In the following, we play around with alternative characterizations, and
  prove them all equivalent .*}

text {* A common characterization is to define an equivalence relation 
  ,,mutually connected'' on nodes, and characterize the SCCs as its 
  equivalence classes: *}

definition mconn :: "('a\<times>'a) set \<Rightarrow> ('a \<times> 'a) set"
  -- "Mutually connected relation on nodes"
  where "mconn E = E\<^sup>* \<inter> (E\<inverse>)\<^sup>*"

lemma mconn_pointwise:
   "mconn E = {(u,v). (u,v)\<in>E\<^sup>* \<and> (v,u)\<in>E\<^sup>*}"
  by (auto simp add: mconn_def rtrancl_converse)

text {* @{text "mconn"} is an equivalence relation: *}
lemma mconn_refl[simp]: "Id\<subseteq>mconn E"
  by (auto simp add: mconn_def)

lemma mconn_sym: "mconn E = (mconn E)\<inverse>"
  by (auto simp add: mconn_pointwise)

lemma mconn_trans: "mconn E O mconn E = mconn E"
  by (auto simp add: mconn_def)

lemma mconn_refl': "refl (mconn E)"
  by (auto intro: refl_onI simp: mconn_pointwise)

lemma mconn_sym': "sym (mconn E)"
  by (auto intro: symI simp: mconn_pointwise)

lemma mconn_trans': "trans (mconn E)"
  by (metis mconn_def trans_Int trans_rtrancl)

lemma mconn_equiv: "equiv UNIV (mconn E)"
  using mconn_refl' mconn_sym' mconn_trans'
  by (rule equivI)


lemma is_scc_mconn_eqclasses: "is_scc E U \<longleftrightarrow> U \<in> UNIV // mconn E"
  -- "The strongly connected components are the equivalence classes of the 
    mutually-connected relation on nodes"
proof
  assume A: "is_scc E U"
  then obtain x where "x\<in>U" unfolding is_scc_def by auto
  hence "U = mconn E `` {x}" using A
    unfolding mconn_pointwise is_scc_def
    apply clarsimp
    apply rule
    apply auto []
    apply clarsimp
    by (metis A is_scc_closed)
  thus "U \<in> UNIV // mconn E"
    by (auto simp: quotient_def)
next
  assume "U \<in> UNIV // mconn E"
  thus "is_scc E U"
    by (auto simp: is_scc_def mconn_pointwise quotient_def)
qed

(* For presentation in the paper *)
lemma "is_scc E U \<longleftrightarrow> U \<in> UNIV // (E\<^sup>* \<inter> (E\<inverse>)\<^sup>*)"
  unfolding is_scc_mconn_eqclasses mconn_def by simp

text {* We can also restrict the notion of "reachability" to nodes
  inside the SCC
  *}

lemma find_outside_node:
  assumes "(u,v)\<in>E\<^sup>*"
  assumes "(u,v)\<notin>(E\<inter>U\<times>U)\<^sup>*"
  assumes "u\<in>U" "v\<in>U"
  shows "\<exists>u'. u'\<notin>U \<and> (u,u')\<in>E\<^sup>* \<and> (u',v)\<in>E\<^sup>*"
  using assms
  apply (induction)
  apply auto []
  apply clarsimp
  by (metis IntI mem_Sigma_iff rtrancl.simps)

lemma is_scc_restrict1:
  assumes SCC: "is_scc E U"
  shows "U\<times>U\<subseteq>(E\<inter>U\<times>U)\<^sup>*"
  using assms
  unfolding is_scc_def
  apply clarsimp
  apply (rule ccontr)
  apply (drule (2) find_outside_node[rotated])
  apply auto []
  by (metis is_scc_closed[OF SCC] mem_Sigma_iff rtrancl_trans subsetD)

lemma is_scc_restrict2:
  assumes SCC: "is_scc E U"
  assumes "V\<supset>U"
  shows "\<not> (V\<times>V\<subseteq>(E\<inter>V\<times>V)\<^sup>*)"
  using assms
  unfolding is_scc_def
  apply clarsimp
  using rtrancl_mono[of "E \<inter> V \<times> V" "E"]
  apply clarsimp
  apply blast
  done

lemma is_scc_restrict3: 
  assumes SCC: "is_scc E U"
  shows "((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
  apply auto
  by (metis assms is_scc_closed is_scc_connected rtrancl_trans)
  
lemma is_scc_alt_restrict_path:
  "is_scc E U \<longleftrightarrow> U\<noteq>{} \<and>
    (U\<times>U \<subseteq> (E\<inter>U\<times>U)\<^sup>*) \<and> ((E\<^sup>*``((E\<^sup>*``U) - U)) \<inter> U = {})"
  apply rule
  apply (intro conjI)
  apply simp
  apply (blast dest: is_scc_restrict1)
  apply (blast dest: is_scc_restrict3)
  
  unfolding is_scc_def
  apply rule
  apply clarsimp
  apply (metis (full_types) Int_lower1 in_mono mem_Sigma_iff rtrancl_mono_mp)
  apply blast
  done

lemma is_scc_pointwise:
  "is_scc E U \<longleftrightarrow> 
    U\<noteq>{}
  \<and> (\<forall>u\<in>U. \<forall>v\<in>U. (u,v)\<in>(E\<inter>U\<times>U)\<^sup>*) 
  \<and> (\<forall>u\<in>U. \<forall>v. (v\<notin>U \<and> (u,v)\<in>E\<^sup>*) \<longrightarrow> (\<forall>u'\<in>U. (v,u')\<notin>E\<^sup>*))"
  -- "Alternative, pointwise characterization"
  unfolding is_scc_alt_restrict_path
  by blast  

lemma is_scc_unique:
  assumes SCC: "is_scc E scc" "is_scc E scc'"
  and v: "v \<in> scc" "v \<in> scc'"
  shows "scc = scc'"
proof -
  from SCC have "scc = scc' \<or> scc \<inter> scc' = {}"
    using quotient_disj[OF mconn_equiv]
    by (simp add: is_scc_mconn_eqclasses)
  with v show ?thesis by auto
qed

lemma is_scc_ex1:
  "\<exists>!scc. is_scc E scc \<and> v \<in> scc"
proof (rule ex1I, rule conjI)
  let ?scc = "mconn E `` {v}"
  have "?scc \<in> UNIV // mconn E" by (auto intro: quotientI)
  thus "is_scc E ?scc" by (simp add: is_scc_mconn_eqclasses)
  moreover show "v \<in> ?scc" by (blast intro: refl_onD[OF mconn_refl'])
  ultimately show "\<And>scc. is_scc E scc \<and> v \<in> scc \<Longrightarrow> scc = ?scc"
    by (metis is_scc_unique)
qed

lemma is_scc_ex:
  "\<exists>scc. is_scc E scc \<and> v \<in> scc"
  by (metis is_scc_ex1)

lemma is_scc_connected':
  "\<lbrakk>is_scc E scc; x \<in> scc; y \<in> scc\<rbrakk> \<Longrightarrow> (x,y)\<in>(Restr E scc)\<^sup>*"
  unfolding is_scc_pointwise
  by blast

definition scc_of :: "('v\<times>'v) set \<Rightarrow> 'v \<Rightarrow> 'v set"
  where
  "scc_of E v = (THE scc. is_scc E scc \<and> v \<in> scc)"

lemma scc_of_is_scc[simp]:
  "is_scc E (scc_of E v)"
  using is_scc_ex1[of E v]
  by (auto dest!: theI' simp: scc_of_def)

lemma node_in_scc_of_node[simp]:
  "v \<in> scc_of E v"
  using is_scc_ex1[of E v]
  by (auto dest!: theI' simp: scc_of_def)

lemma scc_of_unique:
  assumes "w \<in> scc_of E v"
  shows "scc_of E v = scc_of E w"
proof -
  have "is_scc E (scc_of E v)" by simp
  moreover note assms
  moreover have "is_scc E (scc_of E w)" by simp
  moreover have "w \<in> scc_of E w" by simp
  ultimately show ?thesis using is_scc_unique by metis
qed

end
