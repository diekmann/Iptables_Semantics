(*  Title:      IP_Partition_Preliminaries
    Authors:    Cornelius Diekmann, Max Haslbeck
*)
(*SetPartitioning.thy
  Original Author: Max Haslbeck, 2015*)
section\<open>Partition a Set by a Specific Constraint\<close>
theory IP_Partition_Preliminaries
imports Main
begin

text\<open>Will be used for the IP address space partition of a firewall.
    However, this file is completely generic in terms of sets, it only imports Main.

    It will be used in @{file "../Service_Matrix.thy"}.
    Core idea: This file partitions @{typ "'a set set"} by some magic condition.
    Later, we will show that this magic condition implies that all IPs that have been grouped
    by the magic condition show the same behaviour for a simple firewall.\<close>

(* disjoint, ipPartition definitions *)

definition disjoint :: "'a set set \<Rightarrow> bool" where
  "disjoint ts \<equiv> \<forall>A \<in> ts. \<forall>B \<in> ts. A \<noteq> B \<longrightarrow> A \<inter> B = {}"

text_raw\<open>We will call two partitioned sets \emph{complete} iff @{term "\<Union> ss = \<Union> ts"}.\<close>

text\<open>The condition we use to partition a set. If this holds and 
      @{term A} is the set of IP addresses in each rule in a firewall,
      then @{term B} is a partition of @{term "\<Union> A"} where each member has the same behavior
      w.r.t the firewall ruleset.\<close>
text\<open>@{term A} is the carrier set and @{term B}* should be a partition of @{term "\<Union> A"} 
     which fulfills the following condition:\<close>
definition ipPartition :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "ipPartition A B \<equiv> \<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b = {} \<or> b \<subseteq> a"

definition disjoint_list :: "'a set list \<Rightarrow> bool" where
  "disjoint_list ls \<equiv> distinct ls \<and> disjoint (set ls)"

context begin
  (*internal*)
  private fun disjoint_list_rec :: "'a set list \<Rightarrow> bool" where
    "disjoint_list_rec [] = True" |
    "disjoint_list_rec (x#xs) = (x \<inter> \<Union> set xs = {} \<and> disjoint_list_rec xs)"
  
  private lemma disjoint_equi: "disjoint_list_rec ts \<Longrightarrow> disjoint (set ts)"
    apply(induction ts)
     apply(simp_all add: disjoint_def)
    by fast
  
  private lemma disjoint_list_disjoint_list_rec: "disjoint_list ts \<Longrightarrow> disjoint_list_rec ts"
    apply(induction ts)
     apply(simp_all add: disjoint_list_def disjoint_def)
    by fast
  
  private definition addSubsetSet :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
    "addSubsetSet s ts = insert (s - \<Union>ts) ((op \<inter> s) ` ts) \<union> ((\<lambda>x. x - s) ` ts)"
  
  private fun partitioning :: "'a set list \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
    "partitioning [] ts = ts" |
    "partitioning (s#ss) ts = partitioning ss (addSubsetSet s ts)"
  
  
  text\<open>simple examples\<close>
  lemma "partitioning [{1::nat,2},{3,4},{5,6,7},{6},{10}] {} = {{10}, {6}, {5, 7}, {}, {3, 4}, {1, 2}}" by eval
  lemma "\<Union> {{1::nat,2},{3,4},{5,6,7},{6},{10}} = \<Union> (partitioning [{1,2},{3,4},{5,6,7},{6},{10}] {})" by eval
  lemma "disjoint (partitioning [{1::nat,2},{3,4},{5,6,7},{6},{10}] {})" by eval
  lemma "ipPartition {{1::nat,2},{3,4},{5,6,7},{6},{10}} (partitioning [{1::nat,2},{3,4},{5,6,7},{6},{10}] {})" by eval
  
  lemma "ipPartition A {}" by(simp add: ipPartition_def)
  
  lemma ipPartitionUnion: "ipPartition As Cs \<and> ipPartition Bs Cs \<longleftrightarrow> ipPartition (As \<union> Bs) Cs"
    unfolding ipPartition_def by fast
  
  private lemma disjointAddSubset: "disjoint ts \<Longrightarrow> disjoint (addSubsetSet a ts)" 
    by (auto simp add: disjoint_def addSubsetSet_def)
  
  private lemma coversallAddSubset:"\<Union> (insert a ts) = \<Union> (addSubsetSet a ts)" 
    by (auto simp add: addSubsetSet_def)
  
  private lemma ipPartioningAddSubset0: "disjoint ts \<Longrightarrow> ipPartition ts (addSubsetSet a ts)"
    apply(simp add: addSubsetSet_def ipPartition_def)
    apply(safe)
      apply blast
     apply(simp_all add: disjoint_def)
     apply blast+
    done
  
  private lemma ipPartitioningAddSubset1: "disjoint ts \<Longrightarrow> ipPartition (insert a ts) (addSubsetSet a ts)"
    apply(simp add: addSubsetSet_def ipPartition_def)
    apply(safe)
      apply blast
     apply(simp_all add: disjoint_def)
     apply blast+
  done
  
  private lemma addSubsetSetI:
    "s - \<Union>ts \<in> addSubsetSet s ts"
    "t \<in> ts \<Longrightarrow> s \<inter> t \<in> addSubsetSet s ts"
    "t \<in> ts \<Longrightarrow> t - s \<in> addSubsetSet s ts"
  unfolding addSubsetSet_def by blast+
    
  private lemma addSubsetSetE:
    assumes "A \<in> addSubsetSet s ts"
    obtains "A = s - \<Union>ts" | T where "T \<in> ts" "A = s \<inter> T" | T where "T \<in> ts" "A = T - s"
    using assms unfolding addSubsetSet_def by blast
  
  private lemma Union_addSubsetSet: "\<Union>addSubsetSet b As = b \<union> \<Union>As"
    unfolding addSubsetSet_def by auto
  
  private lemma addSubsetSetCom: "addSubsetSet a (addSubsetSet b As) = addSubsetSet b (addSubsetSet a As)"
  proof -
    {
      fix A a b assume "A \<in> addSubsetSet a (addSubsetSet b As)"
      hence "A \<in> addSubsetSet b (addSubsetSet a As)"
      apply (rule addSubsetSetE)
      proof(goal_cases)
        case 1
        assume "A = a - \<Union>addSubsetSet b As"
        hence "A = (a - \<Union>As) - b" by (auto simp add: Union_addSubsetSet)
        thus ?thesis by (auto intro: addSubsetSetI)
      next
        case (2 T)
        have "A = b \<inter> (a - \<Union>As) \<or> (\<exists>S\<in>As. A = b \<inter> (a \<inter> S)) \<or> (\<exists>S\<in>As. A = (a \<inter> S) - b)"
          by (rule addSubsetSetE[OF 2(1)]) (auto simp: 2(2))
        thus ?thesis by (blast intro: addSubsetSetI)
      next
        case (3 T)
        have "A = b - \<Union>addSubsetSet a As \<or> (\<exists>S\<in>As. A = b \<inter> (S - a)) \<or> (\<exists>S\<in>As. A = (S - a) - b)"
          by (rule addSubsetSetE[OF 3(1)]) (auto simp: 3(2) Union_addSubsetSet)
        thus ?thesis by (blast intro: addSubsetSetI)
      qed
    }
    thus ?thesis by blast
  qed
  
  private lemma ipPartitioningAddSubset2: "ipPartition {a} (addSubsetSet a ts)"
    apply(simp add: addSubsetSet_def ipPartition_def) 
    by blast
  
  private lemma disjointPartitioning_helper :"disjoint As \<Longrightarrow> disjoint (partitioning ss As)"
    proof(induction ss arbitrary: As)
    case Nil thus ?case by(simp)
    next
    case (Cons s ss)
      from Cons.prems disjointAddSubset have d: "disjoint (addSubsetSet s As)" by fast
      from Cons.IH d have "disjoint (partitioning ss (addSubsetSet s As))" .
      thus ?case by simp
    qed
  
  private lemma disjointPartitioning: "disjoint (partitioning ss {})"
    proof -
      have "disjoint {}" by(simp add: disjoint_def)
      from this disjointPartitioning_helper show ?thesis by fast
    qed
  
  private lemma coversallPartitioning:"\<Union> (set ts) = \<Union> (partitioning ts {})"
  proof -
    have "\<Union> (set ts \<union> As) = \<Union> (partitioning ts As)" for As
    apply(induction ts arbitrary: As)
     apply(simp_all)
    by (metis Union_addSubsetSet sup_left_commute)
    thus ?thesis by (metis sup_bot.right_neutral)
  qed
  
  private lemma "\<Union> As = \<Union> Bs \<Longrightarrow> ipPartition As Bs \<Longrightarrow> ipPartition As (addSubsetSet a Bs)"
    by(auto simp add: ipPartition_def addSubsetSet_def)
  
  private lemma ipPartitionSingleSet: "ipPartition {t} (addSubsetSet t Bs) 
               \<Longrightarrow> ipPartition {t} (partitioning ts (addSubsetSet t Bs))"
    apply(induction ts arbitrary: Bs t)
     apply(simp_all)
    by (metis addSubsetSetCom ipPartitioningAddSubset2)
  
  private lemma ipPartitioning_helper: "disjoint As \<Longrightarrow> ipPartition (set ts) (partitioning ts As)"
    proof(induction ts arbitrary: As)
    case Nil thus ?case by(simp add: ipPartition_def)
    next
    case (Cons t ts)
      from Cons.prems ipPartioningAddSubset0 have d: "ipPartition As (addSubsetSet t As)" by blast
      from Cons.prems Cons.IH d disjointAddSubset ipPartitioningAddSubset1
      have e: "ipPartition (set ts) (partitioning ts (addSubsetSet t As))" by blast
      from ipPartitioningAddSubset2 Cons.prems 
      have "ipPartition {t} (addSubsetSet t As)" by blast 
      from this Cons.prems ipPartitionSingleSet
      have f: "ipPartition {t} (partitioning ts (addSubsetSet t As))" by fast
      have "set (t#ts) = insert t (set ts)" by auto
      from ipPartitionUnion have "\<And> As Bs Cs. ipPartition As Cs \<Longrightarrow> ipPartition Bs Cs \<Longrightarrow> ipPartition (As \<union> Bs) Cs" by fast
      with this e f 
      have "ipPartition (set (t # ts)) (partitioning ts (addSubsetSet t As))" by fastforce
      thus ?case by simp
   qed
  
  private lemma ipPartitioning: "ipPartition (set ts) (partitioning ts {})"
    proof -
      have "disjoint {}" by(simp add: disjoint_def)
      from this ipPartitioning_helper show ?thesis by fast
    qed
  
  (* OPTIMIZATION PROOFS *)
  
  private lemma inter_dif_help_lemma: "A \<inter> B = {}  \<Longrightarrow> B - S = B - (S - A)"
    by blast
  
  private lemma disjoint_list_lem: "disjoint_list ls \<Longrightarrow> \<forall>s \<in> set(ls). \<forall>t \<in> set(ls). s \<noteq> t \<longrightarrow> s \<inter> t = {}"
    proof(induction ls)
    qed(simp_all add: disjoint_list_def disjoint_def)
  
  private lemma disjoint_list_empty: "disjoint_list []"
    by (simp add: disjoint_list_def disjoint_def)
  
  private lemma disjoint_sublist: "disjoint_list (t#ts) \<Longrightarrow> disjoint_list ts"
    proof(induction ts arbitrary: t)
    qed(simp_all add: disjoint_list_empty disjoint_list_def disjoint_def)
  
  private fun intersection_list :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "intersection_list _ [] = []" |
    "intersection_list s (t#ts) = (s \<inter> t)#(intersection_list s ts)"
  
  private fun intersection_list_opt :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "intersection_list_opt _ [] = []" |
    "intersection_list_opt s (t#ts) = (s \<inter> t)#(intersection_list_opt (s - t) ts)"
  
  private lemma disjoint_subset: "disjoint A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<subseteq> a \<Longrightarrow> disjoint ((A - {a}) \<union> {b})"
    apply(simp add: disjoint_def)
    by blast
  
  private lemma disjoint_intersection: "disjoint A \<Longrightarrow> a \<in> A \<Longrightarrow> disjoint ({a \<inter> b} \<union> (A - {a}))"
    apply(simp add: disjoint_def)
    by(blast)
  
  private lemma intList_equi: "disjoint_list_rec ts \<Longrightarrow> intersection_list s ts = intersection_list_opt s ts"
    proof(induction ts)
    case Nil thus ?case by simp
    next
    case (Cons t ts)
    from Cons.prems have "intersection_list_opt s ts = intersection_list_opt (s - t) ts"
      proof(induction ts arbitrary: s t)
      case Nil thus ?case by simp
      next
      case Cons
      have "\<forall>t \<in> set ts. u \<inter> t = {} \<Longrightarrow> intersection_list_opt s ts = intersection_list_opt (s - u) ts"
        for u
        apply(induction ts arbitrary: s u)
         apply(simp_all)
        by (metis Diff_Int_distrib2 Diff_empty Diff_eq Un_Diff_Int sup_bot.right_neutral)
      with Cons show ?case
        apply(simp)
        by (metis Diff_Int_distrib2 Diff_empty Un_empty inf_sup_distrib1)
      qed
    with Cons show ?case by simp
    qed
  
  private fun difference_list :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "difference_list _ [] = []" |
    "difference_list s (t#ts) = (t - s)#(difference_list s ts)"
  
  private fun difference_list_opt :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "difference_list_opt _ [] = []" |
    "difference_list_opt s (t#ts) = (t - s)#(difference_list_opt (s - t) ts)"
  
  
  private lemma difList_equi: "disjoint_list_rec ts \<Longrightarrow> difference_list s ts = difference_list_opt s ts"
    proof(induction ts arbitrary: s)
    case Nil thus ?case by simp
    next
    case (Cons t ts)
      have difference_list_opt_lem0: "\<forall>t \<in> set(ts). u \<inter> t = {} \<Longrightarrow>
                                        difference_list_opt s ts = difference_list_opt (s - u) ts"
      for u proof(induction ts arbitrary: s u)
      case Cons thus ?case
         apply(simp_all add: inter_dif_help_lemma)
         by (metis Diff_Int_distrib2 Diff_eq Un_Diff_Int sup_bot.right_neutral)
      qed(simp)
      have "disjoint_list_rec (t # ts) \<Longrightarrow> difference_list_opt s ts = difference_list_opt (s - t) ts"
      proof(induction ts arbitrary: s t)
      case Cons thus ?case
         apply(simp_all add: difference_list_opt_lem0)
         by (metis Un_empty inf_sup_distrib1 inter_dif_help_lemma)
      qed(simp)
    with Cons show ?case by simp
  qed
   
  private fun partList0 :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partList0 s [] = []" |
    "partList0 s (t#ts) = (s \<inter> t)#((t - s)#(partList0 s ts))"
  
  private lemma partList0_set_equi: "set(partList0 s ts) = ((op \<inter> s) ` (set ts)) \<union> ((\<lambda>x. x - s) ` (set ts))"
    by(induction ts arbitrary: s) auto
  
  private lemma partList_sub_equi0: "set(partList0 s ts) =
                             set(difference_list s ts) \<union> set(intersection_list s ts)" 
    by(induction ts arbitrary: s) simp+
  
  private fun partList1 :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partList1 s [] = []" |
    "partList1 s (t#ts) = (s \<inter> t)#((t - s)#(partList1 (s - t) ts))"
  
  private lemma partList_sub_equi: "set(partList1 s ts) = 
                            set(difference_list_opt s ts) \<union> set(intersection_list_opt s ts)" 
    by(induction ts arbitrary: s) (simp_all)
  
  private lemma partList0_partList1_equi: "disjoint_list_rec ts \<Longrightarrow> set (partList0 s ts) = set (partList1 s ts)"
    by (simp add: partList_sub_equi partList_sub_equi0 intList_equi difList_equi)
  
  private fun partList2 :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partList2 s [] = []" |
    "partList2 s (t#ts) = (if s \<inter> t = {} then  (t#(partList2 (s - t) ts))
                                         else (s \<inter> t)#((t - s)#(partList2 (s - t) ts)))"
  
  private lemma partList2_empty: "partList2 {} ts = ts"
    by(induction ts) (simp_all)
   
  private lemma partList1_partList2_equi: "set(partList1 s ts) - {{}} = set(partList2 s ts) - {{}}"
    by(induction ts arbitrary: s) (auto)
  
  private fun partList3 :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partList3 s [] = []" |
    "partList3 s (t#ts) = (if s = {} then (t#ts) else
                            (if s \<inter> t = {} then (t#(partList3 (s - t) ts))
                                           else 
                              (if t - s = {} then (t#(partList3 (s - t) ts))
                                             else (t \<inter> s)#((t - s)#(partList3 (s - t) ts)))))"
  
  private lemma partList2_partList3_equi: "set(partList2 s ts) - {{}} = set(partList3 s ts) - {{}}"
    apply(induction ts arbitrary: s)
     apply(simp; fail)
    apply(simp add: partList2_empty)
    by blast
  
  fun partList4 :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partList4 s [] = []" |
    "partList4 s (t#ts) = (if s = {} then (t#ts) else
                            (if s \<inter> t = {} then (t#(partList4 s ts))
                                           else 
                              (if t - s = {} then (t#(partList4 (s - t) ts))
                                             else (t \<inter> s)#((t - s)#(partList4 (s - t) ts)))))"
  
  private lemma partList4: "partList4 s ts = partList3 s ts"
    apply(induction ts arbitrary: s)
     apply(simp; fail)
    apply (simp add: Diff_triv)
    done
  
  private lemma partList0_addSubsetSet_equi: "s \<subseteq> \<Union>(set ts) \<Longrightarrow> 
                                      addSubsetSet s (set ts) - {{}} = set(partList0 s ts) - {{}}"
    by(simp add: addSubsetSet_def partList0_set_equi)
  
  private fun partitioning_nontail :: "'a set list \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
    "partitioning_nontail [] ts = ts" |
    "partitioning_nontail (s#ss) ts = addSubsetSet s (partitioning_nontail ss ts)"
  
  private lemma partitioningCom: "addSubsetSet a (partitioning ss ts) = partitioning ss (addSubsetSet a ts)"
    apply(induction ss arbitrary: a ts)
     apply(simp; fail)
    apply(simp add: addSubsetSetCom)
  done
  
  private lemma partitioning_nottail_equi: "partitioning_nontail ss ts = partitioning ss ts"
    apply(induction ss arbitrary: ts)
     apply(simp; fail)
    apply(simp add: addSubsetSetCom partitioningCom)
  done
  
  fun partitioning1 :: "'a set list \<Rightarrow> 'a set list \<Rightarrow> 'a set list" where
    "partitioning1 [] ts = ts" |
    "partitioning1 (s#ss) ts = partList4 s (partitioning1 ss ts)"
  
  lemma partList4_empty: "{} \<notin> set ts \<Longrightarrow> {} \<notin> set (partList4 s ts)"
    apply(induction ts arbitrary: s)
     apply(simp; fail)
    by auto
  
  lemma partitioning1_empty0: "{} \<notin> set ts \<Longrightarrow> {} \<notin> set (partitioning1 ss ts)"
    apply(induction ss arbitrary: ts)
     apply(simp; fail)
    apply(simp add: partList4_empty)
    done
  
  lemma partitioning1_empty1: "{} \<notin> set ts \<Longrightarrow> 
                                set(partitioning1 ss ts) - {{}} = set(partitioning1 ss ts)"
    by(simp add: partitioning1_empty0)
  
  lemma partList4_subset: "a \<subseteq> \<Union>(set ts) \<Longrightarrow> a \<subseteq> \<Union>set (partList4 b ts)"
    apply(simp add: partList4)
    apply(induction ts arbitrary: a b)
     apply(simp; fail)
    apply(simp)
    by fast
  
  private lemma "a \<noteq> {} \<Longrightarrow> disjoint_list_rec (a # ts) \<longleftrightarrow> disjoint_list_rec ts \<and> a \<inter> \<Union> (set ts) = {}" by auto
  
  lemma partList4_complete0: "s \<subseteq> \<Union> set ts \<Longrightarrow> \<Union> set (partList4 s ts) = \<Union> set ts"
  unfolding partList4
  proof(induction ts arbitrary: s)
    case Nil thus ?case by(simp)
    next
    case Cons thus ?case by (simp add: Diff_subset_conv Un_Diff_Int inf_sup_aci(7) sup.commute)
  qed
  
  private lemma partList4_disjoint: "s \<subseteq> \<Union> set ts \<Longrightarrow> disjoint_list_rec ts \<Longrightarrow> 
                             disjoint_list_rec (partList4 s ts)"
    apply(induction ts arbitrary: s)
     apply(simp; fail)
    apply(simp add: Diff_subset_conv)
    apply(rule conjI)
     apply (metis Diff_subset_conv Int_absorb1 Int_lower2 Un_absorb1 partList4_complete0)
    apply(safe)
       using partList4_complete0 apply (metis Diff_subset_conv Diff_triv IntI UnionI)
      apply (metis Diff_subset_conv Diff_triv)
     using partList4_complete0 by (metis Diff_subset_conv IntI UnionI)+
  
  lemma union_set_partList4: "\<Union>set (partList4 s ts) = \<Union>set ts"
    by (induction ts arbitrary: s, auto)
  
  
  private lemma partList4_distinct_hlp: assumes "a \<noteq> {}" "a \<notin> set ts" "disjoint (insert a (set ts))"
    shows "a \<notin> set (partList4 s ts)"
  proof -
    from assms have "\<not> (a \<subseteq> \<Union>set ts)" unfolding disjoint_def by fastforce
    hence "\<not> (a \<subseteq> \<Union>set (partList4 s ts))" using union_set_partList4 by metis
    thus ?thesis by blast
  qed
  
  private lemma partList4_distinct: "{} \<notin> set ts \<Longrightarrow> disjoint_list ts \<Longrightarrow> distinct (partList4 s ts)"
    proof(induction ts arbitrary: s)
    case Nil thus ?case by simp
    next
    case(Cons t ts)
      have x1: "\<And>x xa xb xc.
         t \<notin> set ts \<Longrightarrow>
         disjoint (insert t (set ts)) \<Longrightarrow>
         xa \<in> t \<Longrightarrow>
         xb \<in> s \<Longrightarrow> 
         xb \<in> t \<Longrightarrow> 
         xb \<notin> {} \<Longrightarrow> 
         xc \<in> s \<Longrightarrow> 
         xc \<notin> {} \<Longrightarrow> 
         t \<inter> s \<in> set (partList4 (s - t) ts) \<Longrightarrow> 
         \<not> t \<inter> s \<subseteq> \<Union>set (partList4 (s - t) ts)"
        by(simp add: union_set_partList4 disjoint_def, force) (*1s*)
      have x2: "\<And>x xa xb xc.
         t \<notin> set ts \<Longrightarrow>
         disjoint (insert t (set ts)) \<Longrightarrow>
         x \<in> t \<Longrightarrow>
         xa \<in> t \<Longrightarrow>
         xa \<notin> s \<Longrightarrow>
         xb \<in> s \<Longrightarrow> 
         xc \<in> s \<Longrightarrow> 
         \<not> t - s \<subseteq> \<Union>set (partList4 (s - t) ts)"
        by(simp add: union_set_partList4 disjoint_def, force) (*1s*)
      from Cons have IH: "distinct (partList4 s ts)" for s
        using disjoint_sublist list.set_intros(2) by auto 
      from Cons.prems(1,2) IH show ?case
      unfolding disjoint_list_def
       apply(simp)
       apply(safe)
            apply(metis partList4_distinct_hlp)
           apply(metis partList4_distinct_hlp)
          apply(metis partList4_distinct_hlp)
         apply blast
        using x1 apply blast
       using x2 by blast
    qed
  
  lemma partList4_disjoint_list: assumes "s \<subseteq> \<Union> set ts" "disjoint_list ts" "{} \<notin> set ts"
    shows "disjoint_list (partList4 s ts)"
    unfolding disjoint_list_def
    proof
      from assms(2,3) show "distinct (partList4 s ts)" 
        using partList4_distinct disjoint_list_def by auto
      show "disjoint (set (partList4 s ts))"
      proof -
        have disjoint_list_disjoint_list_rec: "disjoint_list ts \<Longrightarrow> disjoint_list_rec ts"
        proof(induction ts)
        case Cons thus ?case by(auto simp add: disjoint_list_def disjoint_def)
        qed(simp)
        with partList4_disjoint disjoint_equi assms(1,2) show ?thesis by blast
      qed
    qed
  
  lemma partitioning1_subset: "a \<subseteq> \<Union> (set ts) \<Longrightarrow> a \<subseteq> \<Union> set (partitioning1 ss ts)"
    apply(induction ss arbitrary: ts a)
     apply(simp)
    apply(simp add: partList4_subset)
    done
  
  lemma partitioning1_disjoint_list: "{} \<notin> (set ts) \<Longrightarrow> \<Union> (set ss) \<subseteq> \<Union> (set ts) \<Longrightarrow>
                                 disjoint_list ts \<Longrightarrow> disjoint_list (partitioning1 ss ts)"
  proof(induction ss)
  case Nil thus ?case by simp
  next
  case(Cons t ts) thus ?case
    apply(clarsimp)
    apply(rule partList4_disjoint_list)
      using partitioning1_subset apply(metis)
     apply(blast)
    using partitioning1_empty0 apply(metis)
    done
  qed
  
  private lemma partitioning1_disjoint: "\<Union> (set ss) \<subseteq> \<Union> (set ts) \<Longrightarrow>
                                 disjoint_list_rec ts \<Longrightarrow> disjoint_list_rec (partitioning1 ss ts)"
    proof(induction ss arbitrary: ts)
    qed(simp_all add: partList4_disjoint partitioning1_subset)

  private lemma partitioning_equi: "{} \<notin> set ts \<Longrightarrow> disjoint_list_rec ts \<Longrightarrow> \<Union> (set ss) \<subseteq> \<Union> (set ts) \<Longrightarrow>
           set(partitioning1 ss ts) = partitioning_nontail ss (set ts) - {{}}"
    proof(induction ss)
    case Nil thus ?case by simp
    next
    case (Cons s ss)
      have addSubsetSet_empty: "addSubsetSet s (ts - {{}}) - {{}} = addSubsetSet s ts - {{}}"
        for s and ts::"'a set set"
        unfolding addSubsetSet_def by blast
      have r: "disjoint_list_rec ts \<Longrightarrow> s \<subseteq> \<Union>(set ts) \<Longrightarrow>
                                        addSubsetSet s (set ts) - {{}} = set (partList4 s ts) - {{}}"
        for ts::"'a set list"
        unfolding partList4
        by(simp add: partList0_addSubsetSet_equi partList0_partList1_equi partList1_partList2_equi
                   partList2_partList3_equi)
      have 1: "disjoint_list_rec (partitioning1 ss ts)"
        using partitioning1_disjoint Cons.prems by auto
      from Cons.prems have 2: "s \<subseteq> \<Union>set (partitioning1 ss ts)"
        by (meson Sup_upper dual_order.trans list.set_intros(1) partitioning1_subset)
      from Cons have IH: "set (partitioning1 ss ts) = partitioning_nontail ss (set ts) - {{}}" by auto
      with r[OF 1 2] show ?case by (simp add: partList4_empty addSubsetSet_empty)
    qed
  
  lemma ipPartitioning_helper_opt: "{} \<notin> set ts \<Longrightarrow> disjoint_list ts \<Longrightarrow> \<Union> (set ss) \<subseteq> \<Union> (set ts) 
                                    \<Longrightarrow> ipPartition (set ss) (set (partitioning1 ss ts))"
    apply(drule disjoint_list_disjoint_list_rec)
    apply(simp add: partitioning_equi partitioning_nottail_equi)
    by (meson Diff_subset disjoint_equi ipPartition_def ipPartitioning_helper subsetCE)
  
  lemma complete_helper: "{} \<notin> set ts \<Longrightarrow> \<Union> (set ss) \<subseteq> \<Union> (set ts)\<Longrightarrow>
        \<Union> (set ts) = \<Union> (set (partitioning1 ss ts))"
    apply(induction ss arbitrary: ts)
     apply(simp_all)
    by (metis partList4_complete0)

  lemma "partitioning1  [{1::nat},{2},{}] [{1},{},{2},{3}] = [{1}, {}, {2}, {3}]" by eval

  lemma partitioning_foldr: "partitioning X B = foldr addSubsetSet X B"
    apply(induction X)
     apply(simp; fail)
    apply(simp)
    by (metis partitioningCom)
  
  lemma "ipPartition (set X) (foldr addSubsetSet X {})"
    apply(subst partitioning_foldr[symmetric])
    using ipPartitioning by auto
  
  lemma "\<Union> (set X) = \<Union> (foldr addSubsetSet X {})"
    apply(subst partitioning_foldr[symmetric])
    by (simp add: coversallPartitioning)
  
  lemma "partitioning1 X B = foldr partList4 X B"
    by(induction X)(simp_all)
  
  lemma "ipPartition (set X) (set (partitioning1 X [UNIV]))"
    apply(rule ipPartitioning_helper_opt)
      by(simp_all add: disjoint_list_def disjoint_def)
  
  lemma "(\<Union>(set (partitioning1 X [UNIV]))) = UNIV"
    apply(subgoal_tac "UNIV = \<Union> (set (partitioning1 X [UNIV]))")
     prefer 2
     apply(rule complete_helper[where ts="[UNIV]", simplified])
    apply(simp)
    done
  
end
end
