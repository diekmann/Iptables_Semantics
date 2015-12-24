(*Original Author: Max Haslbeck, 2015*)
theory IPPartitioning
imports "../Common/SetPartitioning"
        "../Primitive_Matchers/Common_Primitive_toString"
        "SimpleFw_Semantics"
        "../afp/Mergesort" (*TODO*)
begin



fun extract_IPSets_generic0 :: "(simple_match \<Rightarrow> 32 word \<times> nat) \<Rightarrow> simple_rule list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets_generic0 _ [] = []" |
  "extract_IPSets_generic0 sel ((SimpleRule m _)#ss) = (ipv4_cidr_tuple_to_interval (sel m)) #
                                                       (extract_IPSets_generic0 sel ss)"

lemma extract_IPSets_generic0_length: "length (extract_IPSets_generic0 sel rs) = length rs"
  by(induction rs rule: extract_IPSets_generic0.induct) (simp_all)



(*
The order in which extract_IPSets returns the collected IP ranges heavily influences the running time
of the subsequent algorithms.
For example:
1) iterating through the ruleset and collecting all source and destination ips:
   10:10:49 elapsed time, 38:41:17 cpu time, factor 3.80
2) iterating through the ruleset and first returning all source ips and iterating again and then return all destination ips:
   3:39:56 elapsed time, 21:08:34 cpu time, factor 5.76

To get a more deterministic runtime, we are sorting the output. As a performance optimization, we also remove duplicate entries.
We use mergesort_remdups, which does a mergesort (i.e sorts!) and removes duplicates and mergesort_by_rel which does a mergesort
(without removing duplicates) and allows to specify the relation we use to sort.
In theory, the largest ip ranges (smallest prefix length) should be put first, the following evaluation shows that this may not
be the fastest solution. The reason might be that build_ip_partition_pretty picks (almost randomly) one IP from the result and
there are fast and slower choices. The faster choices are the ones where the firewall ruleset has a decision very early. 
Therefore, the running time is still a bit unpredictable.

Here is the data:
map ipv4_cidr_tuple_to_interval (mergesort_by_rel (\<lambda> (a1,a2) (b1, b2). (a2, a1) \<le> (b2, b1)) (mergesort_remdups
                        ((map (src \<circ> match_sel) rs) @ (map (dst \<circ> match_sel) rs))))
 (2:47:04 elapsed time, 17:08:01 cpu time, factor 6.15)


map ipv4_cidr_tuple_to_interval (mergesort_remdups ((map (src \<circ> match_sel) rs) @ (map (dst \<circ> match_sel) rs)))
 (2:41:03 elapsed time, 16:56:46 cpu time, factor 6.31)


map ipv4_cidr_tuple_to_interval (mergesort_by_rel (\<lambda> (a1,a2) (b1, b2). (a2, a1) \<le> (b2, b1)) (
                         ((map (src \<circ> match_sel) rs) @ (map (dst \<circ> match_sel) rs)))
 (5:52:28 elapsed time, 41:50:10 cpu time, factor 7.12)


map ipv4_cidr_tuple_to_interval (mergesort_by_rel (op \<le>)
                         ((map (src \<circ> match_sel) rs) @ (map (dst \<circ> match_sel) rs))))
  (3:10:57 elapsed time, 19:12:25 cpu time, factor 6.03)


map ipv4_cidr_tuple_to_interval (mergesort_by_rel (\<lambda> (a1,a2) (b1, b2). (a2, a1) \<le> (b2, b1)) (mergesort_remdups
                        (extract_src_dst_ips rs [])))
 (2:49:57 elapsed time, 17:10:49 cpu time, factor 6.06)

map ipv4_cidr_tuple_to_interval ((mergesort_remdups (extract_src_dst_ips rs [])))
 (2:43:44 elapsed time, 16:57:49 cpu time, factor 6.21)

map ipv4_cidr_tuple_to_interval (mergesort_by_rel (\<lambda> (a1,a2) (b1, b2). (a2, a1) \<ge> (b2, b1)) (mergesort_remdups (extract_src_dst_ips rs [])))
 (2:47:37 elapsed time, 16:54:47 cpu time, factor 6.05)

There is a clear looser: not using mergesort_remdups
There is no clear winner. We will just stick to mergesort_remdups.

*)

(*check the the order of mergesort_remdups did not change*)
lemma "mergesort_remdups [(1::ipv4addr, 2::nat), (8,0), (8,1), (2,2), (2,4), (1,2), (2,2)] = [(1, 2), (2, 2), (2, 4), (8, 0), (8, 1)]" by eval


(*a tail-recursive implementation*)
fun extract_src_dst_ips :: "simple_rule list \<Rightarrow> (ipv4addr \<times> nat) list \<Rightarrow> (ipv4addr \<times> nat) list" where
  "extract_src_dst_ips [] ts = ts" |
  "extract_src_dst_ips ((SimpleRule m _)#ss) ts = extract_src_dst_ips ss  (src m # dst m # ts)"

lemma extract_src_dst_ips_length: "length (extract_src_dst_ips rs acc) = 2*length rs + length acc"
proof(induction rs arbitrary: acc)
case (Cons r rs) thus ?case by(cases r, simp)
qed(simp)

definition extract_IPSets :: "simple_rule list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets rs = map ipv4_cidr_tuple_to_interval (mergesort_remdups (extract_src_dst_ips rs []))"
lemma extract_IPSets: "set (extract_IPSets rs) = set (extract_IPSets_generic0 src rs) \<union> set (extract_IPSets_generic0 dst rs)"
proof -
  { fix acc
    have "ipv4_cidr_tuple_to_interval ` set (extract_src_dst_ips rs acc) =
          ipv4_cidr_tuple_to_interval ` set acc \<union> set (extract_IPSets_generic0 src rs) \<union> set (extract_IPSets_generic0 dst rs)"
    proof(induction rs arbitrary: acc)
    case (Cons r rs ) thus ?case
      apply(cases r)
      apply(simp)
      by fast
    qed(simp)
  } thus ?thesis unfolding extract_IPSets_def by(simp_all add: extract_IPSets_def mergesort_remdups_correct)
qed

lemma "(a::nat) div 2 + a mod 2 \<le> a" by fastforce

lemma merge_length: "length (merge l1 l2) \<le> length l1 + length l2"
by(induction l1 l2 rule: merge.induct) auto

lemma merge_list_length: "length (merge_list as ls) \<le> length (concat (as @ ls))"
proof(induction as ls rule: merge_list.induct)
case (5 l1 l2 acc2 ls)
  have "length (merge l2 acc2) \<le> length l2 + length acc2" using merge_length by blast
  with 5 show ?case by simp
qed(simp_all)

lemma mergesort_remdups_length: "length (mergesort_remdups as) \<le> length as"
unfolding mergesort_remdups_def
proof -
  have "concat ([] @ (map (\<lambda>x. [x]) as)) = as" by simp
  with merge_list_length show "length (merge_list [] (map (\<lambda>x. [x]) as)) \<le> length as" by metis
qed

lemma extract_IPSets_length: "length (extract_IPSets rs) \<le> 2 * length rs"
apply(simp add: extract_IPSets_def)
using extract_src_dst_ips_length mergesort_remdups_length by (metis add.right_neutral list.size(3)) 


(*
export_code extract_IPSets in SML
why you no work?
*)


lemma extract_equi0: "set (map wordinterval_to_set (extract_IPSets_generic0 sel rs))
                     = (\<lambda>(base,len). ipv4range_set_from_prefix base len) ` sel ` match_sel ` set rs"
  proof(induction rs)
  case (Cons r rs) thus ?case
    apply(cases r, simp)
    using ipv4range_to_set_ipv4_cidr_tuple_to_interval[simplified ipv4range_to_set_def] by fastforce
  qed(simp)

lemma src_ipPart:
  assumes "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 src rs))) A"
          "B \<in> A" "s1 \<in> B" "s2 \<in> B"
  shows "simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>)"
proof -
  have "\<forall>A \<in> (\<lambda>(base,len). ipv4range_set_from_prefix base len) ` src ` match_sel ` set rs. B \<subseteq> A \<or> B \<inter> A = {} \<Longrightarrow>
      simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>)"
  proof(induction rs)
    case Nil thus ?case by simp
  next
    case (Cons r rs)
    { fix m
      from `s1 \<in> B` `s2 \<in> B` have 
        "B \<subseteq> (case src m of (x, xa) \<Rightarrow> ipv4range_set_from_prefix x xa) \<or> B \<inter> (case src m of (x, xa) 
                      \<Rightarrow> ipv4range_set_from_prefix x xa) = {} \<Longrightarrow>
             simple_matches m (p\<lparr>p_src := s1\<rparr>) \<longleftrightarrow> simple_matches m (p\<lparr>p_src := s2\<rparr>)"
      apply(cases m)
      apply(rename_tac iiface oiface srca dst proto sports dports)
      apply(case_tac srca)
      apply(simp add: simple_matches.simps)
      by blast
    } note helper=this
    from Cons show ?case
     apply(simp)
     apply(case_tac r, rename_tac m a)
     apply(simp)
     apply(case_tac a)
      using helper apply force+
     done
  qed
  thus ?thesis using assms(1) assms(2)
    unfolding ipPartition_def
    by (metis (full_types) Int_commute extract_equi0)
qed

(*basically a copy of src_ipPart*)
lemma dst_ipPart:
  assumes "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 dst rs))) A"
          "B \<in> A" "s1 \<in> B" "s2 \<in> B"
  shows "simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
proof -
  have "\<forall>A \<in> (\<lambda>(base,len). ipv4range_set_from_prefix base len) ` dst ` match_sel ` set rs. B \<subseteq> A \<or> B \<inter> A = {} \<Longrightarrow>
      simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
  proof(induction rs)
    case Nil thus ?case by simp
  next
    case (Cons r rs)
    { fix m
      from `s1 \<in> B` `s2 \<in> B` have
        "B \<subseteq> (case dst m of (x, xa) \<Rightarrow> ipv4range_set_from_prefix x xa) \<or> B \<inter> (case dst m of (x, xa) 
                  \<Rightarrow> ipv4range_set_from_prefix x xa) = {} \<Longrightarrow>
         simple_matches m (p\<lparr>p_dst := s1\<rparr>) \<longleftrightarrow> simple_matches m (p\<lparr>p_dst := s2\<rparr>)"
          apply(cases m)
          apply(rename_tac iiface oiface src dsta proto sports dports)
          apply(case_tac dsta)
          apply(simp add: simple_matches.simps)
          by blast
    } note helper=this
    from Cons show ?case
     apply(simp)
     apply(case_tac r, rename_tac m a)
     apply(simp)
     apply(case_tac a)
      using helper apply force+
     done
  qed
  thus ?thesis using assms(1) assms(2)
    unfolding ipPartition_def
    by (metis (full_types) Int_commute extract_equi0)
qed



(* OPTIMIZED PARTITIONING *)

fun wordinterval_list_to_set :: "'a::len wordinterval list \<Rightarrow> 'a::len word set" where
  "wordinterval_list_to_set ws = \<Union> set (map wordinterval_to_set ws)"

fun partIps :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval list 
                \<Rightarrow> 'a::len wordinterval list" where
  "partIps _ [] = []" |
  "partIps s (t#ts) = (if wordinterval_empty s then (t#ts) else
                        (if wordinterval_empty (wordinterval_intersection s t)
                          then (t#(partIps (wordinterval_setminus s t) ts))
                          else
                            (if wordinterval_empty (wordinterval_setminus t s)
                              then (t#(partIps (wordinterval_setminus s t) ts))
                              else (wordinterval_intersection t s)#((wordinterval_setminus t s)#
                                   (partIps (wordinterval_setminus s t) ts)))))"

fun partitioningIps :: "'a::len wordinterval list \<Rightarrow> 'a::len wordinterval list \<Rightarrow>
                        'a::len wordinterval list" where
  "partitioningIps [] ts = ts" |
  "partitioningIps (s#ss) ts = partIps s (partitioningIps ss ts)"

lemma partIps_equi: "map wordinterval_to_set (partIps s ts)
       = (partList3 (wordinterval_to_set s) (map wordinterval_to_set ts))"
  proof(induction ts arbitrary: s)
  qed(simp_all)

lemma partitioningIps_equi: "map wordinterval_to_set (partitioningIps ss ts)
       = (partitioning1 (map wordinterval_to_set ss) (map wordinterval_to_set ts))"
  proof(induction ss arbitrary: ts)
  qed(simp_all add: partIps_equi)


lemma ipPartitioning_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow> 
   ipPartition (set (map wordinterval_to_set ss)) 
               (set (map wordinterval_to_set (partitioningIps ss ts)))"
by (metis ipPartitioning_helper_opt partitioningIps_equi wordinterval_list_to_set.simps)

lemma complete_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow> 
   \<Union> (set (map wordinterval_to_set ts)) = \<Union> (set (map wordinterval_to_set (partitioningIps ss ts)))"
using complete_helper by (metis partitioningIps_equi wordinterval_list_to_set.simps)

lemma disjoint_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow>
   disjoint_list_rec (map wordinterval_to_set (partitioningIps ss ts))"
by (simp add: partitioning1_disjoint partitioningIps_equi)


lemma ipPartitioning_partitioningIps1: "ipPartition (set (map wordinterval_to_set ss)) 
                   (set (map wordinterval_to_set (partitioningIps ss [wordinterval_UNIV])))"
  proof(rule ipPartitioning_partitioningIps)
  qed(simp_all)
                  
definition getParts :: "simple_rule list \<Rightarrow> 32 wordinterval list" where
   "getParts rs = partitioningIps (extract_IPSets rs) [wordinterval_UNIV]"


lemma partitioningIps_foldr: "partitioningIps ss ts = foldr partIps ss ts"
  by(induction ss) (simp_all)

lemma getParts_foldr: "getParts rs = foldr partIps (extract_IPSets rs) [wordinterval_UNIV]"
  by(simp add: getParts_def partitioningIps_foldr)


lemma getParts_ipPartition: "ipPartition (set (map wordinterval_to_set (extract_IPSets rs)))
                                         (set (map wordinterval_to_set (getParts rs)))"
  unfolding getParts_def
  apply(subst ipPartitioning_partitioningIps1)
  by(simp)



lemma getParts_complete: "\<Union> (set (map wordinterval_to_set (getParts rs))) = UNIV"
  proof -
    have "\<Union> (set (map wordinterval_to_set (getParts rs))) = \<Union> (set (map wordinterval_to_set [wordinterval_UNIV]))"
      unfolding getParts_def
      apply(rule complete_partitioningIps[symmetric])
        by(simp_all)
    also have "\<dots> = UNIV" by simp
    finally show ?thesis .
qed

lemma getParts_disjoint: "disjoint_list_rec (map wordinterval_to_set (getParts rs))"
  apply(subst getParts_def)
  apply(rule disjoint_partitioningIps)
    apply(simp_all)
  done


theorem getParts_samefw: 
  assumes "A \<in> set (map wordinterval_to_set (getParts rs))" "s1 \<in> A" "s2 \<in> A" 
  shows "simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>) \<and>
         simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
proof -
  let ?X="(set (map wordinterval_to_set (getParts rs)))"
  from getParts_ipPartition have "ipPartition (set (map wordinterval_to_set (extract_IPSets rs))) ?X" .
  hence "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 src rs))) ?X \<and>
         ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 dst rs))) ?X"
    by(simp add: extract_IPSets ipPartitionUnion image_Un)
  thus ?thesis using assms dst_ipPart src_ipPart by blast
qed



lemma partIps_nonempty: "\<forall>t \<in> set ts. \<not> wordinterval_empty t 
       \<Longrightarrow> {} \<notin> set (map wordinterval_to_set (partIps s ts))"
  apply(induction ts arbitrary: s)
   apply(simp; fail)
  apply(simp)
  by blast

lemma partitioning_nonempty: "\<forall>t \<in> set ts. \<not> wordinterval_empty t
                              \<Longrightarrow> {} \<notin> set (map wordinterval_to_set (partitioningIps ss ts))"
  apply(induction ss arbitrary: ts)
   apply(simp_all)
   apply(blast)
  by (metis partIps_equi partList3_empty set_map)

lemma ineedtolearnisar: "\<forall>t \<in> set [wordinterval_UNIV]. \<not> wordinterval_empty t"
  by(simp)

lemma getParts_nonempty: "{} \<notin> set (map wordinterval_to_set 
                                    (partitioningIps ss [wordinterval_UNIV]))"
  using ineedtolearnisar partitioning_nonempty by(blast)

(* HELPER FUNCTIONS UNIFICATION *)

fun getOneIp :: "'a::len wordinterval \<Rightarrow> 'a::len word" where
  "getOneIp (WordInterval b _) = b" |
  "getOneIp (RangeUnion r1 r2) = (if wordinterval_empty r1 then getOneIp r2
                                                           else getOneIp r1)"

lemma getOneIp_elem: "\<not> wordinterval_empty W \<Longrightarrow> wordinterval_element (getOneIp W) W"
  by (induction W) simp_all

record parts_connection = pc_iiface :: string
                          pc_oiface :: string
                          pc_proto :: primitive_protocol
                          pc_sport :: "16 word"
                          pc_dport :: "16 word"
                          pc_tag_ctstate :: ctstate



(* SAME FW DEFINITIONS AND PROOFS *)

lemma relation_lem: "\<forall>D \<in> W. \<forall>d1 \<in> D. \<forall>d2 \<in> D. \<forall>s. f s d1 = f s d2 \<Longrightarrow> \<Union> W = UNIV \<Longrightarrow>
                     \<forall>B \<in> W. \<exists>b \<in> B. f s1 b = f s2 b \<Longrightarrow>
                     f s1 d = f s2 d"
by (metis UNIV_I Union_iff)


definition same_fw_behaviour :: "32 word \<Rightarrow> 32 word \<Rightarrow> simple_rule list \<Rightarrow> bool" where
  "same_fw_behaviour a b rs \<equiv> \<forall>p. simple_fw rs (p\<lparr>p_src:=a\<rparr>) = simple_fw rs (p\<lparr>p_src:=b\<rparr>) \<and>
                                  simple_fw rs (p\<lparr>p_dst:=a\<rparr>) = simple_fw rs (p\<lparr>p_dst:=b\<rparr>)"

lemma getParts_same_fw_behaviour:
  "A \<in> set (map wordinterval_to_set (getParts rs)) \<Longrightarrow>  s1 \<in> A \<Longrightarrow> s2 \<in> A \<Longrightarrow> 
   same_fw_behaviour s1 s2 rs"
  unfolding same_fw_behaviour_def
  using getParts_samefw by blast

definition "runFw s d c rs = simple_fw rs \<lparr>p_iiface=pc_iiface c,p_oiface=pc_oiface c,
                          p_src=s,p_dst=d,
                          p_proto=pc_proto c,
                          p_sport=pc_sport c,p_dport=pc_dport c,
                          p_tcp_flags={TCP_SYN},
                          p_tag_ctstate=pc_tag_ctstate c\<rparr>"

definition "same_fw_behaviour_one ip1 ip2 c rs \<equiv>
            \<forall>d s. runFw ip1 d c rs = runFw ip2 d c rs \<and> runFw s ip1 c rs = runFw s ip2 c rs"

lemma same_fw_spec: "same_fw_behaviour ip1 ip2 rs \<Longrightarrow> same_fw_behaviour_one ip1 ip2 c rs"
  apply(simp add: same_fw_behaviour_def same_fw_behaviour_one_def runFw_def)
  apply(rule conjI)
   apply(clarify)
   apply(erule_tac x="\<lparr>p_iiface = pc_iiface c, p_oiface = pc_oiface c, p_src = ip1, p_dst= d,
                       p_proto = pc_proto c, p_sport = pc_sport c, p_dport = pc_dport c,
                       p_tcp_flags = {TCP_SYN},
                       p_tag_ctstate = pc_tag_ctstate c\<rparr>" in allE)
   apply(simp;fail)
  apply(clarify)
  apply(erule_tac x="\<lparr>p_iiface = pc_iiface c, p_oiface = pc_oiface c, p_src = s, p_dst= ip1,
                       p_proto = pc_proto c, p_sport = pc_sport c, p_dport = pc_dport c,
                       p_tcp_flags = {TCP_SYN},
                       p_tag_ctstate = pc_tag_ctstate c\<rparr>" in allE)
  apply(simp)
  done

text{*Is an equivalence relation*}
lemma same_fw_behaviour_one_equi:
  "same_fw_behaviour_one x x c rs"
  "same_fw_behaviour_one x y c rs = same_fw_behaviour_one y x c rs"
  "same_fw_behaviour_one x y c rs \<and> same_fw_behaviour_one y z c rs \<Longrightarrow> same_fw_behaviour_one x z c rs"
  unfolding same_fw_behaviour_one_def by metis+

lemma same_fw_behaviour_equi:
  "same_fw_behaviour x x rs"
  "same_fw_behaviour x y rs = same_fw_behaviour y x rs"
  "same_fw_behaviour x y rs \<and> same_fw_behaviour y z rs \<Longrightarrow> same_fw_behaviour x z rs"
  unfolding same_fw_behaviour_def by auto

lemma runFw_sameFw_behave: 
       "\<forall>A \<in> W. \<forall>a1 \<in> A. \<forall>a2 \<in> A. same_fw_behaviour_one a1 a2 c rs \<Longrightarrow> \<Union> W = UNIV \<Longrightarrow>
       \<forall>B \<in> W. \<exists>b \<in> B. runFw ip1 b c rs = runFw ip2 b c rs \<Longrightarrow>
       \<forall>B \<in> W. \<exists>b \<in> B. runFw b ip1 c rs = runFw b ip2 c rs \<Longrightarrow>
       same_fw_behaviour_one ip1 ip2 c rs"
proof -
  assume a1: "\<forall>A \<in> W. \<forall>a1 \<in> A. \<forall>a2 \<in> A. same_fw_behaviour_one a1 a2 c rs"
   and a2: "\<Union> W = UNIV "
   and a3: "\<forall>B \<in> W. \<exists>b \<in> B. runFw ip1 b c rs = runFw ip2 b c rs"
   and a4: "\<forall>B \<in> W. \<exists>b \<in> B. runFw b ip1 c rs = runFw b ip2 c rs"

  from a1 have a1':"\<forall>A\<in>W. \<forall>a1\<in>A. \<forall>a2\<in>A. \<forall>s. runFw s a1 c rs = runFw s a2 c rs"
    unfolding same_fw_behaviour_one_def by fast
  from relation_lem[OF a1' a2 a3] have s1: "\<And> d. runFw ip1 d c rs = runFw ip2 d c rs" by simp

  from a1 have a1'':"\<forall>A\<in>W. \<forall>a1\<in>A. \<forall>a2\<in>A. \<forall>d. runFw a1 d c rs = runFw a2 d c rs"
    unfolding same_fw_behaviour_one_def by fast
  from relation_lem[OF a1'' a2 a4] have s2: "\<And> s. runFw s ip1 c rs = runFw s ip2 c rs" by simp
  from s1 s2 show "same_fw_behaviour_one ip1 ip2 c rs"
    unfolding same_fw_behaviour_one_def by fast
qed

lemma sameFw_behave_sets:
  "\<forall>w\<in>set A. \<forall>a1 \<in> w. \<forall>a2 \<in> w. same_fw_behaviour_one a1 a2 c rs \<Longrightarrow>
   \<forall>w1\<in>set A. \<forall>w2\<in>set A. \<exists>a1\<in>w1. \<exists>a2\<in>w2. same_fw_behaviour_one a1 a2 c rs \<Longrightarrow>
   \<forall>w1\<in>set A. \<forall>w2\<in>set A.
     \<forall>a1\<in>w1. \<forall>a2\<in>w2. same_fw_behaviour_one a1 a2 c rs"
proof -
  assume a1: "\<forall>w\<in>set A. \<forall>a1 \<in> w. \<forall>a2 \<in> w. same_fw_behaviour_one a1 a2 c rs" and
         "\<forall>w1\<in>set A. \<forall>w2\<in>set A. \<exists>a1\<in>w1. \<exists>a2\<in>w2.  same_fw_behaviour_one a1 a2 c rs"
  from this have "\<forall>w1\<in>set A. \<forall>w2\<in>set A. \<exists>a1\<in>w1. \<forall>a2\<in>w2.  same_fw_behaviour_one a1 a2 c rs"
    using same_fw_behaviour_one_equi(3) by metis
  from a1 this show "\<forall>w1\<in>set A. \<forall>w2\<in>set A. \<forall>a1\<in>w1. \<forall>a2\<in>w2. same_fw_behaviour_one a1 a2 c rs"
    using same_fw_behaviour_one_equi(3) by metis
qed
  
lemma same_behave_runFw:
  assumes a1: "\<forall>A \<in> set (map wordinterval_to_set W). \<forall>a1 \<in> A. \<forall>a2 \<in> A. same_fw_behaviour_one a1 a2 c rs"
  and a2: "\<Union> set (map wordinterval_to_set W) = UNIV"
  and a3: "\<forall>w \<in> set W. \<not> wordinterval_empty w"
  and a4: "(map (\<lambda>d. runFw x1 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x1 c rs) (map getOneIp W)) =
           (map (\<lambda>d. runFw x2 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x2 c rs) (map getOneIp W))"
  shows "same_fw_behaviour_one x1 x2 c rs"
proof -
  from a3 a4 getOneIp_elem
    have b1: "\<forall>B \<in> set (map wordinterval_to_set W). \<exists>b \<in> B. runFw x1 b c rs = runFw x2 b c rs"
    by fastforce
  from a3 a4 getOneIp_elem
    have b2: "\<forall>B \<in> set (map wordinterval_to_set W). \<exists>b \<in> B. runFw b x1 c rs = runFw b x2 c rs"
    by fastforce
  from runFw_sameFw_behave[OF a1 a2 b1 b2] show "same_fw_behaviour_one x1 x2 c rs" by simp
qed

lemma same_behave_runFw_not:
      "(map (\<lambda>d. runFw x1 d c rs) W, map (\<lambda>s. runFw s x1 c rs) W) \<noteq>
       (map (\<lambda>d. runFw x2 d c rs) W, map (\<lambda>s. runFw s x2 c rs) W) \<Longrightarrow>
       \<not> same_fw_behaviour_one x1 x2 c rs"
by (simp add: same_fw_behaviour_one_def) (blast)


(*TODO: move to common list functions?*)
fun groupF ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
  "groupF f [] = []" |
  "groupF f (x#xs) = (x#(filter (\<lambda>y. f x = f y) xs))#(groupF f (filter (\<lambda>y. f x \<noteq> f y) xs))"

  

(*trying a more efficient implementation of groupF*)
fun select_p_tuple :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)" where
  "select_p_tuple p x (ts,fs) = (if p x then (x#ts, fs) else (ts, x#fs))"

definition partition_tailrec :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)" where
  "partition_tailrec p xs = foldr (select_p_tuple p) xs ([],[])"

lemma partition_tailrec: "partition_tailrec f as =  (filter f as,  filter (\<lambda>x. \<not>f x) as)"
proof - 
  {fix ts_accu fs_accu
    have "foldr (select_p_tuple f) as (ts_accu, fs_accu) = (filter f as @ ts_accu,  filter (\<lambda>x. \<not>f x) as @ fs_accu)"
    by(induction as arbitrary: ts_accu fs_accu) simp_all
  } thus ?thesis unfolding partition_tailrec_def by simp
qed
(*
fun partition_tailrec :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)" where
  "partition_tailrec _ [] acc = acc" |
  "partition_tailrec f (a#as) (ts,fs) = (if f a then partition_tailrec f as (a#ts, fs) else partition_tailrec f as (ts, a#fs))"

lemma "partition_tailrec f as (ts_accu, fs_accu) = (rev (filter f as) @ ts_accu, rev (filter (\<lambda>x. \<not>f x) as) @ fs_accu)"
apply(induction as arbitrary: ts_accu fs_accu)
 apply(simp)
apply(simp)
done
*)


lemma "groupF f (x#xs) = (let (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs in (x#ts)#(groupF f fs))"
by(simp add: partition_tailrec)

(*is this more efficient?*)
function groupF_code ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
  "groupF_code f [] = []" |
  "groupF_code f (x#xs) = (let (ts, fs) = partition_tailrec (\<lambda>y. f x = f y) xs in (x#ts)#(groupF_code f fs))"
apply(pat_completeness)
apply(auto)
done

termination groupF_code
  apply(relation "measure (\<lambda>(f,as). length (filter (\<lambda>x. (\<lambda>y. f x = f y) x) as))")
   apply(simp; fail)
  apply(simp add: partition_tailrec)
  using le_imp_less_Suc length_filter_le by blast

lemma groupF_code[code]: "groupF f as = groupF_code f as"
  by(induction f as rule: groupF_code.induct) (simp_all add: partition_tailrec)

export_code groupF in SML


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
  using assms proof(induction xs)
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    { fix a
      (*I have no idea what I'm doing. This was originally a smt proof -_-*)
      have "groupF f1 xs = groupF f2 xs \<Longrightarrow> \<forall>x \<in> set xs. \<forall>y \<in> set xs. (f1 x = f1 y \<longleftrightarrow> f2 x = f2 y) \<Longrightarrow>
              groupF f1 [x\<leftarrow>xs . f2 a \<noteq> f2 x] = groupF f2 [x\<leftarrow>xs . f2 a \<noteq> f2 x]"
      proof(induction f2 xs rule: groupF.induct)
      case 1 thus ?case by simp
      next
      case (2 f x xs)
        have filter1: "[y\<leftarrow>xs . f1 x \<noteq> f1 y] = [y\<leftarrow>xs . f x \<noteq> f y]"
         using 2(3) by(auto cong: filter_cong)
        have filter2: "[xa\<leftarrow>xs . f x \<noteq> f xa \<and> f a \<noteq> f xa] = [xa\<leftarrow>xs . f a \<noteq> f xa \<and> f x \<noteq> f xa]"
         apply(rule filter_cong)
          apply(simp; fail)
         by auto
        have filter3: "[xa\<leftarrow>xs . f a \<noteq> f xa \<and> f1 x \<noteq> f1 xa] = [xa\<leftarrow>xs . f a \<noteq> f xa \<and> f x \<noteq> f xa]"
         using 2(3) by(auto cong: filter_cong)
        have filter4: "[y\<leftarrow>xs . f1 x \<noteq> f1 y] = [y\<leftarrow>xs . f x \<noteq> f y]"
         using 2(3) by(auto cong: filter_cong)
        have filter5: "[xa\<leftarrow>xs . f a \<noteq> f xa \<and> f1 x = f1 xa] = [xa\<leftarrow>xs . f a \<noteq> f xa \<and> f x = f xa]" 
         using 2(3) by(auto cong: filter_cong)
      
        show ?case
          apply(simp)
          apply(intro conjI impI)
            using filter1 2(2) apply fastforce
           using filter5 apply blast
          using filter2 filter3 filter4 2(1) 2(2) 2(3) by simp
      qed
    } note hackyhack=this

    have filter1: "[y\<leftarrow>xs . f1 x = f1 y] = [y\<leftarrow>xs . f2 x = f2 y]"
      using Cons.prems by(auto cong: filter_cong)
    have filter2: "[y\<leftarrow>xs . f1 x \<noteq> f1 y] = [y\<leftarrow>xs . f2 x \<noteq> f2 y]"
      using Cons.prems by(auto cong: filter_cong)
    from filter1 filter2 Cons show ?case
      apply simp
      apply(rule hackyhack)
       apply(simp; fail)
      by fast
  qed




definition groupWIs :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs c rs = (let W = getParts rs in 
                       (let f = (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs) (map getOneIp W),
                                      map (\<lambda>s. runFw s (getOneIp wi) c rs) (map getOneIp W))) in
                       groupF f W))"

lemma groupParts_same_fw_wi0:
    assumes "V \<in> set (groupWIs c rs)"
    shows "\<forall>w \<in> set (map wordinterval_to_set V). \<forall>a1 \<in> w. \<forall>a2 \<in> w. same_fw_behaviour_one a1 a2 c rs"
proof -
  have "\<forall>A\<in>set (map wordinterval_to_set (concat (groupWIs c rs))). 
        \<forall>a1\<in>A. \<forall>a2\<in>A. same_fw_behaviour_one a1 a2 c rs"
    apply(subst groupWIs_def)
    apply(subst Let_def)+
    apply(subst set_map)
    apply(subst groupF_set_lem)
    using getParts_same_fw_behaviour same_fw_spec by fastforce
  from this assms show ?thesis by force
qed

lemma groupWIs_same_fw_not: "A \<in> set (groupWIs c rs) \<Longrightarrow> B \<in> set (groupWIs c rs) \<Longrightarrow> 
                            A \<noteq> B \<Longrightarrow>
                             \<forall>aw \<in> set (map wordinterval_to_set A).
                             \<forall>bw \<in> set (map wordinterval_to_set B).
                             \<forall>a \<in> aw. \<forall>b \<in> bw. \<not> same_fw_behaviour_one a b c rs"
proof -
  assume asm: "A \<in> set (groupWIs c rs)" "B \<in> set (groupWIs c rs)" "A \<noteq> B"
  from this have b1: "\<forall>aw \<in> set A. \<forall>bw \<in> set B.
                  (map (\<lambda>d. runFw (getOneIp aw) d c rs) (map getOneIp (getParts rs)),
                   map (\<lambda>s. runFw s (getOneIp aw) c rs) (map getOneIp (getParts rs))) \<noteq>
                  (map (\<lambda>d. runFw (getOneIp bw) d c rs) (map getOneIp (getParts rs)),
                   map (\<lambda>s. runFw s (getOneIp bw) c rs) (map getOneIp (getParts rs)))"
  apply(simp add: groupWIs_def Let_def)
  using groupF_lem_not by fastforce
  have "\<forall>C \<in> set (groupWIs c rs). \<forall>c \<in> set C. getOneIp c \<in> wordinterval_to_set c"
    apply(simp add: groupWIs_def Let_def)
    using getParts_nonempty getOneIp_elem getParts_def groupF_set_lem1 by fastforce
  from this b1 asm have
  "\<forall>aw \<in> set (map wordinterval_to_set A). \<forall>bw \<in> set (map wordinterval_to_set B).
   \<exists>a \<in> aw. \<exists>b \<in> bw. (map (\<lambda>d. runFw a d c rs) (map getOneIp (getParts rs)), map (\<lambda>s. runFw s a c rs) (map getOneIp (getParts rs))) \<noteq>
    (map (\<lambda>d. runFw b d c rs) (map getOneIp (getParts rs)), map (\<lambda>s. runFw s b c rs) (map getOneIp (getParts rs)))"
   by (simp) (blast)
  from this same_behave_runFw_not asm
  have " \<forall>aw \<in> set (map wordinterval_to_set A). \<forall>bw \<in> set (map wordinterval_to_set B).
         \<exists>a \<in> aw. \<exists>b \<in> bw. \<not> same_fw_behaviour_one a b c rs" by fast
  from this groupParts_same_fw_wi0[of A c rs]  groupParts_same_fw_wi0[of B c rs] asm
  have "\<forall>aw \<in> set (map wordinterval_to_set A).
        \<forall>bw \<in> set (map wordinterval_to_set B).
        \<forall>a \<in> aw. \<exists>b \<in> bw. \<not> same_fw_behaviour_one a b c rs"
    apply(simp) using same_fw_behaviour_one_equi(3) by blast
  from this groupParts_same_fw_wi0[of A c rs]  groupParts_same_fw_wi0[of B c rs] asm
  show "\<forall>aw \<in> set (map wordinterval_to_set A).
        \<forall>bw \<in> set (map wordinterval_to_set B).
        \<forall>a \<in> aw. \<forall>b \<in> bw. \<not> same_fw_behaviour_one a b c rs"
    apply(simp) using same_fw_behaviour_one_equi(3) by fast
qed

lemma groupParts_same_fw_wi1:
  "V \<in> set (groupWIs c rs) \<Longrightarrow> \<forall>w1 \<in> set V. \<forall>w2 \<in> set V.
     \<forall>a1 \<in> wordinterval_to_set w1. \<forall>a2 \<in> wordinterval_to_set w2. same_fw_behaviour_one a1 a2 c rs"
proof -
  assume asm: "V \<in> set (groupWIs c rs)"
  from getParts_same_fw_behaviour same_fw_spec
    have b1: "\<forall>A \<in> set (map wordinterval_to_set (getParts rs)) . \<forall>a1 \<in> A. \<forall>a2 \<in> A.
              same_fw_behaviour_one a1 a2 c rs" by fast
  from getParts_nonempty
    have "\<forall>w\<in>set (getParts rs). \<not> wordinterval_empty w" apply(subst getParts_def) by auto
  from same_behave_runFw[OF b1 getParts_complete this]
       groupF_lem[of "(\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs) (map getOneIp (getParts rs)),
                             map (\<lambda>s. runFw s (getOneIp wi) c rs) (map getOneIp (getParts rs))))"
                     "(getParts rs)"] asm
  have b2: "\<forall>a1\<in>set V. \<forall>a2\<in>set V. same_fw_behaviour_one (getOneIp a1) (getOneIp a2) c rs"
    apply(subst (asm) groupWIs_def)
    apply(subst (asm) Let_def)+
    by fast
  have "\<forall>w\<in>set (concat (groupWIs c rs)). \<not> wordinterval_empty w"
    apply(subst groupWIs_def)
    apply(subst Let_def)+
    apply(subst groupF_set_lem)
    using getParts_nonempty getParts_def by auto
  from this asm have "\<forall>w \<in> set V. \<not> wordinterval_empty w" by auto
  from this b2 getOneIp_elem
    have b3: "\<forall>w1\<in>set (map wordinterval_to_set V). \<forall>w2\<in>set (map wordinterval_to_set V). 
           \<exists>ip1\<in> w1. \<exists>ip2\<in>w2.
           same_fw_behaviour_one ip1 ip2 c rs" by (simp) (blast)
  from groupParts_same_fw_wi0 asm 
    have "\<forall>A\<in>set (map wordinterval_to_set V). \<forall>a1\<in> A. \<forall>a2\<in> A. same_fw_behaviour_one a1 a2 c rs" 
    by metis
  from sameFw_behave_sets[OF this b3]
  show "\<forall>w1 \<in> set V. \<forall>w2 \<in> set V.
   \<forall>a1 \<in> wordinterval_to_set w1. \<forall>a2 \<in> wordinterval_to_set w2. same_fw_behaviour_one a1 a2 c rs"
  by force
qed

lemma groupParts_same_fw_wi2: "V \<in> set (groupWIs c rs) \<Longrightarrow>
                               \<forall>ip1 \<in> \<Union> set (map wordinterval_to_set V).
                               \<forall>ip2 \<in> \<Union> set (map wordinterval_to_set V).
                               same_fw_behaviour_one ip1 ip2 c rs"
  using groupParts_same_fw_wi0 groupParts_same_fw_wi1 by simp

lemma groupWIs_same_fw_not2: "A \<in> set (groupWIs c rs) \<Longrightarrow> B \<in> set (groupWIs c rs) \<Longrightarrow> 
                                A \<noteq> B \<Longrightarrow>
                                \<forall>ip1 \<in> \<Union> set (map wordinterval_to_set A).
                                \<forall>ip2 \<in> \<Union> set (map wordinterval_to_set B).
                                \<not> same_fw_behaviour_one ip1 ip2 c rs"
  using groupWIs_same_fw_not by fast

(*I like this version -- corny*)
lemma "A \<in> set (groupWIs c rs) \<Longrightarrow> B \<in> set (groupWIs c rs) \<Longrightarrow> 
                \<exists>ip1 \<in> \<Union> set (map wordinterval_to_set A).
                \<exists>ip2 \<in> \<Union> set (map wordinterval_to_set B).  same_fw_behaviour_one ip1 ip2 c rs
                \<Longrightarrow> A = B"
using groupWIs_same_fw_not2 by blast


(*TODO*)
lemma whatup: "[y\<leftarrow>ys . g b = g y] = map fst [y\<leftarrow>map (\<lambda>x. (x, g x)) ys . g b = snd y]"
  apply(induction ys arbitrary: g b)
  apply(simp)
by fastforce

lemma whatup1: "(map (\<lambda>x. (x, f x)) [y\<leftarrow>xs . f x \<noteq> f y]) = [y\<leftarrow>map (\<lambda>x. (x, f x)) xs . f x \<noteq> snd y]"
  apply(induction xs)
  apply(simp)
  apply(simp)
by fastforce

lemma groupF_tuple: "groupF f xs = map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) xs))"
  apply(induction f xs rule: groupF.induct)
  apply(simp)
  apply(simp)
  apply(rule conjI)
    apply(rename_tac b ys g)
    using whatup apply fast
    apply(rename_tac b ys g)
using whatup1 by metis



(*The function uses
    map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) P))
  instead of
    groupF f P
  for the following reasons:
    groupF executes its compare function (first parameter) very often; it always tests for (f x = f y).
    The function f we use here is really expensive. At least polyML does not share the result of f but 
    (probably) always recomputes (part of) it. The optimization pre-computes f and tells groupF to use
    a really cheap function (snd) to compare. The lemma groupF_tuple tells that those are equal.

  TODO: is this also faster for Haskell?*)
definition groupWIs1 :: "'a parts_connection_scheme \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs1 c rs = (let P = getParts rs in
                      (let W = map getOneIp P in 
                       (let f = (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs) W,
                                       map (\<lambda>s. runFw s (getOneIp wi) c rs) W)) in
                      map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) P)))))"

lemma groupWIs_groupWIs1_equi: "groupWIs1 c rs = groupWIs c rs"
  apply(subst groupWIs1_def)
  apply(subst groupWIs_def)
using groupF_tuple by metis

definition simple_conn_matches :: "simple_match \<Rightarrow> parts_connection \<Rightarrow> bool" where
    "simple_conn_matches m c \<longleftrightarrow>
      (match_iface (iiface m) (pc_iiface c)) \<and>
      (match_iface (oiface m) (pc_oiface c)) \<and>
      (match_proto (proto m) (pc_proto c)) \<and>
      (simple_match_port (sports m) (pc_sport c)) \<and>
      (simple_match_port (dports m) (pc_dport c))"

lemma filter_conn_fw_lem: 
  "runFw s d c (filter (\<lambda>r. simple_conn_matches (match_sel r) c) rs) = runFw s d c rs"
  apply(simp add: runFw_def simple_conn_matches_def match_sel_def)
  apply(induction rs "\<lparr>p_iiface = pc_iiface c, p_oiface = pc_oiface c,
                       p_src = s, p_dst = d, p_proto = pc_proto c, 
                       p_sport = pc_sport c, p_dport = pc_dport c,
                       p_tcp_flags = {TCP_SYN},
                       p_tag_ctstate = pc_tag_ctstate c\<rparr>"
        rule: simple_fw.induct)
  apply(simp add: simple_matches.simps)+
done


(*TODO: performance
  despite optimization, this function takes quite long and can be optimized
  possible optimization:
  1) the firewall evaluations could be halved, essentially, we are constructing a full access control
     matrix for inbound and outbound connections of each partition member. This matrix is symmetric.
     It would be enough to construct half of it.
  2) The firewall is evaluated very often. Rules that will definitely not match (w.r.t. the parts_connection)
      can be removed.*)
definition groupWIs2 :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs2 c rs =  (let P = getParts rs in
                       (let W = map getOneIp P in 
                       (let filterW = (filter (\<lambda>r. simple_conn_matches (match_sel r) c) rs) in
                         (let f = (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c filterW) W,
                                         map (\<lambda>s. runFw s (getOneIp wi) c filterW) W)) in
                      map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) P))))))"

lemma groupWIs1_groupWIs2_equi: "groupWIs2 c rs = groupWIs1 c rs"
  by(simp add: groupWIs2_def groupWIs1_def filter_conn_fw_lem)


lemma groupWIs_code[code]: "groupWIs c rs = groupWIs2 c rs"
  using groupWIs1_groupWIs2_equi groupWIs_groupWIs1_equi by metis

lemma wordinterval_unifier: "wordinterval_to_set 
          (wordinterval_compress (foldr wordinterval_union xs Empty_WordInterval)) =
          \<Union> set (map wordinterval_to_set xs)"
  apply simp
  apply(induction xs)
   apply(simp_all add: wordinterval_compress)
  done



(************* BEGIN SCRATCH ***************)
fun matching_dsts :: "ipv4addr \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where
  "matching_dsts _ [] _ = Empty_WordInterval" |
  "matching_dsts s ((SimpleRule m Accept)#rs) acc_dropped =
      (if simple_match_ip (src m) s then
         wordinterval_union (wordinterval_setminus (ipv4_cidr_tuple_to_interval (dst m)) acc_dropped) (matching_dsts s rs acc_dropped)
       else
         matching_dsts s rs acc_dropped)" |
  "matching_dsts s ((SimpleRule m Drop)#rs) acc_dropped =
      (if simple_match_ip (src m) s then
         matching_dsts s rs (wordinterval_union (ipv4_cidr_tuple_to_interval (dst m)) acc_dropped)
       else
         matching_dsts s rs acc_dropped)"

(*a copy of matching_dsts*)
fun matching_srcs :: "ipv4addr \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where
  "matching_srcs _ [] _ = Empty_WordInterval" |
  "matching_srcs d ((SimpleRule m Accept)#rs) acc_dropped =
      (if simple_match_ip (dst m) d then
         wordinterval_union (wordinterval_setminus (ipv4_cidr_tuple_to_interval (src m)) acc_dropped) (matching_srcs d rs acc_dropped)
       else
         matching_srcs d rs acc_dropped)" |
  "matching_srcs d ((SimpleRule m Drop)#rs) acc_dropped =
      (if simple_match_ip (dst m) d then
         matching_srcs d rs (wordinterval_union (ipv4_cidr_tuple_to_interval (src m)) acc_dropped)
       else
         matching_srcs d rs acc_dropped)"


(**when refactoring and cleaning, first make a clear version for dsts, then copy paste for src**)

(*TODO: put into next proof*)
lemma simple_conn_matches_src_runFw_fst1: "simple_conn_matches m c \<Longrightarrow> simple_match_ip (src m) s \<Longrightarrow>
       runFw s d c (SimpleRule m simple_action.Accept # rs) = Decision FinalAllow \<longleftrightarrow>
       simple_match_ip (dst m) d \<or> runFw s d c rs = Decision FinalAllow"
  by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)
lemma simple_conn_matches_src_runFw_fst2: "\<not> simple_match_ip (src m) s \<Longrightarrow>
       runFw s d c (SimpleRule m a # rs) = Decision FinalAllow \<longleftrightarrow>
       runFw s d c rs = Decision FinalAllow"
  apply(cases a)
   by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)+
lemma simple_conn_matches_src_runFw_fst3: "simple_conn_matches m c \<Longrightarrow> simple_match_ip (src m) s \<Longrightarrow>
       runFw s d c (SimpleRule m simple_action.Drop # rs) = Decision FinalAllow \<longleftrightarrow>
       \<not> simple_match_ip (dst m) d \<and> runFw s d c rs = Decision FinalAllow"
  by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)


lemma simple_conn_matches_dst_runFw_fst1: "simple_conn_matches m c \<Longrightarrow> simple_match_ip (dst m) d \<Longrightarrow>
       runFw s d c (SimpleRule m simple_action.Accept # rs) = Decision FinalAllow \<longleftrightarrow>
       simple_match_ip (src m) s \<or> runFw s d c rs = Decision FinalAllow"
  by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)
lemma simple_conn_matches_dst_runFw_fst2: "\<not> simple_match_ip (dst m) d \<Longrightarrow>
       runFw s d c (SimpleRule m a # rs) = Decision FinalAllow \<longleftrightarrow>
       runFw s d c rs = Decision FinalAllow"
  apply(cases a)
   by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)+
lemma simple_conn_matches_dst_runFw_fst3: "simple_conn_matches m c \<Longrightarrow> simple_match_ip (dst m) d \<Longrightarrow>
       runFw s d c (SimpleRule m simple_action.Drop # rs) = Decision FinalAllow \<longleftrightarrow>
       \<not> simple_match_ip (src m) s \<and> runFw s d c rs = Decision FinalAllow"
  by(simp add: simple_conn_matches_def runFw_def simple_matches.simps)

(*TOOD: move to next proof?*)
lemma wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip:
  "s \<in> wordinterval_to_set (ipv4_cidr_tuple_to_interval d) \<longleftrightarrow> simple_match_ip d s"
  apply(cases d)
  using ipv4range_to_set_def ipv4range_to_set_ipv4_cidr_tuple_to_interval by auto
lemma wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set:
  "wordinterval_to_set (ipv4_cidr_tuple_to_interval ip) = {d. simple_match_ip ip d}"
  using wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip by blast


lemma matching_dsts_pull_out_accu:
  "wordinterval_to_set (matching_dsts s rs (wordinterval_union a1 a2)) = wordinterval_to_set (matching_dsts s rs a2) - wordinterval_to_set a1"
  apply(induction s rs a2 arbitrary: a1 a2 rule: matching_dsts.induct)
     apply(simp_all)
  by blast+
lemma matching_srcs_pull_out_accu:
  "wordinterval_to_set (matching_srcs d rs (wordinterval_union a1 a2)) = wordinterval_to_set (matching_srcs d rs a2) - wordinterval_to_set a1"
  apply(induction d rs a2 arbitrary: a1 a2 rule: matching_srcs.induct)
     apply(simp_all)
  by blast+

lemma matching_dsts: "\<forall>r \<in> set rs. simple_conn_matches (match_sel r) c \<Longrightarrow>
        wordinterval_to_set (matching_dsts s rs Empty_WordInterval) = {d. runFw s d c rs = Decision FinalAllow}"
  apply(induction rs)
   apply(simp add: runFw_def; fail)
  apply(simp)
  apply(rename_tac r rs, case_tac r)
  apply(rename_tac m a, case_tac a)
   apply(simp)
   apply(intro conjI impI)
    apply(simp add: simple_conn_matches_src_runFw_fst1)
    apply(simp add: wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set)
    apply blast
   apply(simp add: simple_conn_matches_src_runFw_fst2; fail)
  apply(simp)
  apply(intro conjI impI)
   apply(simp add: simple_conn_matches_src_runFw_fst3)
   apply(simp add: matching_dsts_pull_out_accu)
   apply(simp add: wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set)
   apply blast
  apply(simp add: simple_conn_matches_src_runFw_fst2; fail)
 done
lemma matching_srcs: "\<forall>r \<in> set rs. simple_conn_matches (match_sel r) c \<Longrightarrow>
        wordinterval_to_set (matching_srcs d rs Empty_WordInterval) = {s. runFw s d c rs = Decision FinalAllow}"
  apply(induction rs)
   apply(simp add: runFw_def; fail)
  apply(simp)
  apply(rename_tac r rs, case_tac r)
  apply(rename_tac m a, case_tac a)
   apply(simp)
   apply(intro conjI impI)
    apply(simp add: simple_conn_matches_dst_runFw_fst1)
    apply(simp add: wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set)
    apply blast
   apply(simp add: simple_conn_matches_dst_runFw_fst2; fail)
  apply(simp)
  apply(intro conjI impI)
   apply(simp add: simple_conn_matches_dst_runFw_fst3)
   apply(simp add: matching_srcs_pull_out_accu)
   apply(simp add: wordinterval_to_set_ipv4_cidr_tuple_to_interval_simple_match_ip_set)
   apply blast
  apply(simp add: simple_conn_matches_dst_runFw_fst2; fail)
 done

(* okay, if wordintervals were ordered and we could have log-time lookup time, this would really speed up the groupWIs2 thing.*)
lemma matching_dsts_filterW_TODO_delete: "filterW = filter (\<lambda>r. simple_conn_matches (match_sel r) c) rs \<Longrightarrow>
       runFw s d c filterW = Decision FinalAllow \<longleftrightarrow> wordinterval_element d (matching_dsts s filterW Empty_WordInterval)"
  apply(simp)
  apply(subst matching_dsts[where c=c])
   apply(simp; fail)
  apply(thin_tac _)
  apply(rule)
   apply(simp_all)
  done
lemma matching_srcs_filterW_TODO_delete: "filterW = filter (\<lambda>r. simple_conn_matches (match_sel r) c) rs \<Longrightarrow>
       runFw s d c filterW = Decision FinalAllow \<longleftrightarrow> wordinterval_element s (matching_srcs d filterW Empty_WordInterval)"
  apply(simp)
  apply(subst matching_srcs[where c=c])
   apply(simp; fail)
  apply(thin_tac _)
  apply(rule)
   apply(simp_all)
  done

(*TODO: if we can get wordinterval_element to log runtime (this should be possible! maybe we want to
  use a type from the Collections to store wordintervals), then this should really improve the runtime!*)
definition groupWIs3_default_policy :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs3_default_policy c rs =  (let P = getParts rs in
                       (let W = map getOneIp P in 
                       (let filterW = (filter (\<lambda>r. simple_conn_matches (match_sel r) c) rs) in
                         (let f = (\<lambda>wi. let mtch_dsts = (matching_dsts (getOneIp wi) filterW Empty_WordInterval);
                                            mtch_srcs = (matching_srcs (getOneIp wi) filterW Empty_WordInterval) in 
                                        (map (\<lambda>d. wordinterval_element d mtch_dsts) W,
                                         map (\<lambda>s. wordinterval_element s mtch_srcs) W)) in
                      map (map fst) (groupF snd (map (\<lambda>x. (x, f x)) P))))))"



(*TODO: move to simple_firewall.*)

fun has_default_policy :: "simple_rule list \<Rightarrow> bool" where
  "has_default_policy [] = False" |
  "has_default_policy [(SimpleRule m _)] = (m = simple_match_any)" |
  "has_default_policy (_#rs) = has_default_policy rs"

lemma has_default_policy: "has_default_policy rs \<Longrightarrow> simple_fw rs p = Decision FinalAllow \<or> simple_fw rs p = Decision FinalDeny"
  apply(induction rs rule: has_default_policy.induct)
    apply(simp;fail)
   apply(simp_all)
   apply(rename_tac a, case_tac a)
    apply(simp_all add: simple_match_any)
  apply(rename_tac r1 r2 rs)
  apply(case_tac r1, rename_tac m a, case_tac a)
   apply(simp_all)
 done

lemma has_default_policy_runFw: "has_default_policy rs \<Longrightarrow> runFw s d c rs = Decision FinalAllow \<or> runFw s d c rs = Decision FinalDeny"
  by(simp add: runFw_def has_default_policy)

lemma has_default_policy_fst: "has_default_policy rs \<Longrightarrow> has_default_policy (r#rs)"
 apply(cases r, rename_tac m a, simp)
 apply(case_tac rs)
 by(simp_all)

lemma simple_conn_matches_simple_match_any: "simple_conn_matches simple_match_any c"
  apply(simp add: simple_conn_matches_def)
  apply(simp add: simple_match_any_def ipv4range_set_from_prefix_0 match_ifaceAny)
  apply(subgoal_tac "(65535::16 word) = max_word")
   apply(simp)
  by(simp add: max_word_def)
lemma has_default_policy_simple_conn_matches:
  "has_default_policy rs \<Longrightarrow> has_default_policy [r\<leftarrow>rs . simple_conn_matches (match_sel r) c]"
  apply(induction rs rule: has_default_policy.induct)
    apply(simp; fail)
   apply(simp add: simple_conn_matches_simple_match_any; fail)
  apply(simp)
  apply(intro conjI)
   apply(simp split: split_if_asm; fail)
  apply(simp add: has_default_policy_fst split: split_if_asm)
  done

lemma map_over_tuples_equal_helper:
  assumes "\<forall>w \<in> set W. (f1 x) w = (f1 y) w \<longleftrightarrow> (f2 x) w =  (f2 y) w"
          and "\<forall>w \<in> set W. (g1 x) w = (g1 y) w \<longleftrightarrow> (g2 x) w =  (g2 y) w"
     shows "
       ((map (f1 x) W, map (g1 x) W) = (map (f1 y) W, map (g1 y) W)) 
       \<longleftrightarrow>
       ((map (f2 x) W, map (g2 x) W) = (map (f2 y) W, map (g2 y) W))"
proof -
  from assms(1) have 1: "(map (f1 x) W = map (f1 y) W \<longleftrightarrow> map (f2 x) W = map (f2 y) W)" by(induction W)(simp_all)
  from assms(2) have 2: "(map (g1 x) W = map (g1 y) W \<longleftrightarrow> map (g2 x) W = map (g2 y) W)" by(induction W)(simp_all)
  from 1 2 show ?thesis by fast
qed

lemma has_default_policy_groupF: "has_default_policy rs \<Longrightarrow> 
       groupF (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs = Decision FinalAllow) (map getOneIp W),
                     map (\<lambda>s. runFw s (getOneIp wi) c rs = Decision FinalAllow) (map getOneIp W))) W =
       groupF (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs) (map getOneIp W),
                     map (\<lambda>s. runFw s (getOneIp wi) c rs) (map getOneIp W))) W"
apply(rule groupF_cong)
apply(intro ballI)
apply(rule map_over_tuples_equal_helper)
 apply(simp_all)
 apply(intro ballI)
 using has_default_policy_runFw apply metis
apply(intro ballI)
using has_default_policy_runFw apply metis
done

lemma groupWIs3_default_policy_groupWIs2: "has_default_policy rs \<Longrightarrow> groupWIs2 c rs = groupWIs3_default_policy c rs"
  apply(simp add: groupWIs3_default_policy_def groupWIs_code[symmetric])
  apply(subst groupF_tuple[symmetric])
  apply(simp add: Let_def)
  apply(subst matching_dsts_filterW_TODO_delete[simplified, symmetric, where c=c])
   apply blast
  apply(subst matching_srcs_filterW_TODO_delete[simplified, symmetric, where c=c])
   apply blast
  thm has_default_policy_groupF[simplified]
  apply(subst has_default_policy_groupF[simplified])
   defer
  apply(simp add: groupWIs_def Let_def filter_conn_fw_lem)
  apply(simp add: has_default_policy_simple_conn_matches)
  done


definition groupWIs3 :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs3 c rs = (if has_default_policy rs then groupWIs3_default_policy c rs else groupWIs2 c rs)"

lemma groupWIs3: "groupWIs3 = groupWIs"
  apply(simp add: fun_eq_iff)
  apply(intro allI, rename_tac c rs)
  apply(simp add: groupWIs3_def)
  by (simp add: groupWIs_code groupWIs3_default_policy_groupWIs2) 

(************* END SCRATCH ***************)


(*construct partitions. main function!*)
definition build_ip_partition :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list" where
  "build_ip_partition c rs = map (\<lambda>xs. wordinterval_compress (foldr wordinterval_union xs Empty_WordInterval)) (groupWIs3 c rs)"


theorem build_ip_partition_same_fw: "V \<in> set (build_ip_partition c rs) \<Longrightarrow>
                               \<forall>ip1 \<in> wordinterval_to_set V.
                               \<forall>ip2 \<in> wordinterval_to_set V.
                               same_fw_behaviour_one ip1 ip2 c rs"
  apply(simp add: build_ip_partition_def groupWIs3)
using wordinterval_unifier groupParts_same_fw_wi2 by blast

theorem build_ip_partition_same_fw_min: "A \<in> set (build_ip_partition c rs) \<Longrightarrow> B \<in> set (build_ip_partition c rs) \<Longrightarrow> 
                                A \<noteq> B \<Longrightarrow>
                                \<forall>ip1 \<in> wordinterval_to_set A.
                                \<forall>ip2 \<in> wordinterval_to_set B.
                                \<not> same_fw_behaviour_one ip1 ip2 c rs"
  apply(simp add: build_ip_partition_def groupWIs3)
using wordinterval_unifier groupWIs_same_fw_not2 by fast (*1s*)

(*TODO: move?*)
fun pretty_wordinterval where
  "pretty_wordinterval (WordInterval ip1 ip2) = (if ip1 = ip2
                                                 then ipv4addr_toString ip1
                                                 else ''('' @ ipv4addr_toString ip1 @ '' - '' @
                                                      ipv4addr_toString ip2 @ '')'')" |
  "pretty_wordinterval (RangeUnion r1 r2) = pretty_wordinterval r1 @ '' u '' @
                                            pretty_wordinterval r2"


(*construct an ip partition and print it in some useable format
  returns:
  (vertices, edges) where
  vertices = (name, list of ip addresses this vertex corresponds to)
  and edges = (name \<times> name) list
*)
(*TODO: can we use collect srcs or collect dsts here too?*)
fun build_ip_partition_pretty 
  :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> (string \<times> string) list \<times> (string \<times> string) list" 
  where
  "build_ip_partition_pretty c rs = (let W = build_ip_partition c rs in
                  (let R = map getOneIp W 
      in
                         (let U = concat (map (\<lambda>x. map (\<lambda>y. (x,y)) R) R) in 
     (zip (map ipv4addr_toString R) (map pretty_wordinterval W), 
     map (\<lambda>(x,y). (ipv4addr_toString x, ipv4addr_toString y)) (filter (\<lambda>(a,b). runFw a b c rs = Decision FinalAllow) U)))))"


definition parts_connection_ssh where "parts_connection_ssh = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=22, pc_tag_ctstate=CT_New\<rparr>"

definition parts_connection_http where "parts_connection_http = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=80, pc_tag_ctstate=CT_New\<rparr>"





(*corny stuff -- TODO: move*)

lemma "partIps (WordInterval (1::ipv4addr) 1) [WordInterval 0 1] = [WordInterval 1 1, WordInterval 0 0]" by eval

lemma partIps_length: "length (partIps s ts) \<le> (length ts) * 2"
apply(induction ts arbitrary: s )
 apply(simp)
apply simp
using le_Suc_eq by blast


lemma partitioningIps_length: "length (partitioningIps ss ts) \<le> (2^length ss) * length ts"
apply(induction ss arbitrary: ts)
 apply(simp; fail)
apply(subst partitioningIps.simps)
apply(simp)
apply(subgoal_tac "length (partIps a (partitioningIps ss ts)) \<le> length (partitioningIps ss ts) * 2")
 prefer 2 
 using partIps_length apply fast
(*sledgehammer*)
proof -
  fix a :: "'a wordinterval" and ssa :: "'a wordinterval list" and tsa :: "'a wordinterval list"
  assume a1: "\<And>ts. length (partitioningIps ssa ts) \<le> 2 ^ length ssa * length ts"
  assume a2: "length (partIps a (partitioningIps ssa tsa)) \<le> length (partitioningIps ssa tsa) * 2"
  have "\<not> 2 ^ length ssa * length tsa < length (partitioningIps ssa tsa)"
    using a1 not_less by blast
  thus "length (partIps a (partitioningIps ssa tsa)) \<le> 2 * 2 ^ length ssa * length tsa"
    using a2 by linarith
qed


lemma getParts_length: "length (getParts rs) \<le> 2^(2 * length rs)"
proof -
  from partitioningIps_length[where ss="extract_IPSets rs" and ts="[wordinterval_UNIV]"] have
    1: "length (partitioningIps (extract_IPSets rs) [wordinterval_UNIV]) \<le> 2 ^ length (extract_IPSets rs)" by simp
  from extract_IPSets_length have "(2::nat) ^ length (extract_IPSets rs) \<le> 2 ^ (2 * length rs)" by simp
  with 1 have "length (partitioningIps (extract_IPSets rs) [wordinterval_UNIV]) \<le> 2 ^ (2 * length rs)" by linarith
  thus ?thesis by(simp add: getParts_def) 
qed

value[code] "partitioningIps [WordInterval (0::ipv4addr) 0] [WordInterval 0 2, WordInterval 0 2]"






end                            
