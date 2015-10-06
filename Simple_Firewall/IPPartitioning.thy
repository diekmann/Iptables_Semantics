(*Author: Max Haslbeck, 2015*)
theory IPPartitioning
imports Main
        "SimpleFw_Semantics"
        "../Common/SetPartitioning"
        "../Primitive_Matchers/Common_Primitive_toString"
      (*  "../Examples/TUM_Net_Firewall/TUM_TestFW" *)
      (*  "Example_Firewall" *)
begin

definition "example = [
 SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = (0, 24), dst = (1, 32), proto = ProtoAny, sports = (1000, 1000), dports = (0x16, 0x16)\<rparr> simple_action.Accept,
SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = (0, 0), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF), dports = (0, 0xFFFF)\<rparr> simple_action.Drop]"

definition "example1 = [
 SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = ((ipv4addr_of_dotdecimal (131,159,0,0)), 16), dst = ((ipv4addr_of_dotdecimal (131,159,0,0)), 16), proto = ProtoAny, sports = (0, 0xFFFF), dports = (0, 0xFFFF)\<rparr> simple_action.Accept,
 SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = ((ipv4addr_of_dotdecimal (131,159,0,0)), 16), dst = ((ipv4addr_of_dotdecimal (123,123,123,123)), 32), proto = Proto TCP, sports = (1024, 0xFFFF), dports = (22, 22)\<rparr> simple_action.Accept,
 SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = ((ipv4addr_of_dotdecimal (123,0,0,0)), 8), dst = ((ipv4addr_of_dotdecimal (131,159,0,1)), 32), proto = Proto TCP, sports = (1024, 0xFFFF), dports = (80, 80)\<rparr> simple_action.Accept,
 SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', 
    src = (0, 0), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF), dports = (0, 0xFFFF)\<rparr> simple_action.Drop]"

(* Dat Geschenk von Cornelius *) 
lemma gschenk0_helper: "B \<subseteq> (case src m of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa) \<or> B \<inter> (case src m of (x, xa) 
                \<Rightarrow> ipv4range_set_from_bitmask x xa) = {} \<Longrightarrow>
       s1 \<in> B \<Longrightarrow>
       s2 \<in> B \<Longrightarrow>
       simple_matches m (p\<lparr>p_src := s1\<rparr>) \<longleftrightarrow> simple_matches m (p\<lparr>p_src := s2\<rparr>)"
apply(case_tac m)
apply(rename_tac iiface oiface srca dst proto sports dports)
apply(case_tac srca)
apply(simp)
apply(simp add: simple_matches.simps)
by blast

lemma gschenk0: "\<forall>A \<in> (\<lambda>(base,len).
               ipv4range_set_from_bitmask base len) ` src ` match_sel ` set rs. B \<subseteq> A \<or> B \<inter> A = {} \<Longrightarrow>
  s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow>
    simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>)"
apply(induction rs)
 apply(simp)
apply(rename_tac r rs)
apply(case_tac r, rename_tac m a)
apply(simp)
apply(case_tac a)
 apply(simp)
 using gschenk0_helper apply meson
apply(simp)
using gschenk0_helper apply meson
done

lemma gschenk1_helper: "B \<subseteq> (case dst m of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa) \<or> B \<inter> (case dst m of (x, xa) 
                \<Rightarrow> ipv4range_set_from_bitmask x xa) = {} \<Longrightarrow>
       s1 \<in> B \<Longrightarrow>
       s2 \<in> B \<Longrightarrow>
       simple_matches m (p\<lparr>p_dst := s1\<rparr>) \<longleftrightarrow> simple_matches m (p\<lparr>p_dst := s2\<rparr>)"
apply(case_tac m)
apply(rename_tac iiface oiface src dsta proto sports dports)
apply(case_tac dsta)
apply(simp)
apply(simp add: simple_matches.simps)
by blast


lemma gschenk1: "\<forall>A \<in> (\<lambda>(base,len).
               ipv4range_set_from_bitmask base len) ` dst ` match_sel ` set rs. B \<subseteq> A \<or> B \<inter> A = {} \<Longrightarrow>
  s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow>
    simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
apply(induction rs)
 apply(simp)
apply(rename_tac r rs)
apply(case_tac r, rename_tac m a)
apply(simp)
apply(case_tac a)
 apply(simp)
 using gschenk1_helper apply meson
apply(simp)
using gschenk1_helper apply meson
done


fun extract_IPSets_generic0 :: "(simple_match \<Rightarrow> 32 word \<times> nat) \<Rightarrow> simple_rule list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets_generic0 _ [] = []" |
  "extract_IPSets_generic0 sel ((SimpleRule m _)#ss) = (ipv4_cidr_tuple_to_interval (sel m)) #
                                                       (extract_IPSets_generic0 sel ss)"

fun extract_IPSets_tail_before :: "simple_rule list \<Rightarrow> (32 wordinterval) list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets_tail_before [] ts = ts" |
  "extract_IPSets_tail_before ((SimpleRule m _)#ss) ts = extract_IPSets_tail_before ss 
                                                  ((ipv4_cidr_tuple_to_interval (src m)) #
                                                  ((ipv4_cidr_tuple_to_interval (dst m)))#ts)"

fun extract_IPSets_tail :: "simple_rule list \<Rightarrow> (32 wordinterval) list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets_tail [] ts = ts" |
  "extract_IPSets_tail ((SimpleRule m _)#ss) ts = extract_IPSets_tail ss 
                                                  ((ipv4_cidr_tuple_to_interval (src m)) #
                                                  ((ipv4_cidr_tuple_to_interval (dst m))#ts))"


lemma extract_equi0: "set (map wordinterval_to_set (extract_IPSets_generic0 sel rs))
                     = (\<lambda>(base,len). ipv4range_set_from_bitmask base len) ` sel ` match_sel ` set rs"
  apply(induction rs)
  apply(simp)
  apply(simp_all)
by (metis (no_types, hide_lams) extract_IPSets_generic0.simps(2) image_insert ipv4range_to_set_def
    ipv4range_to_set_ipv4_cidr_tuple_to_interval list.simps(15) 
    old.prod.case old.prod.exhaust simple_rule.collapse)

lemma src_ipPart: "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 src rs))) A \<Longrightarrow>
       B \<in> A \<Longrightarrow>
       s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow> simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>)"
  apply(subst (asm) ipPartition_def)
by (metis (full_types) Int_commute extract_equi0 gschenk0)

lemma dst_ipPart: "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 dst rs))) A \<Longrightarrow>
       B \<in> A \<Longrightarrow>
       s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow> simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
  apply(subst (asm) ipPartition_def)
by (metis (full_types) Int_commute extract_equi0 gschenk1)

lemma srcdst_ipPart: "ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 src rs))) A \<and>
       ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 dst rs))) A \<Longrightarrow>
       B \<in> A \<Longrightarrow> s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow> 
       simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>) \<and>
       simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
using dst_ipPart src_ipPart by blast


fun extract_IPSets :: "simple_rule list \<Rightarrow> (32 wordinterval) list" where
  "extract_IPSets rs = (extract_IPSets_generic0 src rs) @ (extract_IPSets_generic0 dst rs)"

lemma extract_IPSets_helper: "ipPartition (set (map wordinterval_to_set (extract_IPSets rs))) A \<Longrightarrow>
       ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 src rs))) A  \<and>
       ipPartition (set (map wordinterval_to_set (extract_IPSets_generic0 dst rs))) A "
  apply(simp_all add: ipPartition_def)
done

lemma extract_IPSets_lem: "ipPartition (set (map wordinterval_to_set (extract_IPSets rs))) A \<Longrightarrow>
                           B \<in> A \<Longrightarrow> s1 \<in> B \<Longrightarrow> s2 \<in> B \<Longrightarrow> 
                           simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>) \<and>
                           simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
  using extract_IPSets_helper srcdst_ipPart by blast


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
  apply(induction ts arbitrary: s)
  by (simp_all)

lemma partitioningIps_equi: "map wordinterval_to_set (partitioningIps ss ts)
       = (partitioning1 (map wordinterval_to_set ss) (map wordinterval_to_set ts))"
  apply(induction ss arbitrary: ts)
  apply(simp_all add: partIps_equi)
done


(* EXAMPLES/DUMP *)

definition "example_list = map ipv4_cidr_tuple_to_interval 
                           [(ipv4addr_of_dotdecimal (0,0,0,0), 1),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 2),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 3),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 4),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 5),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 6),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 7),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 8),
                            (ipv4addr_of_dotdecimal (0,0,0,0), 0)]"

lemma ipPartitioning_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow> 
   ipPartition (set (map wordinterval_to_set ss)) 
               (set (map wordinterval_to_set (partitioningIps ss ts)))"
by (metis ipPartitioning_helper_opt partitioningIps_equi wordinterval_list_to_set.simps)

lemma complete_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow> 
   complete (set (map wordinterval_to_set ts)) 
               (set (map wordinterval_to_set (partitioningIps ss ts)))"
by (metis complete_helper partitioningIps_equi wordinterval_list_to_set.simps)

lemma disjoint_partitioningIps: 
  "{} \<notin> set (map wordinterval_to_set ts) \<Longrightarrow> disjoint_list_rec (map wordinterval_to_set ts) \<Longrightarrow> 
   (wordinterval_list_to_set ss) \<subseteq> (wordinterval_list_to_set ts) \<Longrightarrow>
   disjoint_list_rec (map wordinterval_to_set (partitioningIps ss ts))"
by (simp add: partitioning1_disjoint partitioningIps_equi)


lemma ipPartitioning_partitioningIps1: "ipPartition (set (map wordinterval_to_set ss)) 
                   (set (map wordinterval_to_set (partitioningIps ss [wordinterval_UNIV])))"
  apply(rule ipPartitioning_partitioningIps)
    apply(simp_all)
  done
                  
definition getParts :: "simple_rule list \<Rightarrow> 32 wordinterval list" where
   "getParts rs = partitioningIps (extract_IPSets rs) [wordinterval_UNIV]"

lemma ipParts_getParts: "ipPartition (set (map wordinterval_to_set (extract_IPSets rs)))
                                     (set (map wordinterval_to_set (getParts rs)))"
  apply(subst getParts_def)
  apply(subst ipPartitioning_partitioningIps1)
  by(simp)


lemma getParts_complete0: "complete (set (map wordinterval_to_set [wordinterval_UNIV]))
                                   (set (map wordinterval_to_set (getParts rs)))"
  apply(subst getParts_def)
  apply(rule complete_partitioningIps)
  apply(simp_all)
done

lemma getParts_complete1: "wordinterval_to_set wordinterval_UNIV =
                          \<Union> (set (map wordinterval_to_set [wordinterval_UNIV]))"
  by(simp)

lemma getParts_complete2: "wordinterval_to_set wordinterval_UNIV =
                           \<Union> (set (map wordinterval_to_set (getParts rs)))"
  apply(subst getParts_complete1)
  apply(insert getParts_complete0)
  apply(simp add: complete_def)
done

lemma getParts_complete3: " \<Union> (set (map wordinterval_to_set (getParts rs))) = UNIV"
  using getParts_complete2 by simp

lemma getParts_disjoint: "disjoint_list_rec (map wordinterval_to_set (getParts rs))"
  apply(subst getParts_def)
  apply(rule disjoint_partitioningIps)
  apply(simp_all)
done

theorem getParts_samefw: 
  "A \<in> set (map wordinterval_to_set (getParts rs)) \<Longrightarrow>  s1 \<in> A \<Longrightarrow> s2 \<in> A \<Longrightarrow> 
   simple_fw rs (p\<lparr>p_src:=s1\<rparr>) = simple_fw rs (p\<lparr>p_src:=s2\<rparr>) \<and>
   simple_fw rs (p\<lparr>p_dst:=s1\<rparr>) = simple_fw rs (p\<lparr>p_dst:=s2\<rparr>)"
  apply(rule extract_IPSets_lem[of rs _ A])
  using ipParts_getParts by blast

lemma partList3_nonempty: "\<forall>t \<in> set ts. \<not> wordinterval_empty t 
       \<Longrightarrow> {} \<notin> set (map wordinterval_to_set (partIps s ts))"
  apply(induction ts arbitrary: s)
  apply(simp)
  apply(simp_all)
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
  apply(insert ineedtolearnisar partitioning_nonempty)
by(blast)

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
  apply(subst same_fw_behaviour_def)
  apply(insert getParts_samefw)
by blast

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
  apply(simp)
  apply(clarify)
  apply(erule_tac x="\<lparr>p_iiface = pc_iiface c, p_oiface = pc_oiface c, p_src = s, p_dst= ip1,
                       p_proto = pc_proto c, p_sport = pc_sport c, p_dport = pc_dport c,
                       p_tcp_flags = {TCP_SYN},
                       p_tag_ctstate = pc_tag_ctstate c\<rparr>" in allE)
  apply(simp)
done

lemma same_fw_behaviour_one_equi:
  "same_fw_behaviour_one x x c rs"
  "same_fw_behaviour_one x y c rs = same_fw_behaviour_one y x c rs"
  "same_fw_behaviour_one x y c rs \<and> same_fw_behaviour_one y z c rs \<Longrightarrow>
   same_fw_behaviour_one x z c rs"
  unfolding same_fw_behaviour_one_def by metis+

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
  "\<forall>A \<in> set (map wordinterval_to_set W). \<forall>a1 \<in> A. \<forall>a2 \<in> A. same_fw_behaviour_one a1 a2 c rs \<Longrightarrow>
   \<Union> set (map wordinterval_to_set W) = UNIV \<Longrightarrow> 
   \<forall>w \<in> set W. \<not> wordinterval_empty w \<Longrightarrow>
   (map (\<lambda>d. runFw x1 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x1 c rs) (map getOneIp W)) =
   (map (\<lambda>d. runFw x2 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x2 c rs) (map getOneIp W)) \<Longrightarrow>
   same_fw_behaviour_one x1 x2 c rs"
proof -
  assume a1: "\<forall>A \<in> set (map wordinterval_to_set W). \<forall>a1 \<in> A. \<forall>a2 \<in> A. same_fw_behaviour_one a1 a2 c rs"
  and a2: "\<Union> set (map wordinterval_to_set W) = UNIV"
  and a3: "\<forall>w \<in> set W. \<not> wordinterval_empty w"
  and a4: "(map (\<lambda>d. runFw x1 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x1 c rs) (map getOneIp W)) =
           (map (\<lambda>d. runFw x2 d c rs) (map getOneIp W), map (\<lambda>s. runFw s x2 c rs) (map getOneIp W))"
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

fun groupF ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"  where
  "groupF f [] = []" |
  "groupF f (x#xs) = (x#(filter (\<lambda>y. f x = f y) xs))#(groupF f (filter (\<lambda>y. f x \<noteq> f y) xs))"

lemma groupF_lem:
  defines "same f A \<equiv> (\<forall>a1 \<in> set A. \<forall>a2 \<in> set A. f a1 = f a2)"
  shows "\<forall>A \<in> set(groupF f xs). same f A"
  proof(induction f xs rule: groupF.induct)
  case 1 thus ?case by simp
  next
  case (2 f x xs)
  have groupF_fst: "groupF f (x # xs) = (x # [y\<leftarrow>xs . f x = f y]) # groupF f [y\<leftarrow>xs . f x \<noteq> f y]" by force
  have step: " \<forall>A\<in>set [x # [y\<leftarrow>xs . f x = f y]]. same f A" unfolding same_def by fastforce
  with 2 show ?case unfolding groupF_fst by fastforce
qed
thm groupF_lem

lemma groupF_set_lem: "set (concat (groupF f xs)) = set xs"
  apply(induction f xs rule: groupF.induct)
  apply(simp_all)
by blast

lemma groupF_set_lem1: "\<forall>X \<in> set (groupF f xs). \<forall>x \<in> set X. x \<in> set xs"
  using groupF_set_lem by fastforce

lemma groupF_lem_not : "\<And>A B. A \<in> set(groupF f xs) \<Longrightarrow> B \<in> set(groupF f xs) \<Longrightarrow> A \<noteq> B \<Longrightarrow>
     \<forall>a \<in> set A. \<forall>b \<in> set B. f a \<noteq> f b"
  apply(induction f xs rule: groupF.induct)
  apply(simp)
  apply(subst (asm) groupF.simps)+
by (smt filter_set groupF_set_lem1 member_filter set_ConsD)


definition groupWIs :: "parts_connection \<Rightarrow> simple_rule list \<Rightarrow> 32 wordinterval list list" where
  "groupWIs c rs = (let W = getParts rs in 
                       (let f = (\<lambda>wi. (map (\<lambda>d. runFw (getOneIp wi) d c rs) (map getOneIp W),
                                      map (\<lambda>s. runFw s (getOneIp wi) c rs) (map getOneIp W))) in
                       groupF f W))"

lemma groupParts_same_fw_wi0: "\<And>V. V \<in> set (groupWIs c rs) \<Longrightarrow> 
                               \<forall>w \<in> set (map wordinterval_to_set V).
                               \<forall>a1 \<in> w. \<forall>a2 \<in> w. same_fw_behaviour_one a1 a2 c rs"
proof -
  fix V assume asm: "V \<in> set (groupWIs c rs)"
  have "\<forall>A\<in>set (map wordinterval_to_set (concat (groupWIs c rs))). 
        \<forall>a1\<in>A. \<forall>a2\<in>A. same_fw_behaviour_one a1 a2 c rs"
    apply(subst groupWIs_def)
    apply(subst Let_def)+
    apply(subst set_map)
    apply(subst groupF_set_lem)
  using getParts_same_fw_behaviour same_fw_spec by fastforce
  from this asm show "\<forall>A\<in>set (map wordinterval_to_set V). \<forall>a1\<in> A. \<forall>a2\<in> A.
                          same_fw_behaviour_one a1 a2 c rs" by force
qed

lemma groupWIs_same_fw_not: "\<And>A B. A \<in> set (groupWIs c rs) \<Longrightarrow> B \<in> set (groupWIs c rs) \<Longrightarrow> 
                            A \<noteq> B \<Longrightarrow>
                             \<forall>aw \<in> set (map wordinterval_to_set A).
                             \<forall>bw \<in> set (map wordinterval_to_set B).
                             \<forall>a \<in> aw. \<forall>b \<in> bw. \<not> same_fw_behaviour_one a b c rs"
proof -
  fix "A" "B" assume asm: "A \<in> set (groupWIs c rs)" "B \<in> set (groupWIs c rs)" "A \<noteq> B"
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
  "\<And>V. V \<in> set (groupWIs c rs) \<Longrightarrow> \<forall>w1 \<in> set V. \<forall>w2 \<in> set V.
   \<forall>a1 \<in> wordinterval_to_set w1. \<forall>a2 \<in> wordinterval_to_set w2. same_fw_behaviour_one a1 a2 c rs"
proof -
  fix V assume asm: "V \<in> set (groupWIs c rs)"
  from getParts_same_fw_behaviour same_fw_spec
    have b1: "\<forall>A \<in> set (map wordinterval_to_set (getParts rs)) . \<forall>a1 \<in> A. \<forall>a2 \<in> A.
              same_fw_behaviour_one a1 a2 c rs" by fast
  from getParts_nonempty
    have "\<forall>w\<in>set (getParts rs). \<not> wordinterval_empty w" apply(subst getParts_def) by auto
  from same_behave_runFw[OF b1 getParts_complete3 this]
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

definition groupWIs1 where
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

lemma wordinterval_unifier: "wordinterval_to_set (
         wordinterval_compress (foldr wordinterval_union xs Empty_WordInterval)) =
       \<Union> set (map wordinterval_to_set xs)"
  apply(induction xs)
  apply(simp_all add: wordinterval_compress)
done

fun buildParts where
  "buildParts c rs = map (\<lambda>xs. wordinterval_compress (foldr wordinterval_union xs Empty_WordInterval)) (groupWIs2 c rs)"

lemma buildParts_same_fw: "V \<in> set (buildParts c rs) \<Longrightarrow>
                               \<forall>ip1 \<in> wordinterval_to_set V.
                               \<forall>ip2 \<in> wordinterval_to_set V.
                               same_fw_behaviour_one ip1 ip2 c rs"
  apply(simp add: groupWIs1_groupWIs2_equi groupWIs_groupWIs1_equi)
using wordinterval_unifier groupParts_same_fw_wi2 by blast



lemma buildParts_same_fw_min: "A \<in> set (buildParts c rs) \<Longrightarrow> B \<in> set (buildParts c rs) \<Longrightarrow> 
                                A \<noteq> B \<Longrightarrow>
                                \<forall>ip1 \<in> wordinterval_to_set A.
                                \<forall>ip2 \<in> wordinterval_to_set B.
                                \<not> same_fw_behaviour_one ip1 ip2 c rs"
  apply(simp add: groupWIs1_groupWIs2_equi groupWIs_groupWIs1_equi)
using wordinterval_unifier groupWIs_same_fw_not2 by fast
  


fun pretty_wordinterval where
  "pretty_wordinterval (WordInterval ip1 ip2) = (if ip1 = ip2
                                                 then ipv4addr_toString ip1
                                                 else ''('' @ ipv4addr_toString ip1 @ '' - '' @
                                                      ipv4addr_toString ip2 @ '')'')" |
  "pretty_wordinterval (RangeUnion r1 r2) = pretty_wordinterval r1 @ '' u '' @
                                            pretty_wordinterval r2"


(*TODO: theorem?*)
(*What does this do?*)
(*can it use groupWIs2?*)
fun build where
  "build c rs = (let W = map (\<lambda>xs. wordinterval_compress (foldr wordinterval_union xs Empty_WordInterval)) (groupWIs2 c rs) in
                  (let R = map getOneIp W 
      in
                         (let U = concat (map (\<lambda>x. map (\<lambda>y. (x,y)) R) R) in 
     (zip (map ipv4addr_toString R) (map pretty_wordinterval W), 
     map (\<lambda>(x,y). (ipv4addr_toString x, ipv4addr_toString y)) (filter (\<lambda>(a,b). runFw a b c rs = Decision FinalAllow) U)))))"


definition ssh where "ssh = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=22, pc_tag_ctstate=CT_New\<rparr>"

definition http where "http = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=80, pc_tag_ctstate=CT_New\<rparr>"

(* was ist da los, corny??? :D *)
value[code] "wordinterval_compress
  (RangeUnion (WordInterval 0x7B7B7B7B 0x7B7B7B7B) (RangeUnion (WordInterval 0x7B000000 0x7B7B7B7A) (WordInterval 0x7B7B7B7C 0x7BFFFFFF)))::32 wordinterval"

end                            