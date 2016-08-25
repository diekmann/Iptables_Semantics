theory Ipassmt
imports Common_Primitive_Syntax
        "../Semantics_Ternary/Primitive_Normalization"
        "../../Simple_Firewall/Primitives/Iface"
        "../../Simple_Firewall/Common/IP_Addr_WordInterval_toString" (*for debug pretty-printing*)
        "../../Automatic_Refinement/Lib/Misc" (*dependnecy!*)
begin

  text\<open>A mapping from an interface to its assigned ip addresses in CIDR notation\<close>
  type_synonym 'i ipassignment="iface \<rightharpoonup> ('i word \<times> nat) list" (*technically, a set*)


subsection\<open>Sanity checking for an @{typ "'i ipassignment"}.\<close>

  text\<open>warning if interface map has wildcards\<close>
  definition ipassmt_sanity_nowildcards :: "'i ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_nowildcards ipassmt \<equiv> \<forall> iface \<in> dom ipassmt. \<not> iface_is_wildcard iface"

    text\<open>Executable of the @{typ "'i ipassignment"} is given as a list.\<close>
    lemma[code_unfold]: "ipassmt_sanity_nowildcards (map_of ipassmt) \<longleftrightarrow> (\<forall> iface \<in> fst` set ipassmt. \<not> iface_is_wildcard iface)"
      by(simp add: ipassmt_sanity_nowildcards_def Map.dom_map_of_conv_image_fst)
  
  lemma ipassmt_sanity_nowildcards_match_iface:
      "ipassmt_sanity_nowildcards ipassmt \<Longrightarrow>
       ipassmt (Iface ifce2) = None \<Longrightarrow>
       ipassmt ifce = Some a \<Longrightarrow>
       \<not> match_iface ifce ifce2"
  unfolding ipassmt_sanity_nowildcards_def using iface_is_wildcard_def match_iface_case_nowildcard by fastforce


  (* use this in all exported code*)
  (*TODO: generate useful error message in exported code*)
  definition map_of_ipassmt :: "(iface \<times> ('i word \<times> nat) list) list \<Rightarrow> iface \<rightharpoonup> ('i word \<times> nat) list" where
    "map_of_ipassmt ipassmt = (
      if
        distinct (map fst ipassmt) \<and> ipassmt_sanity_nowildcards (map_of ipassmt)
      then
        map_of ipassmt
      else undefined (*undefined_ipassmt_must_be_distinct_and_dont_have_wildcard_interfaces*))"


  text\<open>some additional (optional) sanity checks\<close>
  
  text\<open>sanity check that there are no zone-spanning interfaces\<close>
  definition ipassmt_sanity_disjoint :: "'i::len ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_disjoint ipassmt \<equiv> \<forall> i1 \<in> dom ipassmt. \<forall> i2 \<in> dom ipassmt. i1 \<noteq> i2 \<longrightarrow>
          ipcidr_union_set (set (the (ipassmt i1))) \<inter> ipcidr_union_set (set (the (ipassmt i2))) = {}"
  
  lemma[code_unfold]: "ipassmt_sanity_disjoint (map_of ipassmt) \<longleftrightarrow>
    (let Is = fst` set ipassmt in 
      (\<forall> i1 \<in> Is. \<forall> i2 \<in> Is. i1 \<noteq> i2 \<longrightarrow> wordinterval_empty (wordinterval_intersection (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i1))))  (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i2)))))))"
    apply(simp add: ipassmt_sanity_disjoint_def Map.dom_map_of_conv_image_fst)
    apply(simp add: ipcidr_union_set_def)
    apply(simp add: l2wi)
    apply(simp add: ipcidr_to_interval_def)
    using ipset_from_cidr_ipcidr_to_interval by blast
  
  
  text\<open>Checking that the ipassmt covers the complete ipv4 address space.\<close>
  definition ipassmt_sanity_complete :: "(iface \<times> ('i::len word \<times> nat) list) list \<Rightarrow> bool" where
    "ipassmt_sanity_complete ipassmt \<equiv> distinct (map fst ipassmt) \<and> (\<Union>(ipcidr_union_set ` set ` (ran (map_of ipassmt)))) = UNIV"

    lemma[code_unfold]: "ipassmt_sanity_complete ipassmt \<longleftrightarrow> distinct (map fst ipassmt) \<and> (let range = map snd ipassmt in 
        wordinterval_eq (wordinterval_Union (map (l2wi \<circ> (map ipcidr_to_interval)) range)) wordinterval_UNIV
        )"
     apply(cases "distinct (map fst ipassmt)")
      apply(simp add: ipassmt_sanity_complete_def)
      apply(simp add: Map.ran_distinct)
      apply(simp add: wordinterval_eq_set_eq wordinterval_Union)
      apply(simp add: l2wi)
      apply(simp add: ipcidr_to_interval_def)
      apply(simp add: ipcidr_union_set_def ipset_from_cidr_ipcidr_to_interval; fail)
     apply(simp add: ipassmt_sanity_complete_def)
     done



    value[code] "ipassmt_sanity_nowildcards (map_of [(Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,240), 28)])])"

  fun collect_ifaces' :: "'i::len common_primitive rule list \<Rightarrow> iface list" where
    "collect_ifaces' [] = []" |
    "collect_ifaces' ((Rule m a)#rs) = filter (\<lambda>iface. iface \<noteq> ifaceAny) (
                                      (map (\<lambda>x. case x of Pos i \<Rightarrow> i | Neg i \<Rightarrow> i) (fst (primitive_extractor (is_Iiface, iiface_sel) m))) @
                                      (map (\<lambda>x. case x of Pos i \<Rightarrow> i | Neg i \<Rightarrow> i) (fst (primitive_extractor (is_Oiface, oiface_sel) m))) @ collect_ifaces' rs)"

  definition collect_ifaces :: "'i::len common_primitive rule list \<Rightarrow> iface list" where
    "collect_ifaces rs \<equiv> mergesort_remdups (collect_ifaces' rs)"
  lemma "set (collect_ifaces rs) = set (collect_ifaces' rs)"
    by(simp add: collect_ifaces_def mergesort_remdups_correct)

  text\<open>sanity check that all interfaces mentioned in the ruleset are also listed in the ipassmt. May fail for wildcard interfaces in the ruleset.\<close>

  (*primitive_extractor requires normalized_nnf_primitives*)
  definition ipassmt_sanity_defined :: "'i::len common_primitive rule list \<Rightarrow> 'i ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_defined rs ipassmt \<equiv> \<forall> iface \<in> set (collect_ifaces rs). iface \<in> dom ipassmt"

    lemma[code]: "ipassmt_sanity_defined rs ipassmt \<longleftrightarrow> (\<forall> iface \<in> set (collect_ifaces rs). ipassmt iface \<noteq> None)"
      by(simp add: ipassmt_sanity_defined_def Map.domIff)
  
    lemma "ipassmt_sanity_defined [
         Rule (MatchAnd (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192,168,0,0)) 24))) (Match (IIface (Iface ''eth1.1017'')))) action.Accept,
         Rule (MatchAnd (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192,168,0,0)) 24))) (Match (IIface (ifaceAny)))) action.Accept,
         Rule MatchAny action.Drop]
             (map_of [(Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,240), 28)])])" by eval



  (*TODO: use and add code equation*)
  definition ipassmt_ignore_wildcard :: "'i::len ipassignment \<Rightarrow> 'i ipassignment" where
    "ipassmt_ignore_wildcard ipassmt \<equiv> \<lambda>k. case ipassmt k of None \<Rightarrow> None 
                                                           | Some ips \<Rightarrow> if ipcidr_union_set (set ips) = UNIV then None else Some ips"

  lemma ipassmt_ignore_wildcard_le: "ipassmt_ignore_wildcard ipassmt \<subseteq>\<^sub>m ipassmt"
    apply(simp add: ipassmt_ignore_wildcard_def map_le_def)
    apply(clarify)
    apply(simp split: option.split_asm split_if_asm)
    done

  definition ipassmt_ignore_wildcard_list:: "(iface \<times> ('i::len word \<times> nat) list) list \<Rightarrow> (iface \<times> ('i word \<times> nat) list) list" where
    "ipassmt_ignore_wildcard_list ipassmt = filter (\<lambda>(_,ips).  \<not> wordinterval_eq (l2wi (map ipcidr_to_interval ips)) wordinterval_UNIV) ipassmt"

  (*distinct fst ipassmt notwendig?*)
  lemma "distinct (map fst ipassmt) \<Longrightarrow>
    map_of (ipassmt_ignore_wildcard_list ipassmt) = ipassmt_ignore_wildcard (map_of ipassmt)"
      apply(simp add: ipassmt_ignore_wildcard_list_def ipassmt_ignore_wildcard_def)
      apply(simp add: wordinterval_eq_set_eq)
      apply(simp add: l2wi)
      apply(simp add: ipcidr_to_interval_def)
      apply(simp add: fun_eq_iff)
      apply(clarify)
      apply(induction ipassmt)
       apply(simp; fail)
      apply(simp)
      apply(simp split:option.split option.split_asm)
      apply(simp add: ipcidr_union_set_def ipset_from_cidr_ipcidr_to_interval)
      apply(simp add: case_prod_unfold)
      by blast
      (*apply(safe)
                       apply(simp_all)
      by (simp add: rev_image_eqI)*)
      

  
  text\<open>Debug algorithm with human-readable output\<close>
  definition debug_ipassmt_generic
    :: "('i::len wordinterval \<Rightarrow> string) \<Rightarrow>
          (iface \<times> ('i word \<times> nat) list) list \<Rightarrow> 'i common_primitive rule list \<Rightarrow> string list" where
    "debug_ipassmt_generic toStr ipassmt rs \<equiv> let ifaces = (map fst ipassmt) in [
      ''distinct: '' @ (if distinct ifaces then ''passed'' else ''FAIL!'')
      , ''ipassmt_sanity_nowildcards: '' @
          (if ipassmt_sanity_nowildcards (map_of ipassmt)
           then ''passed'' else ''fail: ''@list_toString iface_sel (filter iface_is_wildcard ifaces))
      , ''ipassmt_sanity_defined (interfaces defined in the ruleset are also in ipassmt): '' @ 
          (if ipassmt_sanity_defined rs (map_of ipassmt)
           then ''passed'' else ''fail: ''@list_toString iface_sel [i \<leftarrow> (collect_ifaces rs). i \<notin> set ifaces])
      , ''ipassmt_sanity_disjoint (no zone-spanning interfaces): '' @
          (if ipassmt_sanity_disjoint (map_of ipassmt)
           then ''passed'' else ''fail: ''@list_toString (\<lambda>(i1,i2). ''('' @ iface_sel i1 @ '','' @ iface_sel i2 @ '')'')
               [(i1,i2) \<leftarrow> List.product ifaces ifaces. i1 \<noteq> i2 \<and>
                \<not> wordinterval_empty (wordinterval_intersection
                                        (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i1))))
                                        (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i2)))))
          ])
      , ''ipassmt_sanity_disjoint excluding UNIV interfaces: '' @
          (let ipassmt = ipassmt_ignore_wildcard_list ipassmt;
               ifaces = (map fst ipassmt)
           in
          (if ipassmt_sanity_disjoint (map_of ipassmt)
           then ''passed'' else ''fail: ''@list_toString (\<lambda>(i1,i2). ''('' @ iface_sel i1 @ '','' @ iface_sel i2 @ '')'')
               [(i1,i2) \<leftarrow> List.product ifaces ifaces. i1 \<noteq> i2 \<and>
                \<not> wordinterval_empty (wordinterval_intersection
                                        (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i1))))
                                        (l2wi (map ipcidr_to_interval (the ((map_of ipassmt) i2)))))
          ]))
       , ''ipassmt_sanity_complete: '' @ 
          (if ipassmt_sanity_complete ipassmt
           then ''passed''
           else ''the following is not covered: '' @ 
            toStr (wordinterval_setminus wordinterval_UNIV (wordinterval_Union (map (l2wi \<circ> (map ipcidr_to_interval)) (map snd ipassmt)))))
      , ''ipassmt_sanity_complete excluding UNIV interfaces: '' @
          (let ipassmt = ipassmt_ignore_wildcard_list ipassmt
           in
          (if ipassmt_sanity_complete ipassmt
           then ''passed''
           else ''the following is not covered: '' @
            toStr (wordinterval_setminus wordinterval_UNIV (wordinterval_Union (map (l2wi \<circ> (map ipcidr_to_interval)) (map snd ipassmt))))))
      ]"

  definition "debug_ipassmt_ipv4 \<equiv> debug_ipassmt_generic ipv4addr_wordinterval_toString"
  definition "debug_ipassmt_ipv6 \<equiv> debug_ipassmt_generic ipv6addr_wordinterval_toString"


  lemma dom_ipassmt_ignore_wildcard:
    "i\<in>dom (ipassmt_ignore_wildcard ipassmt) \<longleftrightarrow> i \<in> dom ipassmt \<and> ipcidr_union_set (set (the (ipassmt i))) \<noteq> UNIV"
    apply(simp add: ipassmt_ignore_wildcard_def)
    apply(rule)
     apply(clarify)
     apply(simp split: option.split_asm split_if_asm)
     apply blast
    apply(clarify)
    apply(simp)
    done

  lemma ipassmt_ignore_wildcard_the:
    "ipassmt i = Some ips \<Longrightarrow> ipcidr_union_set (set ips) \<noteq> UNIV \<Longrightarrow> (the (ipassmt_ignore_wildcard ipassmt i)) = ips"
    "ipassmt_ignore_wildcard ipassmt i = Some ips \<Longrightarrow> the (ipassmt i) = ips"
    "ipassmt_ignore_wildcard ipassmt i = Some ips \<Longrightarrow> ipcidr_union_set (set ips) \<noteq> UNIV"
    by (simp_all add: ipassmt_ignore_wildcard_def split: option.split_asm split_if_asm)
    

  lemma ipassmt_sanity_disjoint_ignore_wildcards:
        "ipassmt_sanity_disjoint (ipassmt_ignore_wildcard ipassmt) \<longleftrightarrow>
         (\<forall>i1\<in>dom ipassmt.
          \<forall>i2\<in>dom ipassmt.
            ipcidr_union_set (set (the (ipassmt i1))) \<noteq> UNIV \<and>
            ipcidr_union_set (set (the (ipassmt i2))) \<noteq> UNIV \<and>
            i1 \<noteq> i2 
            \<longrightarrow> ipcidr_union_set (set (the (ipassmt i1))) \<inter> ipcidr_union_set (set (the (ipassmt i2))) = {})"
    apply(simp add: ipassmt_sanity_disjoint_def)
    apply(rule)
     apply(clarify)
     apply(simp)
     subgoal for i1 i2 ips1 ips2
     apply(erule_tac x=i1 in ballE)
      prefer 2
      using dom_ipassmt_ignore_wildcard  apply (metis domI option.sel)
     apply(erule_tac x=i2 in ballE)
      prefer 2
      using dom_ipassmt_ignore_wildcard apply (metis domI domIff option.sel)
     by(simp add: ipassmt_ignore_wildcard_the; fail)
    apply(clarify)
    apply(simp)
    subgoal for i1 i2 ips1 ips2
    apply(erule_tac x=i1 in ballE)
     prefer 2
     using dom_ipassmt_ignore_wildcard apply auto[1]
    apply(erule_tac x=i2 in ballE)
     prefer 2
     using dom_ipassmt_ignore_wildcard apply auto[1]
    by(simp add: ipassmt_ignore_wildcard_the)
   done

  text\<open>Confusing names: @{const ipassmt_sanity_nowildcards} refers to wildcard interfaces.
       @{const ipassmt_ignore_wildcard} refers to the UNIV ip range.
\<close>
  lemma ipassmt_sanity_nowildcards_ignore_wildcardD:
    "ipassmt_sanity_nowildcards ipassmt \<Longrightarrow> ipassmt_sanity_nowildcards (ipassmt_ignore_wildcard ipassmt)"
    by (simp add: dom_ipassmt_ignore_wildcard ipassmt_sanity_nowildcards_def)
    

 lemma ipassmt_disjoint_nonempty_inj:
     assumes ipassmt_disjoint: "ipassmt_sanity_disjoint ipassmt"
        and ifce: "ipassmt ifce = Some i_ips"
        and a: "ipcidr_union_set (set i_ips) \<noteq> {}"
        and k: "ipassmt k = Some i_ips"
     shows "k = ifce"
     proof(rule ccontr)
       assume "k \<noteq> ifce"
       with ifce k ipassmt_disjoint have "ipcidr_union_set (set (the (ipassmt k))) \<inter> ipcidr_union_set (set (the (ipassmt ifce))) = {}"
         unfolding ipassmt_sanity_disjoint_def by fastforce
       thus False using a ifce k by auto 
     qed

  lemma ipassmt_ignore_wildcard_None_Some:
    "ipassmt_ignore_wildcard ipassmt ifce = None \<Longrightarrow> ipassmt ifce = Some ips \<Longrightarrow> ipcidr_union_set (set ips) = UNIV"
    by (metis domI domIff dom_ipassmt_ignore_wildcard option.sel)
    

 (*can this lemma be somehow useful?
   maybe when rewriting, we can try to rewrite in the ignore_wildcard space and just constrain the the other area?*)
 lemma ipassmt_disjoint_ignore_wildcard_nonempty_inj:
     assumes ipassmt_disjoint: "ipassmt_sanity_disjoint (ipassmt_ignore_wildcard ipassmt)"
        and ifce: "ipassmt ifce = Some i_ips"
        and a: "ipcidr_union_set (set i_ips) \<noteq> {}"
        and k: "(ipassmt_ignore_wildcard ipassmt) k = Some i_ips"
     shows "k = ifce"
     proof(rule ccontr)
       assume "k \<noteq> ifce"
       show False
       proof(cases "(ipassmt_ignore_wildcard ipassmt) ifce")
       case (Some i_ips') (*proofs mainly by sledgehammer*)
         hence "i_ips' = i_ips" using ifce ipassmt_ignore_wildcard_the(2) by fastforce
         hence "(ipassmt_ignore_wildcard ipassmt) k = Some i_ips" using Some ifce ipassmt_ignore_wildcard_def k by auto 
         thus False using Some \<open>i_ips' = i_ips\<close> \<open>k \<noteq> ifce\<close> a ipassmt_disjoint ipassmt_disjoint_nonempty_inj by blast
       next
       case None
         with ipassmt_ignore_wildcard_None_Some have "ipcidr_union_set (set i_ips) = UNIV" using ifce by auto 
         thus False using ipassmt_ignore_wildcard_the(3) k by blast 
       qed
     qed

 lemma ipassmt_disjoint_inj_k: 
     assumes ipassmt_disjoint: "ipassmt_sanity_disjoint ipassmt"
        and ifce: "ipassmt ifce = Some ips"
        and k: "ipassmt k = Some ips'"
        and a: "p \<in> ipcidr_union_set (set ips)"
        and b: "p \<in> ipcidr_union_set (set ips')"
     shows "k = ifce"
     proof(rule ccontr)
       assume "k \<noteq> ifce"
       with ipassmt_disjoint have
          "ipcidr_union_set (set (the (ipassmt k))) \<inter> ipcidr_union_set (set (the (ipassmt ifce))) = {}"
         unfolding ipassmt_sanity_disjoint_def using ifce k by blast
       hence "ipcidr_union_set (set ips') \<inter> ipcidr_union_set (set ips) = {}" by(simp add: k ifce)
       thus False using a b by blast
     qed

 (*might also work when we ignore UNIVs in the ipassmt? (not tested)*)
 lemma ipassmt_disjoint_matcheq_iifce_srcip:
        assumes ipassmt_nowild: "ipassmt_sanity_nowildcards ipassmt"
            and ipassmt_disjoint: "ipassmt_sanity_disjoint ipassmt"
            and ifce: "ipassmt ifce = Some i_ips"
            and p_ifce: "ipassmt (Iface (p_iiface p)) = Some p_ips \<and> p_src p \<in> ipcidr_union_set (set p_ips)"
        shows   "match_iface ifce (p_iiface p) \<longleftrightarrow> p_src p \<in> ipcidr_union_set (set i_ips)"
    proof
     assume "match_iface ifce (p_iiface p)"
     thus "p_src p \<in> ipcidr_union_set (set i_ips)"
       apply(cases "ifce = Iface (p_iiface p)")
        using ifce p_ifce apply force
       by (metis domI iface.sel iface_is_wildcard_def ifce ipassmt_nowild ipassmt_sanity_nowildcards_def match_iface.elims(2) match_iface_case_nowildcard)
   next
     assume a: "p_src p \<in> ipcidr_union_set (set i_ips)"
     --\<open>basically, we need to reverse the map @{term ipassmt}\<close>

     from ipassmt_disjoint_nonempty_inj[OF ipassmt_disjoint ifce] a have ipassmt_inj: "\<forall>k. ipassmt k = Some i_ips \<longrightarrow> k = ifce" by blast

     from ipassmt_disjoint_inj_k[OF ipassmt_disjoint ifce _ a] have ipassmt_inj_k:
      "\<And>k ips'. ipassmt k = Some ips' \<Longrightarrow> p_src p \<in> ipcidr_union_set (set ips') \<Longrightarrow> k = ifce" by simp

     have ipassmt_inj_p: "\<forall>ips'. p_src p \<in> ipcidr_union_set (set ips') \<and> (\<exists>k. ipassmt k = Some ips') \<longrightarrow> ips' = i_ips"
       apply(clarify)
       apply(rename_tac ips' k)
       apply(subgoal_tac "k = ifce")
        using ifce apply simp
       using ipassmt_inj_k by simp

     from p_ifce have "(Iface (p_iiface p)) = ifce" using ipassmt_inj_p ipassmt_inj by blast 

     thus "match_iface ifce (p_iiface p)" using match_iface_refl by blast 
   qed



  definition ipassmt_generic_ipv4 :: "(iface \<times> (32 word \<times> nat) list) list" where
    "ipassmt_generic_ipv4 = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)])]"

  definition ipassmt_generic_ipv6 :: "(iface \<times> (128 word \<times> nat) list) list" where
    "ipassmt_generic_ipv6 = [(Iface ''lo'', [(1,128)])]" (*::1/128*)



subsection\<open>IP Assignment difference\<close>
  text\<open>Compare two ipassmts. Returns a list of tuples
    First entry of the tuple: things which are in the left ipassmt but not in the right.
    Second entry of the tupls: things which are in the right ipassmt but not in the left.\<close>
  definition ipassmt_diff
    :: "(iface \<times> ('i::len word \<times> nat) list) list \<Rightarrow> (iface \<times> ('i::len word \<times> nat) list) list
        \<Rightarrow> (iface \<times> ('i word \<times> nat) list \<times> ('i word \<times> nat) list) list"
  where
  "ipassmt_diff a b \<equiv> let
      t = \<lambda>s. (case s of None \<Rightarrow> Empty_WordInterval
                       | Some s \<Rightarrow> wordinterval_Union (map ipcidr_tuple_to_wordinterval s));
      k = \<lambda>x y d. cidr_split (wordinterval_setminus (t (map_of x d)) (t (map_of y d)))
    in
      [(d, (k a b d, k b a d)). d \<leftarrow> remdups (map fst (a @ b))]"
  
  
  text\<open>If an interface is defined in both ipassignments and there is no difference
       then the two ipassignements describe the same IP range for this interface.\<close>
  lemma ipassmt_diff_ifce_equal: "(ifce, [], []) \<in> set (ipassmt_diff ipassmt1 ipassmt2)  \<Longrightarrow>
         ifce \<in> dom (map_of ipassmt1) \<Longrightarrow> ifce \<in> dom (map_of ipassmt2) \<Longrightarrow>
           ipcidr_union_set (set (the ((map_of ipassmt1) ifce))) =
           ipcidr_union_set (set (the ((map_of ipassmt2) ifce)))"
    proof -
    have cidr_empty: "[] = cidr_split r \<Longrightarrow> wordinterval_to_set r = {}" for r :: "'a wordinterval"
      apply(subst cidr_split_prefix[symmetric])
      by(simp)
    show "(ifce, [], []) \<in> set (ipassmt_diff ipassmt1 ipassmt2)  \<Longrightarrow>
         ifce \<in> dom (map_of ipassmt1) \<Longrightarrow> ifce \<in> dom (map_of ipassmt2) \<Longrightarrow>
           ipcidr_union_set (set (the ((map_of ipassmt1) ifce))) =
           ipcidr_union_set (set (the ((map_of ipassmt2) ifce)))"
    apply(simp add: ipassmt_diff_def Let_def ipcidr_union_set_uncurry)
    apply(simp add: Set.image_iff)
    apply(elim conjE)
    apply(drule cidr_empty)+
    apply(simp)
    apply(simp add: domIff)
    apply(elim exE)
    apply(simp add: wordinterval_Union wordinterval_to_set_ipcidr_tuple_to_wordinterval_uncurry)
    done
  qed
  
  text\<open>Explanation for interface @{term "Iface ''a''"}: 
          Left ipassmt: The IP range 4/30 contains the addresses 4,5,6,7
          Diff: right ipassmt contains 6/32, so 4,5,7 is only in the left ipassmt.
          IP addresses 4,5 correspond to subnet 4/30.\<close>
  lemma "ipassmt_diff (ipassmt_generic_ipv4 @ [(Iface ''a'', [(4,30)])])
                       (ipassmt_generic_ipv4 @ [(Iface ''a'', [(6,32), (0,30)]), (Iface ''b'', [(42,32)])]) =
    [(Iface ''lo'', [], []),
     (Iface ''a'', [(4::32 word, 31::nat),
                    (7::32 word, 32::nat)],
                   [(0::32 word, 30::nat)]
     ),
     (Iface ''b'', [], [(42, 32)])]" by eval

end