theory Ipassmt
imports Common_Primitive_Lemmas
        Common_Primitive_toString
        "../Common/Lib_toString"
begin

  text{*A mapping from an interface to its assigned ip addresses in CIDR notation*}
  type_synonym ipassignment="iface \<rightharpoonup> (ipv4addr \<times> nat) list" (*technically, a set*)


subsection{*Sanity checking for an @{typ ipassignment}. *}

  text{*warning if interface map has wildcards*}
  definition ipassmt_sanity_nowildcards :: "ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_nowildcards ipassmt \<equiv> \<forall> iface \<in> dom ipassmt. \<not> iface_is_wildcard iface"

    text{*Executable of the @{typ ipassignment} is given as a list.*}
    lemma[code_unfold]: "ipassmt_sanity_nowildcards (map_of ipassmt) \<longleftrightarrow> (\<forall> iface \<in> fst` set ipassmt. \<not> iface_is_wildcard iface)"
      by(simp add: ipassmt_sanity_nowildcards_def Map.dom_map_of_conv_image_fst)
  
  lemma ipassmt_sanity_nowildcards_match_iface:
      "ipassmt_sanity_nowildcards ipassmt \<Longrightarrow>
       ipassmt (Iface ifce2) = None \<Longrightarrow>
       ipassmt ifce = Some a \<Longrightarrow>
       \<not> match_iface ifce ifce2"
  unfolding ipassmt_sanity_nowildcards_def using iface_is_wildcard_def match_iface_case_nowildcard by fastforce


  (* use this in all exported code*)
  definition map_of_ipassmt :: "(iface \<times> (32 word \<times> nat) list) list \<Rightarrow> iface \<rightharpoonup> (32 word \<times> nat) list" where
    "map_of_ipassmt ipassmt = (if distinct (map fst ipassmt) \<and> ipassmt_sanity_nowildcards (map_of ipassmt) then map_of ipassmt else undefined)"


  text{* some additional (optional) sanity checks *}
  
  text{*sanity check that there are no zone-spanning interfaces*}
  definition ipassmt_sanity_disjoint :: "ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_disjoint ipassmt \<equiv> \<forall> i1 \<in> dom ipassmt. \<forall> i2 \<in> dom ipassmt. i1 \<noteq> i2 \<longrightarrow>
          ipv4cidr_union_set (set (the (ipassmt i1))) \<inter> ipv4cidr_union_set (set (the (ipassmt i2))) = {}"
  
  lemma[code_unfold]: "ipassmt_sanity_disjoint (map_of ipassmt) \<longleftrightarrow> (let Is = fst` set ipassmt in 
      (\<forall> i1 \<in> Is. \<forall> i2 \<in> Is. i1 \<noteq> i2 \<longrightarrow> wordinterval_empty (wordinterval_intersection (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i1))))  (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i2)))))))"
    apply(simp add: ipassmt_sanity_disjoint_def Map.dom_map_of_conv_image_fst)
    apply(simp add: ipv4cidr_union_set_def)
    apply(simp add: l2br)
    apply(simp add: ipv4cidr_to_interval_def)
    apply(simp add: ipv4cidr_to_interval_ipv4range_set_from_bitmask)
    done
  
  
  text{*Checking that the ipassmt covers the complete ipv4 address space.*}
  definition ipassmt_sanity_complete :: "(iface \<times> (32 word \<times> nat) list) list \<Rightarrow> bool" where
    "ipassmt_sanity_complete ipassmt \<equiv> distinct (map fst ipassmt) \<and> (\<Union>(ipv4cidr_union_set ` set ` (ran (map_of ipassmt)))) = UNIV"

    lemma[code_unfold]: "ipassmt_sanity_complete ipassmt \<longleftrightarrow> distinct (map fst ipassmt) \<and> (let range = map snd ipassmt in 
        wordinterval_eq (wordinterval_Union (map (l2br \<circ> (map ipv4cidr_to_interval)) range)) wordinterval_UNIV
        )"
     apply(cases "distinct (map fst ipassmt)")
      apply(simp add: ipassmt_sanity_complete_def)
      apply(simp add: Map.ran_distinct)
      apply(simp add:  wordinterval_eq_set_eq wordinterval_Union)
      apply(simp add: l2br)
      apply(simp add: ipv4cidr_to_interval_def)
      apply(simp add: ipv4cidr_union_set_def ipv4cidr_to_interval_ipv4range_set_from_bitmask)
     apply(simp add: ipassmt_sanity_complete_def)
     done



    value[code] "ipassmt_sanity_nowildcards (map_of [(Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,240), 28)])])"

  fun collect_ifaces :: "common_primitive rule list \<Rightarrow> iface list" where
    "collect_ifaces [] = []" |
    "collect_ifaces ((Rule m a)#rs) = filter (\<lambda>iface. iface \<noteq> ifaceAny) (
                                      (map (\<lambda>x. case x of Pos i \<Rightarrow> i | Neg i \<Rightarrow> i) (fst (primitive_extractor (is_Iiface, iiface_sel) m))) @
                                      (map (\<lambda>x. case x of Pos i \<Rightarrow> i | Neg i \<Rightarrow> i) (fst (primitive_extractor (is_Oiface, oiface_sel) m))) @ collect_ifaces rs)"

  text{*sanity check that all interfaces mentioned in the ruleset are also listed in the ipassmt. May fail for wildcard interfaces in the ruleset.*}
  (*TODO: wildcards*)
  (*primitive_extractor requires normalized_nnf_primitives*)
  definition ipassmt_sanity_defined :: "common_primitive rule list \<Rightarrow> ipassignment \<Rightarrow> bool" where
    "ipassmt_sanity_defined rs ipassmt \<equiv> \<forall> iface \<in> set (collect_ifaces rs). iface \<in> dom ipassmt"

    lemma[code]: "ipassmt_sanity_defined rs ipassmt \<longleftrightarrow> (\<forall> iface \<in> set (collect_ifaces rs). ipassmt iface \<noteq> None)"
      by(simp add: ipassmt_sanity_defined_def Map.domIff)
  
    value[code] "ipassmt_sanity_defined [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (Iface ''eth1.1017'')))) action.Accept,
             Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (ifaceAny)))) action.Accept,
             Rule MatchAny action.Drop]
             (map_of [(Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,240), 28)])])"



  (*TODO: use and add code equation*)
  definition ipassmt_ignore_wildcard :: "ipassignment \<Rightarrow> ipassignment" where
    "ipassmt_ignore_wildcard ipassmt \<equiv> \<lambda>k. case ipassmt k of None \<Rightarrow> None 
                                                           | Some ips \<Rightarrow> if ipv4cidr_union_set (set ips) = UNIV then None else Some ips"

  lemma ipassmt_ignore_wildcard_le: "ipassmt_ignore_wildcard ipassmt \<subseteq>\<^sub>m ipassmt"
    apply(simp add: ipassmt_ignore_wildcard_def map_le_def)
    apply(clarify)
    apply(simp split: option.split_asm split_if_asm)
    done



  text{*Debug algorithm with human-readable output*}
  definition debug_ipassmt :: "(iface \<times> (32 word \<times> nat) list) list \<Rightarrow> common_primitive rule list \<Rightarrow> string list" where
    "debug_ipassmt ipassmt rs \<equiv> let ifaces = (map fst ipassmt) in [
      ''distinct: '' @ (if distinct ifaces then ''passed'' else ''FAIL!'')
      , ''ipassmt_sanity_nowildcards: '' @
          (if ipassmt_sanity_nowildcards (map_of ipassmt)
           then ''passed'' else list_toString iface_sel (filter iface_is_wildcard ifaces))
      , ''ipassmt_sanity_defined (interfaces defined in the ruleset are also in ipassmt): '' @ 
          (if ipassmt_sanity_defined rs (map_of ipassmt)
           then ''passed'' else list_toString iface_sel [i \<leftarrow> (collect_ifaces rs). i \<notin> set ifaces])
      , ''ipassmt_sanity_disjoint (no zone-spanning interfaces): '' @
          (if ipassmt_sanity_disjoint (map_of ipassmt)
           then ''passed'' else list_toString (\<lambda>(i1,i2). ''('' @ iface_sel i1 @ '','' @ iface_sel i2 @ '')'')
               [(i1,i2) \<leftarrow> List.product ifaces ifaces. i1 \<noteq> i2 \<and>
                \<not> wordinterval_empty (wordinterval_intersection
                                        (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i1))))
                                        (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i2)))))
          ])
      , ''ipassmt_sanity_disjoint excluding UNIV interfaces: '' @
          (let ipassmt = filter (\<lambda>(_,ips). ips \<noteq> [(0,0)]) ipassmt;
               ifaces = (map fst ipassmt)
           in
          (if ipassmt_sanity_disjoint (map_of ipassmt)
           then ''passed'' else list_toString (\<lambda>(i1,i2). ''('' @ iface_sel i1 @ '','' @ iface_sel i2 @ '')'')
               [(i1,i2) \<leftarrow> List.product ifaces ifaces. i1 \<noteq> i2 \<and>
                \<not> wordinterval_empty (wordinterval_intersection
                                        (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i1))))
                                        (l2br (map ipv4cidr_to_interval (the ((map_of ipassmt) i2)))))
          ]))
       , ''ipassmt_sanity_complete: '' @ 
          (if ipassmt_sanity_complete ipassmt
           then ''passed''
           else ''the following is not covered: '' @ 
            ipv4addr_wordinterval_toString (wordinterval_setminus wordinterval_UNIV (wordinterval_Union (map (l2br \<circ> (map ipv4cidr_to_interval)) (map snd ipassmt)))))
      , ''ipassmt_sanity_complete excluding UNIV interfaces: '' @
          (let ipassmt = filter (\<lambda>(_,ips). ips \<noteq> [(0,0)]) ipassmt
           in
          (if ipassmt_sanity_complete ipassmt
           then ''passed''
           else ''the following is not covered: '' @
            ipv4addr_wordinterval_toString (wordinterval_setminus wordinterval_UNIV (wordinterval_Union (map (l2br \<circ> (map ipv4cidr_to_interval)) (map snd ipassmt))))))
      ]"




  (*TODO: could also work when we ignore UNIVs in the ipassmt?*)
  lemma ipassmt_disjoint_matcheq_iifce_srcip:
        assumes ipassmt_nowild: "ipassmt_sanity_nowildcards ipassmt"
            and ipassmt_disjoint: "ipassmt_sanity_disjoint ipassmt"
            and ifce: "ipassmt ifce = Some i_ips"
            and p_ifce: "ipassmt (Iface (p_iiface p)) = Some p_ips \<and> p_src p \<in> ipv4cidr_union_set (set p_ips)"
        shows   "match_iface ifce (p_iiface p) \<longleftrightarrow> p_src p \<in> ipv4cidr_union_set (set i_ips)"
    proof
     assume "match_iface ifce (p_iiface p)"
     thus "p_src p \<in> ipv4cidr_union_set (set i_ips)"
       apply(cases "ifce = Iface (p_iiface p)")
        using ifce p_ifce apply force
       by (metis domI iface.sel iface_is_wildcard_def ifce ipassmt_nowild ipassmt_sanity_nowildcards_def match_iface.elims(2) match_iface_case_nowildcard)
   next
     assume a: "p_src p \<in> ipv4cidr_union_set (set i_ips)"
     --{*basically, we need to reverse the map @{term ipassmt}*}

     have ipassmt_inj: "\<forall>k. ipassmt k = Some i_ips \<longrightarrow> k = ifce"
     proof(rule ccontr, simp)
       assume "\<exists>k. ipassmt k = Some i_ips \<and> k \<noteq> ifce"
       with this obtain k where k: "ipassmt k = Some i_ips" and "k \<noteq> ifce" by blast
       with ifce ipassmt_disjoint have "ipv4cidr_union_set (set (the (ipassmt k))) \<inter> ipv4cidr_union_set (set (the (ipassmt ifce))) = {}"
         unfolding ipassmt_sanity_disjoint_def by fastforce
       thus False using a ifce k by auto 
     qed

     { fix ips' k
       assume 1:"p_src p \<in> ipv4cidr_union_set (set ips')" and 2: "ipassmt k = Some ips'"
       have "k = ifce"
       proof(rule ccontr)
         assume "k \<noteq> ifce"
         with ipassmt_disjoint have "ipv4cidr_union_set (set (the (ipassmt k))) \<inter> ipv4cidr_union_set (set (the (ipassmt ifce))) = {}"
           unfolding ipassmt_sanity_disjoint_def using 2 ifce by blast
         hence "ipv4cidr_union_set (set ips') \<inter> ipv4cidr_union_set (set i_ips) = {}" by(simp add: 2 ifce)
         thus False using 1 a by blast
       qed
     } note ipassmt_inj_k=this

     have ipassmt_inj_p: "\<forall>ips'. p_src p \<in> ipv4cidr_union_set (set ips') \<and> (\<exists>k. ipassmt k = Some ips') \<longrightarrow> ips' = i_ips"
       apply(clarify)
       apply(rename_tac ips' k)
       apply(subgoal_tac "k = ifce")
        using ifce apply simp
       using ipassmt_inj_k by simp

     from p_ifce have "(Iface (p_iiface p)) = ifce" using ipassmt_inj_p ipassmt_inj by blast 

     thus "match_iface ifce (p_iiface p)" using match_iface_refl by blast 
   qed
   


end