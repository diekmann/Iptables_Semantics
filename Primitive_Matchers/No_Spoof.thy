theory No_Spoof
imports Common_Primitive_Matcher
        Primitive_Normalization
        "../Common/Lib_toString"
begin

section{*No Spoofing*}
(* we do this in ternary (not simple firewall) to support things such as negated interfaces *)
  text{*assumes: @{const simple_ruleset}*}

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


  (*TODO: use this in all exported code*)
  definition map_of_ipassmt :: "(iface \<times> (32 word \<times> nat) list) list \<Rightarrow> iface \<rightharpoonup> (32 word \<times> nat) list" where
    "map_of_ipassmt ipassmt = (if distinct (map fst ipassmt) \<and> ipassmt_sanity_nowildcards (map_of ipassmt) then map_of ipassmt else undefined)"


  (*
  check wool: warning if zone-spanning (optional)
  *)

(***************TODO***************)
text{* some additional (optional) sanity checks *}
(*TODO: move to nospoof zone spanning*)
definition ipassmt_sanity_disjoint :: "ipassignment \<Rightarrow> bool" where
  "ipassmt_sanity_disjoint ipassmt \<equiv> \<forall> i1 \<in> dom ipassmt. \<forall> i2 \<in> dom ipassmt. 
        ipv4cidr_union_set (set (the (ipassmt i1))) \<inter> ipv4cidr_union_set (set (the (ipassmt i1))) = {}"

(*TODO: check those in the code examples*)
(*
lemma[code_unfold]: "ipassmt_sanity_disjoint (map_of ipassmt) \<longleftrightarrow> (let Is = fst` set ipassmt in 
    (\<forall> i1 \<in> Is. \<forall> i2 \<in> Is. ipv4cidr_union_set (set (the (map_of (ipassmt i1)))) \<inter> ipv4cidr_union_set (set (the (map_of (ipassmt i1)))) = {}))"
  apply(simp add: ipassmt_sanity_disjoint_def Map.dom_map_of_conv_image_fst)*)

(*TODO: move to nospoof and add those to the isabelle ipassm code generation and haskell tool!*)
definition ipassmt_sanity_complete :: "ipassignment \<Rightarrow> bool" where
  "ipassmt_sanity_complete ipassmt \<equiv> (ipv4cidr_union_set ` set ` (ran ipassmt)) = UNIV"
(***************TODO***************)



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

    text{*Executable code*}
    lemma[code]: "ipassmt_sanity_defined rs ipassmt \<longleftrightarrow> (\<forall> iface \<in> set (collect_ifaces rs). ipassmt iface \<noteq> None)"
      by(simp add: ipassmt_sanity_defined_def Map.domIff)
  
    value[code] "ipassmt_sanity_defined [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (Iface ''eth1.1017'')))) action.Accept,
             Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (ifaceAny)))) action.Accept,
             Rule MatchAny action.Drop]
             (map_of [(Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,240), 28)])])"


  text{*Debug algorithm*}
  definition debug_ipassmt :: "(iface \<times> (32 word \<times> nat) list) list \<Rightarrow> common_primitive rule list \<Rightarrow> string list" where
    "debug_ipassmt ipassmt rs \<equiv> let ifaces = (map fst ipassmt) in [
      ''distinct: '' @ (if distinct ifaces then ''passed'' else ''FAIL!'')
      , ''ipassmt_sanity_nowildcards: '' @
          (if ipassmt_sanity_nowildcards (map_of ipassmt)
           then ''passed'' else list_toString iface_sel (filter iface_is_wildcard ifaces))
      , ''ipassmt_sanity_defined: '' @ (if ipassmt_sanity_defined rs (map_of ipassmt)
        then ''passed'' else list_toString iface_sel [i \<leftarrow> (collect_ifaces rs). i \<notin> set ifaces])
      ]"

subsection{*Spoofing Protection*}
  text{*
  No spoofing means:
  Every packet that is (potentially) allowed by the firewall and comes from an interface @{text iface} 
  must have a Source IP Address in the assigned range @{text iface}.
  
  ``potentially allowed'' means we use the upper closure.
  The definition states: For all interfaces which are configured, every packet that comes from this
  interface and is allowed by the firewall must be in the IP range of that interface.
  *}
  definition no_spoofing :: "ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> bool" where
    "no_spoofing ipassmt rs \<equiv> \<forall> iface \<in> dom ipassmt. \<forall>p.
        ((common_matcher, in_doubt_allow),p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow) \<longrightarrow>
            p_src p \<in> (ipv4cidr_union_set (set (the (ipassmt iface))))"

  text{* The definition is sound (if that can be said about a definition):
          if @{const no_spoofing} certifies your ruleset, then your ruleset prohibits spoofing.
         The definition may not be complete:
          @{const no_spoofing} may return @{const False} even though your ruleset prevents spoofing
          (should only occur if some strange and unknown primitives occur)*}

  text{*Technical note: The definition can can be thought of as protection from OUTGOING spoofing.
        OUTGOING means: I define my interfaces and their IP addresses. For all interfaces,
                        only the assigned IP addresses may pass the firewall.
                        This definition is simple for e.g. local sub-networks.
                        Example: @{term "[Iface ''eth0'' \<mapsto> {(ipv4addr_of_dotdecimal (192,168,0,0), 24)}]"}
        If I want spoofing protection from the Internet, I need to specify the range of the Internet IP addresses.
        Example: @{term "[Iface ''evil_internet'' \<mapsto> {everything_that_does_not_belong_to_me}]"}.
          This is also a good opportunity to exclude the private IP space, link local, and probably multicast space.

        See examples below. Check Example 3 why it can be thought of as OUTGOING spoofing.*}

  (*TODO: make a definition of the `good' Internet IP address space.
        parameterized with a list of IP ranges that belong `me' (the institution that runs the firewall), which are hence
        excluded from the `good' Internet IP address sapce (because this is the local space, if such packets
        come from the Internet, they are spoofed!
    e.g. UNIV - 10/8 - 172.16/12 - 192.168/16 - institutes_range - \<dots>
    luckily, there is CIDR_split and we can easily have an executable representation of this set ...)*)



context
begin
  (*TODO move*)

  fun has_primitive :: "'a match_expr \<Rightarrow> bool" where
    "has_primitive MatchAny = False" |
    "has_primitive (Match a) = True" |
    "has_primitive (MatchNot m) = has_primitive m" |
    "has_primitive (MatchAnd m1 m2) = (has_primitive m1 \<or> has_primitive m2)"


  text{*Is a match expression equal to the @{const MatchAny} expression?
        Only applicable if no primitives are in the expression. *}
  fun matcheq_matachAny :: "'a match_expr \<Rightarrow> bool" where
    "matcheq_matachAny MatchAny \<longleftrightarrow> True" |
    "matcheq_matachAny (MatchNot m) \<longleftrightarrow> \<not> (matcheq_matachAny m)" |
    "matcheq_matachAny (MatchAnd m1 m2) \<longleftrightarrow> matcheq_matachAny m1 \<and> matcheq_matachAny m2" |
    "matcheq_matachAny (Match _) = undefined"

  private lemma no_primitives_no_unknown: "\<not> has_primitive m  \<Longrightarrow> (ternary_ternary_eval (map_match_tac \<beta> p m)) \<noteq> TernaryUnknown"
  proof(induction m)
  case Match thus ?case by auto
  next
  case MatchAny thus ?case by simp
  next
  case MatchAnd thus ?case by(auto elim: eval_ternary_And.elims)
  next
  case MatchNot thus ?case by(auto dest: eval_ternary_Not_UnknownD)
  qed


  private lemma no_primitives_matchNot: assumes "\<not> has_primitive m" shows "matches \<gamma> (MatchNot m) a p \<longleftrightarrow> \<not> matches \<gamma> m a p"
  proof -
    obtain \<beta> \<alpha> where "(\<beta>, \<alpha>) = \<gamma>" by (cases \<gamma>, simp)
    from assms have "matches (\<beta>, \<alpha>) (MatchNot m) a p \<longleftrightarrow> \<not> matches (\<beta>, \<alpha>) m a p"
      apply(induction m)
         apply(simp_all add: matches_case_ternaryvalue_tuple split: ternaryvalue.split)
      apply(rename_tac m1 m2)
      using no_primitives_no_unknown by (metis (no_types, hide_lams) eval_ternary_simps_simple(1) eval_ternary_simps_simple(3) ternaryvalue.exhaust) 
    with `(\<beta>, \<alpha>) = \<gamma>` assms show ?thesis by simp
  qed
  

  lemma matcheq_matachAny: "\<not> has_primitive m \<Longrightarrow> matcheq_matachAny m \<longleftrightarrow> matches \<gamma> m a p"
  proof(induction m)
  case Match hence False by auto
    thus ?case ..
  next
  case (MatchNot m)
    from MatchNot.prems have "\<not> has_primitive m" by simp
    with no_primitives_matchNot have "matches \<gamma> (MatchNot m) a p = (\<not> matches \<gamma> m a p)" by metis
    with MatchNot show ?case by(simp)
  next
  case (MatchAnd m1 m2)
    thus ?case by(simp add: Matching_Ternary.bunch_of_lemmata_about_matches)
  next
  case MatchAny show ?case by(simp add: Matching_Ternary.bunch_of_lemmata_about_matches)
  qed
end



(*
and now code to check spoofing protection
*)
context
begin
  text{*The set of any ip addresses which may match for a fixed @{text iface} (overapproximation)*}
  private definition get_exists_matching_src_ips :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_exists_matching_src_ips iface m \<equiv> let (i_matches, _) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, _) = (primitive_extractor (is_Src, src_sel) m) in
                if ip_matches = []
                then
                  UNIV
                else
                  \<Inter> ips \<in> set (ip_matches). (case ips of Pos ip \<Rightarrow> ipv4s_to_set ip | Neg ip \<Rightarrow> - ipv4s_to_set ip))
              else
                {}"

  (*when we replace the set by a 32 wordinterval, we should get executable code*)
  value[code] "primitive_extractor (is_Src, src_sel) (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 30))) (Match (IIface (Iface ''eth0''))))"

  private lemma match_simplematcher_Src_getPos: "(\<forall>m\<in>set (map Src (getPos ip_matches)). matches (common_matcher, \<alpha>) (Match m) a p)
         \<longleftrightarrow> (\<forall>ip\<in>set (getPos ip_matches). p_src p \<in> ipv4s_to_set ip)"
  by(simp add: Common_Primitive_Matcher.match_simplematcher_SrcDst)
  private lemma match_simplematcher_Src_getNeg: "(\<forall>m\<in>set (map Src (getNeg ip_matches)). matches (common_matcher, \<alpha>) (MatchNot (Match m)) a p)
         \<longleftrightarrow> (\<forall>ip\<in>set (getNeg ip_matches). p_src p \<in> - ipv4s_to_set ip)"
  by(simp add: match_simplematcher_SrcDst_not)
  private lemma match_simplematcher_Iface_getPos: "(\<forall>m\<in>set (map IIface (getPos i_matches)). matches (common_matcher, \<alpha>) (Match m) a p)
         \<longleftrightarrow> (\<forall>i\<in>set (getPos i_matches). match_iface i (p_iiface p))"
  by(simp add: match_simplematcher_Iface)
  private lemma match_simplematcher_Iface_getNeg: "(\<forall>m\<in>set (map IIface (getNeg i_matches)). matches (common_matcher, \<alpha>) (MatchNot (Match m)) a p)
         \<longleftrightarrow> (\<forall>i\<in>set (getNeg i_matches). \<not> match_iface i (p_iiface p))"
  by(simp add: match_simplematcher_Iface_not)

 private lemma get_exists_matching_src_ips_subset: 
    assumes "normalized_nnf_match m"
    shows "{ip. (\<exists>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))} \<subseteq>
           get_exists_matching_src_ips iface m"
  proof -
    
    let ?\<gamma>="(common_matcher, in_doubt_allow)"

    { fix ip_matches p rest src_ip i_matches rest2
      assume a1: "primitive_extractor (is_Src, src_sel) m = (ip_matches, rest)"
      and a2: "matches ?\<gamma> m a (p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      let ?p="(p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"

      (*TODO: simplify using negation_type_forall_split*)

      from primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(3) a1] have 
        "\<And>p. matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a p \<and> 
              matches ?\<gamma> rest a p \<longleftrightarrow>
              matches ?\<gamma> m a p" by fast
      with a2 have "matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a ?p \<and> 
              matches ?\<gamma> rest a ?p" by simp
      hence "matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a ?p" by blast
      with Negation_Type_Matching.matches_alist_and have
        "(\<forall>m\<in>set (getPos (NegPos_map Src ip_matches)). matches ?\<gamma> (Match m) a ?p) \<and> 
         (\<forall>m\<in>set (getNeg (NegPos_map Src ip_matches)). matches ?\<gamma> (MatchNot (Match m)) a ?p)" by metis
      with getPos_NegPos_map_simp2 getNeg_NegPos_map_simp2 have 
        "(\<forall>m\<in>set (map Src (getPos ip_matches)). matches ?\<gamma> (Match m) a ?p) \<and> 
         (\<forall>m\<in>set (map Src (getNeg ip_matches)). matches ?\<gamma> (MatchNot (Match m)) a ?p)" by metis
      with match_simplematcher_Src_getPos match_simplematcher_Src_getNeg have inset:
        "(\<forall>ip\<in>set (getPos ip_matches). p_src ?p \<in> ipv4s_to_set ip) \<and> (\<forall>ip\<in>set (getNeg ip_matches). p_src ?p \<in> - ipv4s_to_set ip)" by presburger
  
      with inset have "\<forall>x \<in> set ip_matches. src_ip \<in> (case x of Pos x \<Rightarrow> ipv4s_to_set x | Neg ip \<Rightarrow> - ipv4s_to_set ip)"
        apply(simp add: split: negation_type.split)
        apply(safe)
        using NegPos_set apply fast+
      done
    } note 1=this

    { fix ip_matches p rest src_ip i_matches rest2
      assume a2: "matches ?\<gamma> m a (p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      and a4: "primitive_extractor (is_Iiface, iiface_sel) m = (i_matches, rest2)"
      let ?p="(p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
    
      from primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(5) a4] have 
        "\<And>p. matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a p \<and> 
              matches ?\<gamma> rest2 a p \<longleftrightarrow>
              matches ?\<gamma> m a p" by fast
      with a2 have "matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a ?p \<and> 
              matches ?\<gamma> rest2 a ?p" by simp
      hence "matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a ?p" by blast
      with matches_alist_and have
        "(\<forall>m\<in>set (getPos (NegPos_map IIface i_matches)). matches ?\<gamma> (Match m) a ?p) \<and> 
         (\<forall>m\<in>set (getNeg (NegPos_map IIface i_matches)). matches ?\<gamma> (MatchNot (Match m)) a ?p)" by metis
      with getPos_NegPos_map_simp2 getNeg_NegPos_map_simp2 have 
        "(\<forall>m\<in>set (map IIface (getPos i_matches)). matches ?\<gamma> (Match m) a ?p) \<and> 
         (\<forall>m\<in>set (map IIface (getNeg i_matches)). matches ?\<gamma> (MatchNot (Match m)) a ?p)" by metis
      with match_simplematcher_Iface_getPos match_simplematcher_Iface_getNeg have inset_iface:
        "(\<forall>i\<in>set (getPos i_matches). match_iface i (p_iiface ?p)) \<and> (\<forall>i\<in>set (getNeg i_matches). \<not> match_iface i (p_iiface ?p))" by presburger
      hence 2: "(\<forall>x\<in>set i_matches. case x of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not> match_iface i (iface_sel iface))"
        apply(simp add: split: negation_type.split)
        apply(safe)
        using NegPos_set apply fast+
      done
    } note 2=this

    from 1 2 show ?thesis
      unfolding get_exists_matching_src_ips_def
      by(clarsimp)
  qed





  text{*The set of ip addresses which definitely match for a fixed @{text iface} (underapproximation)*}
  private definition get_all_matching_src_ips :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_all_matching_src_ips iface m \<equiv> let (i_matches, rest1) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, rest2) = (primitive_extractor (is_Src, src_sel) rest1) in
                if \<not> has_disc is_Dst rest2 \<and> 
                   \<not> has_disc is_Oiface rest2 \<and>
                   \<not> has_disc is_Prot rest2 \<and>
                   \<not> has_disc is_Src_Ports rest2 \<and>
                   \<not> has_disc is_Dst_Ports rest2 \<and>
                   \<not> has_disc is_CT_State rest2 \<and>
                   \<not> has_disc is_Extra rest2 \<and> 
                   matcheq_matachAny rest2
                then
                  if ip_matches = []
                  then
                    UNIV
                  else
                    \<Inter> ips \<in> set (ip_matches). (case ips of Pos ip \<Rightarrow> ipv4s_to_set ip | Neg ip \<Rightarrow> - ipv4s_to_set ip)
                else
                  {})
              else
                {}"



 private lemma get_all_matching_src_ips: 
    assumes "normalized_nnf_match m"
    shows "get_all_matching_src_ips iface m \<subseteq> {ip. (\<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))}"
  proof 
    fix ip
    assume a: "ip \<in> get_all_matching_src_ips iface m" 
    obtain i_matches rest1 where select1: "primitive_extractor (is_Iiface, iiface_sel) m = (i_matches, rest1)" by fastforce
    show "ip \<in> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}"
    proof(cases "\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface))")
    case False
      have "get_all_matching_src_ips iface m = {}"
        unfolding get_all_matching_src_ips_def
        using select1 False by auto
      with a show ?thesis by simp
    next
    case True
      let ?\<gamma>="(common_matcher, in_doubt_allow)"
      let ?p="\<lambda>p. p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>"
      obtain ip_matches rest2 where select2: "primitive_extractor (is_Src, src_sel) rest1 = (ip_matches, rest2)" by fastforce

      let ?noDisc="\<not> has_disc is_Dst rest2 \<and>
                      \<not> has_disc is_Oiface rest2 \<and>
                      \<not> has_disc is_Prot rest2 \<and>
                      \<not> has_disc is_Src_Ports rest2 \<and> \<not> has_disc is_Dst_Ports rest2 \<and>
                      \<not> has_disc is_CT_State rest2 \<and>
                      \<not> has_disc is_Extra rest2"

      have get_all_matching_src_ips_caseTrue: "get_all_matching_src_ips iface m = (if ?noDisc \<and> matcheq_matachAny rest2
                   then if ip_matches = [] then UNIV else INTER (set ip_matches) (case_negation_type ipv4s_to_set (\<lambda>ip. - ipv4s_to_set ip)) else {})"
      unfolding get_all_matching_src_ips_def
      by(simp add: True select1 select2)

      from True have "\<And>p. (\<forall>m\<in>set (getPos i_matches). matches (common_matcher, in_doubt_allow) (Match (IIface m)) a (?p p)) \<and>
         (\<forall>m\<in>set (getNeg i_matches). matches (common_matcher, in_doubt_allow) (MatchNot (Match (IIface m))) a (?p p))"
         by(simp add: negation_type_forall_split match_simplematcher_Iface match_simplematcher_Iface_not)
      hence matches_iface: "\<And>p. matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a (?p p)"
        by(simp add: matches_alist_and NegPos_map_simps)

      show ?thesis
      proof(cases "?noDisc \<and> matcheq_matachAny rest2")
      case False
        assume F: "\<not> (?noDisc \<and> matcheq_matachAny rest2)"
        with get_all_matching_src_ips_caseTrue have "get_all_matching_src_ips iface m = {}" by presburger
        with a have False by simp
        thus "ip \<in> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}" ..
      next
      case True
        assume F: "?noDisc \<and> matcheq_matachAny rest2"
        with get_all_matching_src_ips_caseTrue have "get_all_matching_src_ips iface m = 
            (if ip_matches = [] then UNIV else INTER (set ip_matches) (case_negation_type ipv4s_to_set (\<lambda>ip. - ipv4s_to_set ip)))" by presburger


        from primitive_extractor_correct[OF assms wf_disc_sel_common_primitive(5) select1] have
          select1_matches: "\<And>p. matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a p \<and> matches ?\<gamma> rest1 a p \<longleftrightarrow> matches ?\<gamma> m a p"
          and normalized1: "normalized_nnf_match rest1"
          and no_iiface_rest1: "\<not> has_disc is_Iiface rest1"
          apply -
            apply fast+
          done
        from select1_matches matches_iface have rest1_matches: "\<And>p. matches ?\<gamma> rest1 a (?p p) \<longleftrightarrow> matches ?\<gamma> m a (?p p)" by blast

        from primitive_extractor_correct[OF normalized1 wf_disc_sel_common_primitive(3) select2] have
          select2_matches: "\<And>p. (matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a p \<and> matches ?\<gamma> rest2 a p) = matches ?\<gamma> rest1 a p"
          and no_Src_rest2: "\<not> has_disc is_Src rest2"
          and no_IIface_rest2: "\<not> has_disc is_Iiface rest2"
          apply -
            apply fast+
           using no_iiface_rest1 apply fast
          done

        from F have ?noDisc by simp
        with no_Src_rest2 no_IIface_rest2 have "\<not> has_primitive rest2"
          apply(induction rest2)
             apply(simp_all)
          apply(rename_tac x)
          apply(case_tac x, auto)
          done
        with F matcheq_matachAny have "\<And>p. matches ?\<gamma> rest2 a p" by metis
        with select2_matches rest1_matches have ip_src_matches: 
            "\<And>p. matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a (?p p) \<longleftrightarrow> matches ?\<gamma> m a (?p p)" by simp

        have case_nil: "\<And>p. ip_matches = [] \<Longrightarrow> matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a p" by(simp add: bunch_of_lemmata_about_matches)

        have case_list: "\<And>p. \<forall>x\<in>set ip_matches. (case x of Pos i \<Rightarrow> ip \<in> ipv4s_to_set i | Neg i \<Rightarrow> ip \<in>  - ipv4s_to_set i) \<Longrightarrow>
            matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)"
          apply(simp add: matches_alist_and NegPos_map_simps)
          apply(simp add: negation_type_forall_split match_simplematcher_SrcDst_not match_simplematcher_SrcDst)
          done

        from a show "ip \<in> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}"
          unfolding get_all_matching_src_ips_caseTrue
          proof(clarsimp split: split_if_asm)
            fix p
            assume "ip_matches = []"
            with case_nil have "matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a (?p p)" by simp
            with ip_src_matches show "matches ?\<gamma> m a (?p p)" by simp
          next
            fix p
            assume "\<forall>x\<in>set ip_matches. ip \<in> (case x of Pos x \<Rightarrow> ipv4s_to_set x | Neg ip \<Rightarrow> - ipv4s_to_set ip)"
            hence "\<forall>x\<in>set ip_matches. case x of Pos i \<Rightarrow> ip \<in> ipv4s_to_set i | Neg i \<Rightarrow> ip \<in> - ipv4s_to_set i"
             by(simp_all split: negation_type.split negation_type.split_asm)
            with case_list have "matches ?\<gamma> (alist_and (NegPos_map Src ip_matches)) a (?p p)" .
            with ip_src_matches show "matches ?\<gamma> m a (?p p)" by simp
          qed
       qed
     qed
  qed



  private definition get_exists_matching_src_ips_executable :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> 32 wordinterval" where
    "get_exists_matching_src_ips_executable iface m \<equiv> let (i_matches, _) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, _) = (primitive_extractor (is_Src, src_sel) m) in
                if ip_matches = []
                then
                  ipv4range_UNIV
                else
                  l2br_negation_type_intersect (NegPos_map ipt_ipv4range_to_interval ip_matches))
              else
                Empty_WordInterval"
  (*WOW, such horrible proof!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!*)
  lemma get_exists_matching_src_ips_executable: 
    "wordinterval_to_set (get_exists_matching_src_ips_executable iface m) = get_exists_matching_src_ips iface m"
    apply(simp add: get_exists_matching_src_ips_executable_def get_exists_matching_src_ips_def)
    apply(case_tac "primitive_extractor (is_Iiface, iiface_sel) m")
    apply(case_tac "primitive_extractor (is_Src, src_sel) m")
    apply(simp)
    apply(simp add: l2br_negation_type_intersect)
    apply(simp add: ipv4range_UNIV_def NegPos_map_simps)
    apply(simp add: ipt_ipv4range_to_interval)
    apply(safe)
         apply(simp_all add: ipt_ipv4range_to_interval)
      apply(rename_tac i_matches rest1 a b x xa)
      apply(case_tac xa)
       apply(simp_all add: NegPos_set)
       using ipt_ipv4range_to_interval apply fast+
     apply(rename_tac i_matches rest1 a b x aa ab ba)
     apply(erule_tac x="Pos aa" in ballE)
      apply(simp_all add: NegPos_set)
    using NegPos_set(2) by fastforce

  value[code] "(get_exists_matching_src_ips_executable (Iface ''eth0'')
      (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))))"

  private definition get_all_matching_src_ips_executable :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> 32 wordinterval" where
    "get_all_matching_src_ips_executable iface m \<equiv> let (i_matches, rest1) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, rest2) = (primitive_extractor (is_Src, src_sel) rest1) in
                if \<not> has_disc is_Dst rest2 \<and> 
                   \<not> has_disc is_Oiface rest2 \<and>
                   \<not> has_disc is_Prot rest2 \<and>
                   \<not> has_disc is_Src_Ports rest2 \<and>
                   \<not> has_disc is_Dst_Ports rest2 \<and>
                   \<not> has_disc is_CT_State rest2 \<and>
                   \<not> has_disc is_Extra rest2 \<and> 
                   matcheq_matachAny rest2
                then
                  if ip_matches = []
                  then
                    ipv4range_UNIV
                  else
                    l2br_negation_type_intersect (NegPos_map ipt_ipv4range_to_interval ip_matches)
                else
                  Empty_WordInterval)
              else
                Empty_WordInterval"
  (*WOW, such horrible proof!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!*)
  lemma get_all_matching_src_ips_executable: 
    "wordinterval_to_set (get_all_matching_src_ips_executable iface m) = get_all_matching_src_ips iface m"
    apply(simp add: get_all_matching_src_ips_executable_def get_all_matching_src_ips_def)
    apply(case_tac "primitive_extractor (is_Iiface, iiface_sel) m")
    apply(simp, rename_tac i_matches rest1)
    apply(case_tac "primitive_extractor (is_Src, src_sel) rest1")
    apply(simp)
    apply(simp add: l2br_negation_type_intersect)
    apply(simp add: ipv4range_UNIV_def NegPos_map_simps)
    apply(simp add: ipt_ipv4range_to_interval)
    apply(safe)
         apply(simp_all add: ipt_ipv4range_to_interval)
      apply(rename_tac i_matches rest1 a b x xa)
      apply(case_tac xa)
       apply(simp_all add: NegPos_set)
       using ipt_ipv4range_to_interval apply fast+
     apply(rename_tac i_matches rest1 a b x aa ab ba)
     apply(erule_tac x="Pos aa" in ballE)
      apply(simp_all add: NegPos_set)
    apply(erule_tac x="Neg aa" in ballE)
     apply(simp_all add: NegPos_set)
    done
  value[code] "(get_all_matching_src_ips_executable (Iface ''eth0'')
      (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))))"



  private lemma "{ip. \<forall>p \<in> {p. \<not> match_iface iface (p_iiface p)}. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr> p_src:= ip\<rparr>)} =
                 {ip. \<forall>p. \<not> match_iface iface (p_iiface p) \<longrightarrow> matches (common_matcher, in_doubt_allow) m Drop (p\<lparr> p_src:= ip\<rparr>)}" by blast
  private lemma p_iiface_update: "p\<lparr>p_iiface := p_iiface p, p_src := x\<rparr> = p\<lparr>p_src := x\<rparr>" by(simp)
  private lemma "(\<Inter> if' \<in> {if'. \<not> match_iface iface if'}. {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr> p_iiface := if', p_src:= ip\<rparr>)}) = 
                 {ip. \<forall>p \<in> {p. \<not> match_iface iface (p_iiface p)}. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr> p_src:= ip\<rparr>)}"
    apply(simp)
    apply(safe)
     apply(simp_all)
    apply(erule_tac x="(p_iiface p)" in allE)
    apply(simp)
    using p_iiface_update by metis
     

  text{* The following algorithm sound but not complete.*}
  (*alowed: set ip ips potentially allowed for iface
    denied: set of ips definitely dropped for iface*)
  private fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr set \<Rightarrow> (*ipv4addr set \<Rightarrow>*) bool" where
    "no_spoofing_algorithm iface ipassmt [] allowed denied1  \<longleftrightarrow> 
      (allowed - denied1) \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Accept)#rs) allowed denied1 = no_spoofing_algorithm iface ipassmt rs 
        (allowed \<union> get_exists_matching_src_ips iface m) denied1" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Drop)#rs) allowed denied1 = no_spoofing_algorithm iface ipassmt rs
         allowed (denied1 \<union> (get_all_matching_src_ips iface m - allowed))"  |
    "no_spoofing_algorithm _ _ _ _ _  = undefined"



  private fun no_spoofing_algorithm_executable :: "iface \<Rightarrow> (iface \<rightharpoonup> (ipv4addr \<times> nat) list) \<Rightarrow> common_primitive rule list \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> bool" where
    "no_spoofing_algorithm_executable iface ipassmt [] allowed denied1  \<longleftrightarrow> 
      wordinterval_subset (wordinterval_setminus allowed denied1) (l2br (map ipv4cidr_to_interval (the (ipassmt iface))))" |
    "no_spoofing_algorithm_executable iface ipassmt ((Rule m Accept)#rs) allowed denied1 = no_spoofing_algorithm_executable iface ipassmt rs 
        (wordinterval_union allowed (get_exists_matching_src_ips_executable iface m)) denied1" |
    "no_spoofing_algorithm_executable iface ipassmt ((Rule m Drop)#rs) allowed denied1 = no_spoofing_algorithm_executable iface ipassmt rs
         allowed (wordinterval_union denied1 (wordinterval_setminus (get_all_matching_src_ips_executable iface m) allowed))"  |
    "no_spoofing_algorithm_executable _ _ _ _ _  = undefined"

  lemma no_spoofing_algorithm_executable: "no_spoofing_algorithm_executable iface ipassmt rs allowed denied \<longleftrightarrow> 
         no_spoofing_algorithm iface ipassmt rs (wordinterval_to_set allowed) (wordinterval_to_set denied)"
  proof(induction iface ipassmt rs allowed denied rule: no_spoofing_algorithm_executable.induct)
  case (1 iface ipassmt allowed denied1)
    have "(\<Union>a\<in>set (the (ipassmt iface)). case ipv4cidr_to_interval a of (x, xa) \<Rightarrow> {x..xa}) = 
          (\<Union>x\<in>set (the (ipassmt iface)). case x of (base, len) \<Rightarrow> ipv4range_set_from_bitmask base len)" 
    using ipv4cidr_to_interval_ipv4range_set_from_bitmask ipv4cidr_to_interval_def by simp
    with 1 show ?case by(simp add: ipv4cidr_union_set_def l2br)
  next
  case 2 thus ?case by(simp add: get_exists_matching_src_ips_executable get_all_matching_src_ips_executable)
  next
  case 3 thus ?case by(simp add: get_exists_matching_src_ips_executable get_all_matching_src_ips_executable)
  qed(simp_all)

  lemma "no_spoofing_algorithm_executable
      (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (Iface ''eth0'')))) action.Accept,
           Rule MatchAny action.Drop]
          Empty_WordInterval Empty_WordInterval" by eval
    

  (*implementation could store ipv4addr set as 32 wordinterval*)


  text{*Examples*}
  text{*Example 1*}
  text{*
    Ruleset: Accept all non-spoofed packets, drop rest.
  *}
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (Iface ''eth0'')))) action.Accept,
           Rule MatchAny action.Drop]
          {} {}
          "
     proof -
      have localrng: "ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192,168,0,0)) 24 = {0xC0A80000..0xC0A800FF}"
      by(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
        
      have ipset: "{ip. \<exists>p. matches (common_matcher, in_doubt_allow) (MatchAnd (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24))) (Match (IIface (Iface ''eth0'')))) Accept
              (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192,168,0,0)) 24"
         by(auto simp add: localrng eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple match_iface.simps
                      split: ternaryvalue.split ternaryvalue.split_asm)
       show ?thesis
        apply(simp add: ipset ipv4cidr_union_set_def get_exists_matching_src_ips_def)
        by blast
      qed

  text{*Example 2*}
  text{*
    Ruleset: Drop packets from a spoofed IP range, allow rest.
  *}
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (IIface (Iface ''wlan+''))) (Match (Extra ''no idea what this is''))) action.Accept, (*not interesting for spoofing*)
           Rule (MatchNot (Match (IIface (Iface ''eth0+'')))) action.Accept, (*not interesting for spoofing*)
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))) action.Drop, (*spoof-protect here*)
           Rule MatchAny action.Accept]
          {} {}
          "
        apply(simp add: get_all_matching_src_ips_def get_exists_matching_src_ips_def match_iface.simps)
        apply(simp add: ipv4cidr_union_set_def)
        done

   private lemma iprange_example: "ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24 = {0xC0A80000..0xC0A800FF}"
     by(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
   lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchNot (Match (IIface (Iface ''wlan+'')))) action.Accept, (*accidently allow everything for eth0*)
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))) action.Drop,
           Rule MatchAny action.Accept]
          {} {} \<longleftrightarrow> False
          "
        apply(simp add: get_exists_matching_src_ips_def match_iface.simps)
        apply(simp add: range_0_max_UNIV ipv4cidr_union_set_def iprange_example)
        done

  text{*Example 3*}
  text{*
    Ruleset: Drop packets coming from the wrong interface, allow the rest.
    Warning: this does not prevent spoofing for eth0!
    Explanation: someone on eth0 can send a packet e.g. with source IP 8.8.8.8
    The ruleset only prevents spoofing of 192.168.0.0/24 for other interfaces
  *}
   lemma "no_spoofing [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (MatchNot (Match (IIface (Iface ''eth0''))))) action.Drop,
           Rule MatchAny action.Accept] \<longleftrightarrow> False" (is "no_spoofing ?ipassmt ?rs \<longleftrightarrow> False")
   proof -
     have "simple_ruleset ?rs" by(simp add: simple_ruleset_def)
     hence 1: "\<forall>p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>?rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longleftrightarrow>
                approximating_bigstep_fun (common_matcher, in_doubt_allow) p ?rs Undecided = Decision FinalAllow"
       apply -
       apply(drule simple_imp_good_ruleset)
       apply(simp add: approximating_semantics_iff_fun_good_ruleset)
       done
     have 2: "\<forall>p. \<not> matches (common_matcher, in_doubt_allow) (MatchNot (Match (IIface (Iface ''eth0'')))) Drop (p\<lparr>p_iiface := ''eth0''\<rparr>)"
     by(simp add: match_simplematcher_Iface_not match_iface.simps)
     
     text{*The @{const no_spoofing} definition requires that all packets from @{term "''eth0''"} are from 192.168.0.0/24*}
     have "no_spoofing ?ipassmt ?rs \<longleftrightarrow> 
      (\<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := ''eth0''\<rparr>) ?rs  Undecided = Decision FinalAllow \<longrightarrow>
            p_src p \<in> ipv4cidr_union_set {(ipv4addr_of_dotdecimal (192, 168, 0, 0), 24)})"
      unfolding no_spoofing_def
       apply(subst 1)
       by(simp)
     text{*In this example however, all packets for all IPs from @{term "''eth0''"} are allowed.*}
     have "\<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := ''eth0''\<rparr>) ?rs  Undecided = Decision FinalAllow"
       by(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary 2)

     have 3: "no_spoofing ?ipassmt ?rs \<longleftrightarrow> (\<forall>p::simple_packet. p_src p \<in> ipv4cidr_union_set {(ipv4addr_of_dotdecimal (192, 168, 0, 0), 24)})"
       unfolding no_spoofing_def
       apply(subst 1)
       apply(simp)
       apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
       apply(simp add: 2)
       done
     
     show ?thesis
     unfolding 3
     apply(simp add: ipv4cidr_union_set_def)
     apply(simp add: iprange_example)
     apply(rule_tac x="p\<lparr>p_src := 0\<rparr>" in exI) (*any p*)
     apply(simp)
     done
   qed
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (MatchNot (Match (IIface (Iface ''eth0''))))) action.Drop,
           Rule MatchAny action.Accept]
          {} {} \<longleftrightarrow> False"
    apply(subst no_spoofing_algorithm.simps)
    apply(simp add: get_exists_matching_src_ips_def get_all_matching_src_ips_def match_iface.simps del: no_spoofing_algorithm.simps)
    apply(subst no_spoofing_algorithm.simps)
    apply(simp add: get_exists_matching_src_ips_def get_all_matching_src_ips_def match_iface.simps del: no_spoofing_algorithm.simps)
    apply(subst no_spoofing_algorithm.simps)
    apply(simp add: get_exists_matching_src_ips_def get_all_matching_src_ips_def match_iface.simps del: no_spoofing_algorithm.simps)
    apply(simp add: ipv4cidr_union_set_def)
    apply(simp add: iprange_example)
    apply(simp add: range_0_max_UNIV)
    done

  text{*Example 4: spoofing protection but the algorithm fails (it is only sound, not complete).*}
  lemma "no_spoofing [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (MatchAnd (Match (IIface (Iface ''eth0''))) (Match (Prot (Proto TCP))))) action.Drop,
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (MatchAnd (Match (IIface (Iface ''eth0''))) (MatchNot (Match (Prot (Proto TCP)))))) action.Drop,
           Rule MatchAny action.Accept]" (is "no_spoofing ?ipassmt ?rs")
   proof -
     have "simple_ruleset ?rs" by(simp add: simple_ruleset_def)
     hence 1: "\<forall>p. (common_matcher, in_doubt_allow),p\<turnstile> \<langle>?rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<longleftrightarrow>
                approximating_bigstep_fun (common_matcher, in_doubt_allow) p ?rs Undecided = Decision FinalAllow"
       apply -
       apply(drule simple_imp_good_ruleset)
       apply(simp add: approximating_semantics_iff_fun_good_ruleset)
       done
     show ?thesis
       unfolding no_spoofing_def
       apply(subst 1)
       apply(simp)
       apply(simp add: bunch_of_lemmata_about_matches ternary_to_bool_bool_to_ternary)
       apply(simp add: match_iface.simps)
       apply(simp add: match_simplematcher_SrcDst_not)
       apply(auto simp add: eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple match_iface.simps
                      split: ternaryvalue.split ternaryvalue.split_asm)
       apply(simp add: ipv4cidr_union_set_def)
       done
   qed
  lemma "\<not> no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (MatchAnd (Match (IIface (Iface ''eth0''))) (Match (Prot (Proto TCP))))) action.Drop,
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (MatchAnd (Match (IIface (Iface ''eth0''))) (MatchNot (Match (Prot (Proto TCP)))))) action.Drop,
           Rule MatchAny action.Accept] {} {}"
    by(simp add: get_exists_matching_src_ips_def get_all_matching_src_ips_def match_iface.simps ipv4cidr_union_set_def iprange_example range_0_max_UNIV)

  private definition "nospoof iface ipassmt rs = (\<forall>p.
          (approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow) \<longrightarrow>
              p_src p \<in> (ipv4cidr_union_set (set (the (ipassmt iface)))))"
  private definition "setbydecision iface rs dec = {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"

  private lemma packet_update_iface_simp: "p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr> = p\<lparr>p_src := x, p_iiface := iface_sel iface\<rparr>" by simp
 
  private lemma nospoof_setbydecision: "nospoof iface ipassmt rs \<longleftrightarrow> setbydecision iface rs FinalAllow \<subseteq> (ipv4cidr_union_set (set (the (ipassmt iface))))"
  proof
    assume a: "nospoof iface ipassmt rs"
    from a show "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))"
      apply(simp add: nospoof_def setbydecision_def)
      apply(safe)
      apply(rename_tac x p)
      apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr>" in allE)
      apply(simp)
      apply(simp add: packet_update_iface_simp)
      done
  next
    assume a1: "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))"
    show "nospoof iface ipassmt rs"
      unfolding nospoof_def
      proof(safe)
        fix p
        assume a2: "approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow"
        --{*In @{text setbydecision_fix_p}the @{text \<exists>} quantifier is gone and we consider this set for @{term p}.*}
        let ?setbydecision_fix_p="{ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision FinalAllow}"
        from a1 a2 have 1: "?setbydecision_fix_p \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))" by(simp add: nospoof_def setbydecision_def) blast
        from a2 have 2: "p_src p \<in> ?setbydecision_fix_p" by simp
        from 1 2 show "p_src p \<in> ipv4cidr_union_set (set (the (ipassmt iface)))" by blast
      qed
  qed


  private definition "setbydecision_all iface rs dec = {ip. \<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"

  private lemma setbydecision_setbydecision_all_Allow: "(setbydecision iface rs FinalAllow - setbydecision_all iface rs FinalDeny) = 
      setbydecision iface rs FinalAllow"
    apply(safe)
    apply(simp add: setbydecision_def setbydecision_all_def)
    done
  private lemma setbydecision_setbydecision_all_Deny: "(setbydecision iface rs FinalDeny - setbydecision_all iface rs FinalAllow) = 
      setbydecision iface rs FinalDeny"
    apply(safe)
    apply(simp add: setbydecision_def setbydecision_all_def)
    done

  (*follows directly from existing lemmas, move into proof below, do not move to generic thy!*)
  private lemma decision_append: "simple_ruleset rs1 \<Longrightarrow> approximating_bigstep_fun \<gamma> p rs1 Undecided = Decision X \<Longrightarrow>
           approximating_bigstep_fun \<gamma> p (rs1 @ rs2) Undecided = Decision X"
    apply(drule simple_imp_good_ruleset)
    apply(drule good_imp_wf_ruleset[of _ \<gamma> p])
    apply(simp add: approximating_bigstep_fun_seq_wf Decision_approximating_bigstep_fun)
    done

  private lemma setbydecision_append: "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision iface (rs1 @ rs2) FinalAllow =
          setbydecision iface rs1 FinalAllow \<union> {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs2 Undecided = Decision FinalAllow \<and>
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}"
      apply(simp add: setbydecision_def)
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_cong)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      by blast

  private lemma not_FinalAllow: "foo \<noteq> Decision FinalAllow \<longleftrightarrow> foo = Decision FinalDeny \<or> foo = Undecided"
    apply(cases foo)
     apply simp_all
    apply(rename_tac x2)
    apply(case_tac x2)
     apply(simp_all)
    done

  private lemma foo_not_FinalDeny: "foo \<noteq> Decision FinalDeny \<longleftrightarrow> foo = Undecided \<or> foo = Decision FinalAllow"
    apply(cases foo)
     apply simp_all
    apply(rename_tac x2)
    apply(case_tac x2)
     apply(simp_all)
    done

  private lemma setbydecision_all_appendAccept: "simple_ruleset (rs @ [Rule r Accept]) \<Longrightarrow> 
    setbydecision_all iface rs FinalDeny = setbydecision_all iface (rs @ [Rule r Accept]) FinalDeny"
      apply(simp add: setbydecision_all_def)
      apply(rule Set.Collect_cong)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(simp add: not_FinalAllow)
      done

  lemma "(\<forall>x. P x \<and> Q x) \<longleftrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)" by blast
  lemma "(\<forall>x. P x) \<or> (\<forall>x. Q x) \<Longrightarrow> (\<forall>x. P x \<or> Q x)" by blast

  private lemma setbydecision_all_append_subset: "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision_all iface rs1 FinalDeny \<union> {ip. \<forall>p.
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs2 Undecided = Decision FinalDeny \<and>
            approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}
            \<subseteq>
            setbydecision_all iface (rs1 @ rs2) FinalDeny"
      unfolding setbydecision_all_def
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(simp add: not_FinalAllow)
      done

  private lemma Collect_minus_eq: "{x. P x} - {x. Q x} = {x. P x \<and> \<not> Q x}" by blast

  private lemma "setbydecision_all iface rs1 FinalDeny \<union>
                 {ip. \<forall>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs1 Undecided = Undecided}
                 \<subseteq>
                 - setbydecision iface rs1 FinalAllow"
      unfolding setbydecision_all_def
      unfolding setbydecision_def
      apply(subst Set.Collect_neg_eq[symmetric])
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      by(simp)


  private lemma setbydecision_all_append_subset2:
      "simple_ruleset (rs1 @ rs2) \<Longrightarrow> setbydecision_all iface rs1 FinalDeny \<union> (setbydecision_all iface rs2 FinalDeny - setbydecision iface rs1 FinalAllow)
            \<subseteq> setbydecision_all iface (rs1 @ rs2) FinalDeny"
      unfolding setbydecision_all_def
      unfolding setbydecision_def
      apply(subst Collect_minus_eq)
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       apply(simp add: simple_imp_good_ruleset good_imp_wf_ruleset)
      apply(intro impI allI)
      apply(simp add: not_FinalAllow)
      apply(case_tac "approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr>) rs1 Undecided")
       apply(elim disjE)
        apply(simp_all)[2]
      apply(rename_tac x2)
      apply(case_tac x2)
       prefer 2
       apply simp
      apply(elim disjE)
       apply(simp)
      by blast



  private lemma notin_setbydecisionD: "ip \<notin> setbydecision iface rs FinalAllow \<Longrightarrow> (\<forall>p.
      approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision FinalDeny \<or>
      approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided)"
    by(simp add: setbydecision_def not_FinalAllow)
  
  private lemma helper1: "a \<and> (a \<longrightarrow> b) \<longleftrightarrow> a \<and> b" by auto

  private lemma "simple_ruleset (rs @ [Rule r Accept]) \<Longrightarrow> 
         (setbydecision iface rs FinalAllow \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) r Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}) = 
           setbydecision iface (rs @ [Rule r Accept]) FinalAllow"
      apply(simp add: setbydecision_append)
      apply(simp add: helper1)
      apply(rule)
       prefer 2
       apply blast (*have ?r \<subseteq> ?l. would this suffice for an approximation (sound but not complete) of nospoof?*)
      apply(simp)
      apply(safe)
      apply(drule notin_setbydecisionD)
      apply(rule_tac x="p" in exI)
      apply(simp)
      (* okay, if we can make sure that this particular packet was not denied before, we are done here *)
       oops




  private lemma "- {ip. \<exists>p. \<not> match_iface iface (p_iiface p) \<or> \<not> matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_src := ip\<rparr>)}
      \<subseteq> setbydecision_all iface ([Rule m Drop]) FinalDeny"
      apply(simp add: setbydecision_all_def)
      apply(subst Collect_neg_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(simp)
      done

  private lemma setbydecision_all_not_iface: "(\<Inter> if' \<in> {if'. \<not> match_iface iface if'}. setbydecision_all (Iface if') rs1 FinalDeny) = 
      {ip. \<forall>p. \<not> match_iface iface (p_iiface p) \<longrightarrow> 
          approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs1 Undecided = Decision FinalDeny}"
    apply(simp add: setbydecision_all_def)
    apply(safe)
     apply(simp_all)
    apply(erule_tac x="(p_iiface p)" in allE)
    apply(simp)
    using p_iiface_update by metis


  private lemma setbydecision_all2: "setbydecision_all iface rs dec = 
      {ip. \<forall>p. (iface_sel iface) = (p_iiface p) \<longrightarrow> approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec}"
    apply(simp add: setbydecision_all_def)
    apply(rule Set.Collect_cong)
    apply(rule iffI)
     apply(clarify)
     apply(erule_tac x=p in allE)
     apply(simp)
    apply(clarify)
    apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface\<rparr>" in allE)
    apply(simp)
    done
  private lemma "{ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec} =
                 {ip | ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec}" by simp

  private lemma setbydecision_all2': "setbydecision_all iface rs dec = 
      {ip. \<forall>p. (iface_sel iface) = (p_iiface p) \<longrightarrow> p_src p = ip \<longrightarrow> approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision dec}"
    apply(simp add: setbydecision_all_def)
    apply(rule Set.Collect_cong)
    apply(rule iffI)
     apply(clarify)
     apply(erule_tac x=p in allE)
     apply(simp)
    apply(clarify)
    apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>" in allE)
    apply(simp)
    done

  private lemma setbydecision_all3: "setbydecision_all iface rs dec = (\<Inter> p \<in> {p. (iface_sel iface) = (p_iiface p)}. 
        {ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec})"
    apply(simp add: setbydecision_all2)
    by blast

  (*WTF?*)
  private lemma setbydecision_all3': "setbydecision_all iface rs dec = (\<Inter> p \<in> {p. (iface_sel iface) = (p_iiface p)}. 
        {ip | ip. p_src p = ip \<longrightarrow> approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision dec})"
    apply(simp add: setbydecision_all3)
    apply(safe)
    apply(simp_all)
    by fastforce

  (*this is a bit WTF*)
  private lemma setbydecision_all4: "setbydecision_all iface rs dec =
    (\<Inter> p \<in> {p. \<not> approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision dec}. 
            {ip. p_src p = ip \<longrightarrow> (iface_sel iface) \<noteq> (p_iiface p)})"
    apply(simp add: setbydecision_all2')
    apply(safe)
    apply(simp_all)
    by blast


  private lemma setbydecision2: "setbydecision iface rs dec = 
      {ip. \<exists>p. (iface_sel iface) = (p_iiface p) \<and> approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec}"
    apply(simp add: setbydecision_def)
    apply(rule Set.Collect_cong)
    apply(rule iffI)
     apply(clarify)
     apply(rule_tac x="p\<lparr>p_iiface := iface_sel iface\<rparr>" in exI)
     apply(simp)
    apply(clarify)
    apply(rule_tac x="p" in exI)
    apply(simp)
    done

  private lemma setbydecision3: "setbydecision iface rs dec = (\<Union> p \<in> {p. (iface_sel iface) = (p_iiface p)}. 
        {ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs Undecided = Decision dec})"
    apply(simp add: setbydecision2)
    by blast

  private lemma "{ip. (iface_sel iface) = (p_iiface p) \<and> p_src p = ip} = {ip | ip. (iface_sel iface) = (p_iiface p) \<and> p_src p = ip}" by simp

  private lemma setbydecision4: "setbydecision iface rs dec = 
    (\<Union> p \<in> {p. approximating_bigstep_fun (common_matcher, in_doubt_allow) p rs Undecided = Decision dec}. 
            {ip. (iface_sel iface) = (p_iiface p) \<and> p_src p = ip})"
    apply(simp add: setbydecision2)
    by fastforce

  (*lemma "- {ip. \<forall>p. \<not> match_iface iface (p_iiface p) \<longrightarrow> 
          approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_src := ip\<rparr>) rs1 Undecided = Decision FinalDeny} = {ip. P ip}"
    apply(subst Collect_neg_eq[symmetric])
    apply(rule Set.Collect_cong)
    apply(simp)
    oops*)


  private lemma "setbydecision_all iface rs FinalDeny \<subseteq> - setbydecision iface rs FinalAllow"
      apply(simp add: setbydecision_def setbydecision_all_def)
      apply(subst Set.Collect_neg_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(simp)
      done

  lemma "a - (d1 \<union> (d2 - a)) = a - d1" by auto
  
  private lemma xxhlpsubset1: "Y \<subseteq> X \<Longrightarrow> \<forall> x. S x \<subseteq> S' x \<Longrightarrow> (\<Inter>x\<in>X. S x) \<subseteq> (\<Inter>x\<in>Y. S' x)" by auto
  private lemma xxhlpsubset2: "X \<subseteq> Y \<Longrightarrow> \<forall> x. S x \<subseteq> S' x \<Longrightarrow> (\<Union>x\<in>X. S x) \<subseteq> (\<Union>x\<in>Y. S' x)" by auto


  private lemma no_spoofing_algorithm_sound_generalized: 
  shows "simple_ruleset rs1 \<Longrightarrow> simple_ruleset rs2 \<Longrightarrow>
        (\<forall>r \<in> set rs2. normalized_nnf_match (get_match r)) \<Longrightarrow>
        setbydecision iface rs1 FinalAllow \<subseteq> allowed \<Longrightarrow>
        denied1 \<subseteq> setbydecision_all iface rs1 FinalDeny \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs2 allowed denied1 \<Longrightarrow>
        nospoof iface ipassmt (rs1@rs2)"
  proof(induction iface ipassmt rs2 allowed denied1 arbitrary: rs1 allowed denied1 rule: no_spoofing_algorithm.induct)
  case (1 iface ipassmt)
    from 1 have "allowed - denied1 \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))"
      by(simp)
    with 1 have "setbydecision iface rs1 FinalAllow - setbydecision_all iface rs1 FinalDeny
          \<subseteq> ipv4cidr_union_set (set (the (ipassmt iface)))"
      by blast
       
    thus ?case 
      by(simp add: nospoof_setbydecision setbydecision_setbydecision_all_Allow)
  next
  case (2 iface ipassmt m rs)
    from 2(2) have simple_rs1: "simple_ruleset rs1" by(simp add: simple_ruleset_def)
    hence simple_rs': "simple_ruleset (rs1 @ [Rule m Accept])" by(simp add: simple_ruleset_def)
    from 2(3) have simple_rs: "simple_ruleset rs" by(simp add: simple_ruleset_def)
    with 2 have IH: "\<And>rs' allowed denied1.
      simple_ruleset rs' \<Longrightarrow>
      setbydecision iface rs' FinalAllow \<subseteq> allowed \<Longrightarrow>
      denied1 \<subseteq> setbydecision_all iface rs' FinalDeny \<Longrightarrow> 
      no_spoofing_algorithm iface ipassmt rs allowed denied1 \<Longrightarrow> nospoof iface ipassmt (rs' @ rs)"
      by(simp)
    from 2(5) simple_rs' have "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> 
      (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})" 
      apply(simp add: setbydecision_append)
      apply(simp add: helper1)
      by blast
    with get_exists_matching_src_ips_subset 2(4) have allowed: "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> (allowed \<union> get_exists_matching_src_ips iface m)"
      by fastforce
      
    from 2(6) setbydecision_all_appendAccept[OF simple_rs'] have denied1: "denied1 \<subseteq> setbydecision_all iface (rs1 @ [Rule m Accept]) FinalDeny" by simp

    from 2(7) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs
         (allowed \<union> get_exists_matching_src_ips iface m) denied1"
      by(simp)

    from IH[OF simple_rs' allowed denied1 no_spoofing_algorithm_prems] have "nospoof iface ipassmt ((rs1 @ [Rule m Accept]) @ rs)" by blast
    thus ?case by(simp)
  next
  case (3 iface ipassmt m rs)
    from 3(2) have simple_rs1: "simple_ruleset rs1" by(simp add: simple_ruleset_def)
    hence simple_rs': "simple_ruleset (rs1 @ [Rule m Drop])" by(simp add: simple_ruleset_def)
    from 3(3) have simple_rs: "simple_ruleset rs" by(simp add: simple_ruleset_def)
    with 3 have IH: "\<And>rs' allowed denied1.
      simple_ruleset rs' \<Longrightarrow>
      setbydecision iface rs' FinalAllow \<subseteq> allowed \<Longrightarrow>
      denied1 \<subseteq> setbydecision_all iface rs' FinalDeny \<Longrightarrow> 
      no_spoofing_algorithm iface ipassmt rs allowed denied1 \<Longrightarrow> nospoof iface ipassmt (rs' @ rs)"
      by(simp)
    from 3(5) simple_rs' have allowed: "setbydecision iface (rs1 @ [Rule m Drop]) FinalAllow \<subseteq> allowed "
      by(simp add: setbydecision_append)
    
    have "{ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} \<subseteq> 
          setbydecision_all iface [Rule m Drop] FinalDeny" by(simp add: setbydecision_all_def)
    with 3(5) have "setbydecision_all iface rs1 FinalDeny \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
          setbydecision_all iface rs1 FinalDeny \<union> (setbydecision_all iface [Rule m Drop] FinalDeny - setbydecision iface rs1 FinalAllow)"
      by blast
    with 3(6) setbydecision_all_append_subset2[OF simple_rs', of iface] have
     "denied1 \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
      setbydecision_all iface (rs1 @ [Rule m Drop]) FinalDeny"
      by blast
    with get_all_matching_src_ips 3(4) have denied1:
     "denied1 \<union> (get_all_matching_src_ips iface m - allowed) \<subseteq> setbydecision_all iface (rs1 @ [Rule m Drop]) FinalDeny"
      by force


    from 3(7) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs allowed
     (denied1 \<union> (get_all_matching_src_ips iface m - allowed))"
      apply(simp)
      done

    from IH[OF simple_rs' allowed denied1 no_spoofing_algorithm_prems] have "nospoof iface ipassmt ((rs1 @ [Rule m Drop]) @ rs)" by blast
    thus ?case by(simp)
  next
  case "4_1" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_2" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_3" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_4" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_5" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_6" thus ?case by(simp add: simple_ruleset_def)
  next
  case "4_7" thus ?case by(simp add: simple_ruleset_def)
  qed

  definition no_spoofing_iface :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> bool" where
    "no_spoofing_iface iface ipassmt rs \<equiv> no_spoofing_algorithm iface ipassmt rs {} {}"

  lemma[code]: "no_spoofing_iface iface ipassmt rs = 
      no_spoofing_algorithm_executable iface ipassmt rs Empty_WordInterval Empty_WordInterval"
    by(simp add: no_spoofing_iface_def no_spoofing_algorithm_executable)

  private corollary no_spoofing_algorithm_sound: "simple_ruleset rs \<Longrightarrow> \<forall>r\<in>set rs. normalized_nnf_match (get_match r) \<Longrightarrow>
        no_spoofing_iface iface ipassmt rs  \<Longrightarrow> nospoof iface ipassmt rs"
    unfolding no_spoofing_iface_def
    apply(rule no_spoofing_algorithm_sound_generalized[of "[]" rs iface "{}" "{}", simplified])
        apply(simp_all)
     apply(simp add: simple_ruleset_def)
    apply(simp add: setbydecision_def)
    done
    

  text{*The @{const nospoof} definition used throughout the proofs corresponds to checking @{const no_spoofing} for all interfaces*}
  private lemma nospoof: "simple_ruleset rs \<Longrightarrow> (\<forall>iface \<in> dom ipassmt. nospoof iface ipassmt rs) \<longleftrightarrow> no_spoofing ipassmt rs"
    unfolding nospoof_def no_spoofing_def
    apply(drule simple_imp_good_ruleset)
    apply(subst approximating_semantics_iff_fun_good_ruleset)
    apply(simp_all)
    done


  theorem no_spoofing_iface: "simple_ruleset rs \<Longrightarrow> \<forall>r\<in>set rs. normalized_nnf_match (get_match r) \<Longrightarrow>
        \<forall>iface \<in> dom ipassmt. no_spoofing_iface iface ipassmt rs  \<Longrightarrow> no_spoofing ipassmt rs"
    by(auto dest: nospoof no_spoofing_algorithm_sound)
  

  lemma "no_spoofing_iface
      (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> [(ipv4addr_of_dotdecimal (192,168,0,0), 24)]]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (Match (IIface (Iface ''eth0'')))) action.Accept,
           Rule MatchAny action.Drop]" by eval
end


value[code] "no_spoofing_iface (Iface ''eth1.1011'') ([Iface ''eth1.1011'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,0), 24)]]:: ipassignment)
  [Rule (MatchNot (Match (IIface (Iface ''eth1.1011+'')))) action.Accept,
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (131,159,14,0) 24)))) (Match (IIface (Iface ''eth1.101'')))) action.Drop,
           Rule MatchAny action.Accept]"

value[code] "no_spoofing_iface (Iface ''eth1.1011'') ([Iface ''eth1.1011'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,0), 24)]]:: ipassignment)
  [Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) Drop]"


end