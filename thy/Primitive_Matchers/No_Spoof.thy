theory No_Spoof
imports Common_Primitive_Lemmas
        Ipassmt
begin

section{*No Spoofing*}
(* we do this in ternary (not simple firewall) to support negated interfaces *)
  text{*assumes: @{const simple_ruleset}*}


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
        See @{const all_but_those_ips} to easily specify these ranges.

        See examples below. Check Example 3 why it can be thought of as OUTGOING spoofing.*}



(*
and now code to check spoofing protection
*)
context
begin
  text{*The set of any ip addresses which may match for a fixed @{text iface} (overapproximation)*}
  private definition get_exists_matching_src_ips :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_exists_matching_src_ips iface m \<equiv> let (i_matches, _) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface)
                                                  | Neg i \<Rightarrow> \<not> match_iface i (iface_sel iface)))
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
  lemma "primitive_extractor (is_Src, src_sel)
      (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 30))) (Match (IIface (Iface ''eth0'')))) =
      ([Pos (Ip4AddrNetmask (0, 0, 0, 0) 30)], MatchAnd MatchAny (Match (IIface (Iface ''eth0''))))" by eval

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

      from primitive_extractor_negation_type_matching1[OF wf_disc_sel_common_primitive(3) assms a1 a2]
           match_simplematcher_SrcDst match_simplematcher_SrcDst_not
       have ip_matches: "(\<forall>ip\<in>set (getPos ip_matches). p_src ?p \<in> ipv4s_to_set ip) \<and>
                         (\<forall>ip\<in>set (getNeg ip_matches). p_src ?p \<in> - ipv4s_to_set ip)" by simp
      from ip_matches have "\<forall>x \<in> set ip_matches. src_ip \<in> (case x of Pos x \<Rightarrow> ipv4s_to_set x | Neg ip \<Rightarrow> - ipv4s_to_set ip)"
        apply(simp)
        apply(simp  split: negation_type.split)
        apply(safe)
         using NegPos_set apply fast+
      done
    } note 1=this

    { fix ip_matches p rest src_ip i_matches rest2
      assume a1: "primitive_extractor (is_Iiface, iiface_sel) m = (i_matches, rest2)"
         and a2: "matches ?\<gamma> m a (p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      let ?p="(p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
    
      from primitive_extractor_negation_type_matching1[OF wf_disc_sel_common_primitive(5) assms a1 a2]
           match_simplematcher_Iface match_simplematcher_Iface_not
      have iface_matches: "(\<forall>i\<in>set (getPos i_matches). match_iface i (p_iiface ?p)) \<and>
                           (\<forall>i\<in>set (getNeg i_matches). \<not> match_iface i (p_iiface ?p))" by simp
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


  (*TODO: could this be useful somewhere?*)
  lemma common_primitive_not_has_primitive_expand: 
        "\<not> has_primitive (m::common_primitive match_expr) \<longleftrightarrow>
         \<not> has_disc is_Dst m \<and> 
         \<not> has_disc is_Src m \<and>
         \<not> has_disc is_Iiface m \<and>
         \<not> has_disc is_Oiface m \<and>
         \<not> has_disc is_Prot m \<and>
         \<not> has_disc is_Src_Ports m \<and>
         \<not> has_disc is_Dst_Ports m \<and>
         \<not> has_disc is_L4_Flags m \<and>
         \<not> has_disc is_CT_State m \<and>
         \<not> has_disc is_Extra m"
  apply(induction m)
     apply(simp_all)
    apply(rename_tac x, case_tac x, simp_all)
   by blast
  (*TODO: we can clean up the \<not>has_disc hell below with \<not> has_primitive*)
  lemma assumes n: "normalized_nnf_match m"
        and p1: "(primitive_extractor (is_Iiface, iiface_sel) m) = (i_matches, rest1)"
        and p2: "(primitive_extractor (is_Src, src_sel) rest1) = (ip_matches, rest2)"
        shows "\<not> has_disc is_Dst rest2 \<and> 
               \<not> has_disc is_Oiface rest2 \<and>
               \<not> has_disc is_Prot rest2 \<and>
               \<not> has_disc is_Src_Ports rest2 \<and>
               \<not> has_disc is_Dst_Ports rest2 \<and>
               \<not> has_disc is_L4_Flags rest2 \<and>
               \<not> has_disc is_CT_State rest2 \<and>
               \<not> has_disc is_Extra rest2 \<longleftrightarrow>
               \<not> has_primitive rest2"
    using p1 p2
    unfolding common_primitive_not_has_primitive_expand
    apply -
    apply(frule primitive_extractor_correct(2)[OF n wf_disc_sel_common_primitive(5)])
    apply(frule primitive_extractor_correct(3)[OF n wf_disc_sel_common_primitive(5)])
    apply(frule primitive_extractor_correct(4)[OF n wf_disc_sel_common_primitive(5)])
    apply(frule primitive_extractor_correct(3)[OF _ wf_disc_sel_common_primitive(3)], simp)
    apply(frule primitive_extractor_correct(4)[OF _ wf_disc_sel_common_primitive(3)], simp)
    by blast

  text{*The set of ip addresses which definitely match for a fixed @{text iface} (underapproximation)*}
  private definition get_all_matching_src_ips :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_all_matching_src_ips iface m \<equiv> let (i_matches, rest1) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface)
                                                  | Neg i \<Rightarrow> \<not> match_iface i (iface_sel iface)))
              then
                (let (ip_matches, rest2) = (primitive_extractor (is_Src, src_sel) rest1) in
                if \<not> has_disc is_Dst rest2 \<and> 
                   \<not> has_disc is_Oiface rest2 \<and>
                   \<not> has_disc is_Prot rest2 \<and>
                   \<not> has_disc is_Src_Ports rest2 \<and>
                   \<not> has_disc is_Dst_Ports rest2 \<and>
                   \<not> has_disc is_L4_Flags rest2 \<and>
                   \<not> has_disc is_CT_State rest2 \<and>
                   \<not> has_disc is_Extra rest2 \<and> 
                   matcheq_matchAny rest2
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
    shows "get_all_matching_src_ips iface m \<subseteq>
            {ip. (\<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))}"
  proof 
    fix ip
    assume a: "ip \<in> get_all_matching_src_ips iface m" 
    obtain i_matches rest1 where select1: "primitive_extractor (is_Iiface, iiface_sel) m = (i_matches, rest1)" by fastforce
    show "ip \<in> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}"
    proof(cases "\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface)
                                                 | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface))")
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
                      \<not> has_disc is_L4_Flags rest2 \<and>
                      \<not> has_disc is_CT_State rest2 \<and>
                      \<not> has_disc is_Extra rest2"

      have get_all_matching_src_ips_caseTrue: "get_all_matching_src_ips iface m = (if ?noDisc \<and> matcheq_matchAny rest2
                   then if ip_matches = [] then UNIV else INTER (set ip_matches) (case_negation_type ipv4s_to_set (\<lambda>ip. - ipv4s_to_set ip)) else {})"
      unfolding get_all_matching_src_ips_def
      by(simp add: True select1 select2)

      from True have "\<And>p. (\<forall>m\<in>set (getPos i_matches). matches (common_matcher, in_doubt_allow) (Match (IIface m)) a (?p p)) \<and>
         (\<forall>m\<in>set (getNeg i_matches). matches (common_matcher, in_doubt_allow) (MatchNot (Match (IIface m))) a (?p p))"
         by(simp add: negation_type_forall_split match_simplematcher_Iface match_simplematcher_Iface_not)
      hence matches_iface: "\<And>p. matches ?\<gamma> (alist_and (NegPos_map IIface i_matches)) a (?p p)"
        by(simp add: matches_alist_and NegPos_map_simps)

      show ?thesis
      proof(cases "?noDisc \<and> matcheq_matchAny rest2")
      case False
        assume F: "\<not> (?noDisc \<and> matcheq_matchAny rest2)"
        with get_all_matching_src_ips_caseTrue have "get_all_matching_src_ips iface m = {}" by presburger
        with a have False by simp
        thus "ip \<in> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}" ..
      next
      case True
        assume F: "?noDisc \<and> matcheq_matchAny rest2"
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
            apply fast
           apply fast
           using no_iiface_rest1 by fast

        from F have ?noDisc by simp
        with no_Src_rest2 no_IIface_rest2 have "\<not> has_primitive rest2"
          apply(induction rest2)
             apply(simp_all)
          apply(rename_tac x)
          apply(case_tac x, auto)
          done
        with F matcheq_matchAny have "\<And>p. matches ?\<gamma> rest2 a p" by metis
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

  lemma "(get_exists_matching_src_ips_executable (Iface ''eth0'')
      (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0''))))) =
      RangeUnion (WordInterval 0 0xC0A7FFFF) (WordInterval 0xC0A80100 0xFFFFFFFF)" by eval

  private definition get_all_matching_src_ips_executable :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> 32 wordinterval" where
    "get_all_matching_src_ips_executable iface m \<equiv> let (i_matches, rest1) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface)
                                                  | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, rest2) = (primitive_extractor (is_Src, src_sel) rest1) in
                if \<not> has_disc is_Dst rest2 \<and> 
                   \<not> has_disc is_Oiface rest2 \<and>
                   \<not> has_disc is_Prot rest2 \<and>
                   \<not> has_disc is_Src_Ports rest2 \<and>
                   \<not> has_disc is_Dst_Ports rest2 \<and>
                   \<not> has_disc is_L4_Flags rest2 \<and>
                   \<not> has_disc is_CT_State rest2 \<and>
                   \<not> has_disc is_Extra rest2 \<and> 
                   matcheq_matchAny rest2
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
  lemma "(get_all_matching_src_ips_executable (Iface ''eth0'')
      (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0''))))) = 
      RangeUnion (WordInterval 0 0xC0A7FFFF) (WordInterval 0xC0A80100 0xFFFFFFFF)" by eval



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
      wordinterval_subset (wordinterval_setminus allowed denied1) (l2br (map ipcidr_to_interval (the (ipassmt iface))))" |
    "no_spoofing_algorithm_executable iface ipassmt ((Rule m Accept)#rs) allowed denied1 = no_spoofing_algorithm_executable iface ipassmt rs 
        (wordinterval_union allowed (get_exists_matching_src_ips_executable iface m)) denied1" |
    "no_spoofing_algorithm_executable iface ipassmt ((Rule m Drop)#rs) allowed denied1 = no_spoofing_algorithm_executable iface ipassmt rs
         allowed (wordinterval_union denied1 (wordinterval_setminus (get_all_matching_src_ips_executable iface m) allowed))"  |
    "no_spoofing_algorithm_executable _ _ _ _ _  = undefined"

  lemma no_spoofing_algorithm_executable: "no_spoofing_algorithm_executable iface ipassmt rs allowed denied \<longleftrightarrow> 
         no_spoofing_algorithm iface ipassmt rs (wordinterval_to_set allowed) (wordinterval_to_set denied)"
  proof(induction iface ipassmt rs allowed denied rule: no_spoofing_algorithm_executable.induct)
  case (1 iface ipassmt allowed denied1)
    have "(\<Union>a\<in>set (the (ipassmt iface)). case ipcidr_to_interval a of (x, xa) \<Rightarrow> {x..xa}) = 
          (\<Union>x\<in>set (the (ipassmt iface)). case x of (base, len) \<Rightarrow> ipv4range_set_from_prefix base len)"
    unfolding ipcidr_to_interval_def (*since we used an arbitrary 'a::len word, we need to unfold manually*)
    using ipcidr_to_interval_ipv4range_set_from_prefix by simp
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
      have localrng: "ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (192,168,0,0)) 24 = {0xC0A80000..0xC0A800FF}"
      by(simp add: ipv4range_set_from_prefix_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
        
      have ipset: "{ip. \<exists>p. matches (common_matcher, in_doubt_allow) (MatchAnd (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24))) (Match (IIface (Iface ''eth0'')))) Accept
              (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (192,168,0,0)) 24"
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

   private lemma iprange_example: "ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24 = {0xC0A80000..0xC0A800FF}"
     by(simp add: ipv4range_set_from_prefix_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
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
    from 2(5) have "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> 
      (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})"
      apply(simp add: setbydecision_append[OF simple_rs'])
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


lemma "no_spoofing_iface (Iface ''eth1.1011'')
                         ([Iface ''eth1.1011'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,0), 24)]]:: ipassignment)
  [Rule (MatchNot (Match (IIface (Iface ''eth1.1011+'')))) action.Accept,
   Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (131,159,14,0) 24)))) (Match (IIface (Iface ''eth1.1011'')))) action.Drop,
   Rule MatchAny action.Accept]" by eval

text{*We only check accepted packets.
      If there is no default rule (this will never happen if parsed from iptables!), the result is unfinished.*}
lemma "no_spoofing_iface (Iface ''eth1.1011'')
                         ([Iface ''eth1.1011'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,0), 24)]]:: ipassignment)
  [Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8))) Drop]" by eval


end