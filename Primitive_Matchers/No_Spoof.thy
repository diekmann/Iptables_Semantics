theory No_Spoof
imports Common_Primitive_Matcher
  "../Common/Negation_Type_DNF"
        Primitive_Normalization
begin

section{*No Spoofing*}
(* we do this in ternary (not simple firewall) to support things such as negated interfaces *)
  text{*assumes: @{const simple_ruleset}*}

  text{*A mapping from an interface to its assigned ip addresses in CIDR notation*}
  type_synonym ipassignment="iface \<rightharpoonup> (ipv4addr \<times> nat) set"

  (*
  check wool: warning if zone-spanning
  
  warning if interface map has wildcards
  
  warning if interface occurs in ruleset but not in ipassignment (typo?)
  *)

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
            p_src p \<in> (ipv4cidr_union_set (the (ipassmt iface)))"

  text{* The definition is sound (if that can be said about a definition):
          if @{const no_spoofing} certifies your ruleset, then your ruleset prohibits spoofing.
         The definition may not be complete:
          @{const no_spoofing} may return @{const False} even though your ruleset prevents spoofing
          (should only occur if some strange and unknown primitives occur)*}


text{*everything in the following context is just an unfinished draft*}
context
begin
(*
and now code to check this ....
*)


  text{*The set of any ip addresses which match for a fixed @{text iface}*}
  private definition get_matching_src_ips :: "iface \<Rightarrow> common_primitive match_expr \<Rightarrow> ipv4addr set" where
    "get_matching_src_ips iface m \<equiv> let (i_matches, _) = (primitive_extractor (is_Iiface, iiface_sel) m) in
              if (\<forall> is \<in> set i_matches. (case is of Pos i \<Rightarrow> match_iface i (iface_sel iface) | Neg i \<Rightarrow> \<not>match_iface i (iface_sel iface)))
              then
                (let (ip_matches, _) = (primitive_extractor (is_Src, src_sel) m) in
                if ip_matches = []
                then
                  UNIV
                else
                  \<Union> ips \<in> set (ip_matches). (case ips of Pos ip \<Rightarrow> ipv4s_to_set ip | Neg ip \<Rightarrow> - ipv4s_to_set ip))
              else
                {}"

  (*when we replace the set by a 32 wordinterval, we should get executable code*)
  value(code) "primitive_extractor (is_Src, src_sel) (MatchAnd (Match (Src (Ip4AddrNetmask (0,0,0,0) 30))) (Match (IIface (Iface ''eth0''))))"

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

 private lemma get_matching_src_ips_subset: 
    assumes "normalized_nnf_match m"
    shows "{ip. (\<exists>p. matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))} \<subseteq>
           get_matching_src_ips iface m"
  proof -
    
    { fix ip_matches p rest src_ip i_matches rest2
      assume a1: "primitive_extractor (is_Src, src_sel) m = (ip_matches, rest)"
      and a2: "matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      let ?p="(p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      let ?\<gamma>="(common_matcher, in_doubt_allow)"
  
      from primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(3) a1] have 
        "\<And>p. matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map Src ip_matches)) a p \<and> 
              matches (common_matcher, in_doubt_allow) rest a p \<longleftrightarrow>
              matches (common_matcher, in_doubt_allow) m a p" by fast
      with a2 have "matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map Src ip_matches)) a ?p \<and> 
              matches (common_matcher, in_doubt_allow) rest a ?p" by simp
      hence "matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map Src ip_matches)) a ?p" by blast
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
      assume a2: "matches (common_matcher, in_doubt_allow) m a (p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      and a4: "primitive_extractor (is_Iiface, iiface_sel) m = (i_matches, rest2)"
      let ?p="(p\<lparr>p_iiface := iface_sel iface, p_src := src_ip\<rparr>)"
      let ?\<gamma>="(common_matcher, in_doubt_allow)"
    
      from primitive_extractor_correct(1)[OF assms wf_disc_sel_common_primitive(5) a4] have 
        "\<And>p. matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map IIface i_matches)) a p \<and> 
              matches (common_matcher, in_doubt_allow) rest2 a p \<longleftrightarrow>
              matches (common_matcher, in_doubt_allow) m a p" by fast
      with a2 have "matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map IIface i_matches)) a ?p \<and> 
              matches (common_matcher, in_doubt_allow) rest2 a ?p" by simp
      hence "matches (common_matcher, in_doubt_allow) (alist_and (NegPos_map IIface i_matches)) a ?p" by blast
      with Negation_Type_Matching.matches_alist_and have
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

    have very_stupid_helper: "\<And>aaa. aaa \<noteq> [] \<Longrightarrow> \<exists>x. x \<in> set aaa"
      apply(case_tac aaa)
       apply(simp_all)
      by blast

    from 1 2 show ?thesis
      unfolding get_matching_src_ips_def
      apply(clarsimp)
      using very_stupid_helper by fast
  qed


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
    denied1: set of ips definetely dropped for iface*)
  private fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr set \<Rightarrow> (*ipv4addr set \<Rightarrow>*) bool" where
    "no_spoofing_algorithm iface ipassmt [] allowed denied1 (*denied2*) \<longleftrightarrow> 
      (allowed - (denied1 (*\<union> - denied2*))) \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Accept)#rs) allowed denied1 (*denied2*) = no_spoofing_algorithm iface ipassmt rs 
        (allowed \<union> get_matching_src_ips iface m) denied1 (*denied2*)" |
    "no_spoofing_algorithm iface ipassmt ((Rule m Drop)#rs) allowed denied1 (*denied2*) = no_spoofing_algorithm iface ipassmt rs
         allowed
         (denied1 \<union> ({ip.(\<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface:= iface_sel iface, p_src:= ip\<rparr>))} - allowed))
         (*(denied2 \<union> ({ip. \<forall>p. \<not> match_iface iface (p_iiface p) \<longrightarrow> matches (common_matcher, in_doubt_allow) m Drop (p\<lparr> p_src:= ip\<rparr>)} - allowed))*)"  |
    "no_spoofing_algorithm _ _ _ _ _  = undefined"

  (*implementation could store ipv4addr set as 32 wordinterval*)

  (*we can tune accuracy when only adding to allowed if it is not in denied?*)

  (*TODO: we could add a second denied set: {ip. (\<forall>p. p not from iface \<rightarrow> matches p(p_src := ip)}*)
  (*TODO: test if this suffices to make example 3 work
    
    possible invariant: allowed \<inter> denied2 = {}
    only add to allowed if not in denied 2
    only add to denied2 if not in allowed
  
      *)


  text{*Examples*}
  text{*
    Ruleset: Accept all non-spoofed packets, drop rest.
  *}
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> {(ipv4addr_of_dotdecimal (192,168,0,0), 24)}]
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
        apply(simp add: ipset ipv4cidr_union_set_def get_matching_src_ips_def)
        by blast
      qed

  text{*
    Ruleset: Drop packets from a spoofed IP range, allow rest.
  *}
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> {(ipv4addr_of_dotdecimal (192,168,0,0), 24)}]
          [Rule (MatchAnd (Match (IIface (Iface ''wlan+''))) (Match (Extra ''no idea what this is''))) action.Accept,
           Rule (MatchNot (Match (IIface (Iface ''eth0+'')))) action.Accept,
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))) action.Drop,
           Rule MatchAny action.Accept]
          {} {}
          "
     proof -
      have ipset1: "{ip. \<exists>p. matches (common_matcher, in_doubt_allow) MatchAny Accept (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = UNIV"
         by(auto simp add: eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple
                      split: ternaryvalue.split ternaryvalue.split_asm)

       have ipset2: "{ip. \<forall>p. matches (common_matcher, in_doubt_allow)
                     (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24)))) (Match (IIface (Iface ''eth0'')))) Drop
                     (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = - ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192,168,0,0)) 24"
         by(auto simp add:  eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple match_iface.simps
                      split: ternaryvalue.split ternaryvalue.split_asm)
       have i2: "(\<forall>p. match_iface (Iface ''eth0'') (p_iiface p)) \<longleftrightarrow> False"
        apply(simp add: match_iface.simps)
        apply(rule_tac x="p\<lparr>p_iiface := ''eth1''\<rparr>" in exI)
        apply(simp)
        done
       have i1: "match_iface (Iface ''eth0'') ''eth0''" by(simp add: match_iface.simps)
       have ipset3: "{ip. \<forall>p. \<not> match_iface (Iface ''eth0'') (p_iiface p) \<longrightarrow>
                       matches (common_matcher, in_doubt_allow)
                        (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24)))) (Match (IIface (Iface ''eth0'')))) Drop (p\<lparr>p_src := ip\<rparr>)}
                      = {}"
         apply(simp add: bool_to_ternary_pullup eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple
                      split: ternaryvalue.split ternaryvalue.split_asm)
          apply(simp add: match_iface.simps)
          apply(rule_tac x="p\<lparr>p_iiface := ''eth1''\<rparr>" in exI)
          apply(simp)
         done
       show ?thesis
        apply(simp add: ipset1)
        apply(simp add: ipset2)
        apply(simp add: get_matching_src_ips_def match_iface.simps)
        (*apply(simp add: ipset3)*)
        apply(simp add: ipv4cidr_union_set_def)
        done
      qed

   private lemma iprange_example: "ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24 = {0xC0A80000..0xC0A800FF}"
     by(simp add: ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
   lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> {(ipv4addr_of_dotdecimal (192,168,0,0), 24)}]
          [Rule (MatchNot (Match (IIface (Iface ''wlan+'')))) action.Accept, (*accidently allow everything for eth0*)
           Rule (MatchAnd (MatchNot (Match (Src (Ip4AddrNetmask (192,168,0,0) 24)))) (Match (IIface (Iface ''eth0'')))) action.Drop,
           Rule MatchAny action.Accept]
          {} {} \<longleftrightarrow> False
          "
        apply(simp add: get_matching_src_ips_def match_iface.simps)
        apply(simp add: range_0_max_UNIV[symmetric] ipv4cidr_union_set_def iprange_example del:range_0_max_UNIV)
        done

  text{*
    Ruleset: Drop packets coming from the wrong interface, allow rest.
  *}
  (*fails*)
  lemma "no_spoofing_algorithm 
          (Iface ''eth0'') 
          [Iface ''eth0'' \<mapsto> {(ipv4addr_of_dotdecimal (192,168,0,0), 24)}]
          [Rule (MatchAnd (Match (Src (Ip4AddrNetmask (192,168,0,0) 24))) (MatchNot (Match (IIface (Iface ''eth0''))))) action.Drop,
           Rule MatchAny action.Accept]
          {} {}
          "
     proof -
      have ipset1: "{ip. \<exists>p. matches (common_matcher, in_doubt_allow) MatchAny Accept (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = UNIV"
         by(auto simp add: eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple
                      split: ternaryvalue.split ternaryvalue.split_asm)

       have ipset2: "{ip. \<forall>p. matches (common_matcher, in_doubt_allow)
                     (MatchAnd (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24))) (MatchNot (Match (IIface (Iface ''eth0''))))) Drop
                     (p\<lparr>p_iiface := ''eth0'', p_src := ip\<rparr>)} = {}"
         by(simp add:  eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple match_iface.simps
                      split: ternaryvalue.split ternaryvalue.split_asm)
       
       have i2: "(\<forall>p. match_iface (Iface ''eth0'') (p_iiface p)) \<longleftrightarrow> False"
        apply(simp add: match_iface.simps)
        apply(rule_tac x="p\<lparr>p_iiface := ''eth1''\<rparr>" in exI)
        apply(simp)
        done
       have i1: "match_iface (Iface ''eth0'') ''eth0''" by(simp add: match_iface.simps)
       have ipset3: "{ip. \<forall>p. \<not> match_iface (Iface ''eth0'') (p_iiface p) \<longrightarrow>
              matches (common_matcher, in_doubt_allow)
               (MatchAnd (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 24))) (MatchNot (Match (IIface (Iface ''eth0''))))) Drop (p\<lparr>p_src := ip\<rparr>)}
                     = ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24"
         apply(simp add: bool_to_ternary_pullup eval_ternary_simps bool_to_ternary_simps matches_case_ternaryvalue_tuple
                      split: ternaryvalue.split ternaryvalue.split_asm)
         apply(simp add: i1 i2)
         done
       show ?thesis
        apply(subst no_spoofing_algorithm.simps)
        apply(simp add: ipset1 ipset2 ipset3 del: no_spoofing_algorithm.simps)
        apply(subst no_spoofing_algorithm.simps)
        apply(simp add: ipset1 ipset2 ipset3 del: no_spoofing_algorithm.simps)
        apply(simp)
        apply(simp add: ipv4cidr_union_set_def)
        oops
   

  private definition "nospoof iface ipassmt rs = (\<forall>p.
          (approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface:=iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow) \<longrightarrow>
              p_src p \<in> (ipv4cidr_union_set (the (ipassmt iface))))"
  private definition "setbydecision iface rs dec = {ip. \<exists>p. approximating_bigstep_fun (common_matcher, in_doubt_allow) 
                           (p\<lparr>p_iiface:=iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision dec}"

  private lemma packet_update_iface_simp: "p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr> = p\<lparr>p_src := x, p_iiface := iface_sel iface\<rparr>" by simp
 
  private lemma nospoof_setbydecision: "nospoof iface ipassmt rs \<longleftrightarrow> setbydecision iface rs FinalAllow \<subseteq> (ipv4cidr_union_set (the (ipassmt iface)))"
  proof
    assume a: "nospoof iface ipassmt rs"
    from a show "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      apply(simp add: nospoof_def setbydecision_def)
      apply(safe)
      apply(rename_tac x p)
      apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface, p_src := x\<rparr>" in allE)
      apply(simp)
      apply(simp add: packet_update_iface_simp)
      done
  next
    assume a1: "setbydecision iface rs FinalAllow \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
    show "nospoof iface ipassmt rs"
      unfolding nospoof_def
      proof(safe)
        fix p
        assume a2: "approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface\<rparr>) rs Undecided = Decision FinalAllow"
        --{*In @{text setbydecision_fix_p}the @{text \<exists>} quantifier is gone and we consider this set for @{term p}.*}
        let ?setbydecision_fix_p="{ip. approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Decision FinalAllow}"
        from a1 a2 have 1: "?setbydecision_fix_p \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" by(simp add: nospoof_def setbydecision_def) blast
        from a2 have 2: "p_src p \<in> ?setbydecision_fix_p" by simp
        from 1 2 show "p_src p \<in> ipv4cidr_union_set (the (ipassmt iface))" by blast
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

  private lemma assumes "simple_ruleset (rs @ [Rule m Drop])" shows "
    (setbydecision_all iface rs FinalDeny \<union> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})
    \<subseteq>
    setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny
    "
    proof -
    from setbydecision_all_append_subset[OF assms, of iface] have 1: "setbydecision_all iface rs FinalDeny \<union>
      {ip. \<forall>p.
        approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) [Rule m Drop] Undecided = Decision FinalDeny \<and>
        approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided}
      \<subseteq> setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny" by simp
    from setbydecision_all_append_subset2[OF assms, of iface] have x1:
      "setbydecision_all iface rs FinalDeny \<union> (setbydecision_all iface [Rule m Drop] FinalDeny - setbydecision iface rs FinalAllow)
      \<subseteq> setbydecision_all iface (rs @ [Rule m Drop]) FinalDeny" by simp
    have 2: "setbydecision_all iface rs FinalDeny \<union>
  {ip. \<forall>p. 
    approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) [Rule m Drop] Undecided = Decision FinalDeny \<and>
    approximating_bigstep_fun (common_matcher, in_doubt_allow) (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>) rs Undecided = Undecided} 
      \<subseteq>
   setbydecision_all iface rs FinalDeny \<union> {ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}"
    apply(simp add: helper1)
    apply(rule)
    by auto
    have 3: "{ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} =
       setbydecision_all iface [Rule m Drop] FinalDeny"
       by(simp add: setbydecision_all_def)
    show ?thesis
      unfolding 3
      unfolding setbydecision_all_def
      apply(subst Set.Collect_disj_eq[symmetric])
      apply(rule Set.Collect_mono)
      apply(subst approximating_bigstep_fun_seq_Undecided_t_wf)
       defer
       apply(simp_all)
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
        iface \<in> dom ipassmt \<Longrightarrow>
        setbydecision iface rs1 FinalAllow \<subseteq> allowed \<Longrightarrow> (* = *)
        denied1 \<subseteq> setbydecision_all iface rs1 FinalDeny \<Longrightarrow>
        (*(\<Inter> if' \<in> {if'. \<not> match_iface iface if'}. setbydecision_all (Iface if') rs1 FinalDeny) \<subseteq> denied2\<Longrightarrow>*)
        no_spoofing_algorithm iface ipassmt rs2 allowed denied1  \<Longrightarrow> (*\<longleftrightarrow>*)
        nospoof iface ipassmt (rs1@rs2)"
  proof(induction iface ipassmt rs2 allowed denied1 arbitrary: rs1 allowed denied1 rule: no_spoofing_algorithm.induct)
  case (1 iface ipassmt)
    from 1 have "allowed - denied1 \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      by(simp)
    with 1 have "setbydecision iface rs1 FinalAllow - setbydecision_all iface rs1 FinalDeny
          \<subseteq> ipv4cidr_union_set (the (ipassmt iface))"
      by blast
    (*hence "setbydecision iface rs1 FinalAllow -
      - (\<Inter> if' \<in> {if'. \<not> match_iface iface if'}. setbydecision_all (Iface if') rs1 FinalDeny)
          \<subseteq> ipv4cidr_union_set (the (ipassmt iface))" 
       apply(subst(asm) Set.Diff_Un)
       apply(simp add: setbydecision_setbydecision_all_Allow)
       apply(subst(asm) Set.Int_absorb1)
        apply(blast)
       by blast*)
       
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
    from 2(6) simple_rs' have "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> 
      (allowed \<union> {ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)})" 
      apply(simp add: setbydecision_append)
      apply(simp add: helper1)
      by blast
    with get_matching_src_ips_subset 2(4) have allowed: "setbydecision iface (rs1 @ [Rule m Accept]) FinalAllow \<subseteq> (allowed \<union> get_matching_src_ips iface m)"
      by fastforce
      
    from 2(7) setbydecision_all_appendAccept[OF simple_rs'] have denied1: "denied1 \<subseteq> setbydecision_all iface (rs1 @ [Rule m Accept]) FinalDeny" by simp

    from 2(8) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs
         (allowed \<union> get_matching_src_ips iface m) denied1"
      by(simp)

    (*{ip. \<exists>p. matches (common_matcher, in_doubt_allow) m Accept (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)}*)

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
    from 3(6) simple_rs' have allowed: "setbydecision iface (rs1 @ [Rule m Drop]) FinalAllow \<subseteq> allowed "
      by(simp add: setbydecision_append)
    
    have "{ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} \<subseteq> 
          setbydecision_all iface [Rule m Drop] FinalDeny" by(simp add: setbydecision_all_def)
    with 3(6) have "setbydecision_all iface rs1 FinalDeny \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
          setbydecision_all iface rs1 FinalDeny \<union> (setbydecision_all iface [Rule m Drop] FinalDeny - setbydecision iface rs1 FinalAllow)"
      by blast
    with 3(7) setbydecision_all_append_subset2[OF simple_rs', of iface] have denied1:
     "denied1 \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed) \<subseteq>
      setbydecision_all iface (rs1 @ [Rule m Drop]) FinalDeny"
      by blast


    from 3(8) have no_spoofing_algorithm_prems: "no_spoofing_algorithm iface ipassmt rs allowed
     (denied1 \<union> ({ip. \<forall>p. matches (common_matcher, in_doubt_allow) m Drop (p\<lparr>p_iiface := iface_sel iface, p_src := ip\<rparr>)} - allowed))"
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
  qed
  private corollary no_spoofing_algorithm_sound: "simple_ruleset rs \<Longrightarrow> \<forall>r\<in>set rs. normalized_nnf_match (get_match r) \<Longrightarrow>
        iface \<in> dom ipassmt \<Longrightarrow>
        no_spoofing_algorithm iface ipassmt rs {} {} \<Longrightarrow> nospoof iface ipassmt rs"
    apply(rule no_spoofing_algorithm_sound_generalized[of "[]" rs iface ipassmt "{}" "{}", simplified])
        apply(simp_all)
     apply(simp add: simple_ruleset_def)
    apply(simp add: setbydecision_def)
    done
    

  text{*The @{const nospoof} definition used throughout the proofs corresponds to checking @{const no_spoofing} for all interfaces*}
  lemma nospoof: "simple_ruleset rs \<Longrightarrow> (\<forall>iface \<in> dom ipassmt. nospoof iface ipassmt rs) \<longleftrightarrow> no_spoofing ipassmt rs"
    unfolding nospoof_def no_spoofing_def
    apply(drule simple_imp_good_ruleset)
    apply(subst approximating_semantics_iff_fun_good_ruleset)
    apply(simp_all)
    done
  
end


end