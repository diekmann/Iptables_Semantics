theory Output_Interface_Replace
imports
  Ipassmt
  Routing_IpAssmt
  Common_Primitive_toString
begin

section\<open>Replacing output interfaces by their IP ranges according to Routing\<close>

text\<open>Copy of @{file "Interface_Replace.thy"}\<close>

definition ipassmt_iface_replace_dstip_mexpr
  :: "'i::len ipassignment \<Rightarrow> iface \<Rightarrow> 'i common_primitive match_expr" where
  "ipassmt_iface_replace_dstip_mexpr ipassmt ifce \<equiv> case ipassmt ifce of
          None \<Rightarrow> Match (OIface ifce)
        | Some ips \<Rightarrow> (match_list_to_match_expr (map (Match \<circ> Dst) (map (uncurry IpAddrNetmask) ips)))"


lemma matches_ipassmt_iface_replace_dstip_mexpr: 
    "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_dstip_mexpr ipassmt ifce) a p \<longleftrightarrow> (case ipassmt ifce of
            None \<Rightarrow> match_iface ifce (p_oiface p)
          | Some ips \<Rightarrow> p_dst p \<in> ipcidr_union_set (set ips)
          )"
proof(cases "ipassmt ifce")
case None thus ?thesis by(simp add: ipassmt_iface_replace_dstip_mexpr_def primitive_matcher_generic.Iface_single[OF primitive_matcher_generic_common_matcher])
next
case (Some ips)
  have "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Dst \<circ> (uncurry IpAddrNetmask)) ips)) a p \<longleftrightarrow>
       (\<exists>m\<in>set ips. p_dst p \<in> (uncurry ipset_from_cidr m))" 
       by(simp add: match_list_to_match_expr_disjunction[symmetric]
                    match_list_matches match_simplematcher_SrcDst ipt_iprange_to_set_uncurry_IpAddrNetmask)
  with Some show ?thesis
    apply(simp add: ipassmt_iface_replace_dstip_mexpr_def bunch_of_lemmata_about_matches)
    apply(simp add: ipcidr_union_set_uncurry)
    done
qed


fun oiface_rewrite
  :: "'i::len ipassignment \<Rightarrow> 'i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr"
where
  "oiface_rewrite _       MatchAny = MatchAny" |
  "oiface_rewrite ipassmt (Match (OIface ifce)) = ipassmt_iface_replace_dstip_mexpr ipassmt ifce" |
  "oiface_rewrite ipassmt (Match a) = Match a" |
  "oiface_rewrite ipassmt (MatchNot m) = MatchNot (oiface_rewrite ipassmt m)" |
  "oiface_rewrite ipassmt (MatchAnd m1 m2) = MatchAnd (oiface_rewrite ipassmt m1) (oiface_rewrite ipassmt m2)"


context
begin
  (*helper1: used in induction case MatchNot*)
  private lemma oiface_rewrite_matches_Primitive:
          "matches (common_matcher, \<alpha>) (MatchNot (oiface_rewrite ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<longleftrightarrow>
           matches (common_matcher, \<alpha>) (oiface_rewrite ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
  proof(cases x)
  case (OIface ifce)
    have "(matches (common_matcher, \<alpha>) (MatchNot (ipassmt_iface_replace_dstip_mexpr ipassmt ifce)) a p = (\<not> match_iface ifce (p_oiface p))) \<longleftrightarrow>
      (matches (common_matcher, \<alpha>) (ipassmt_iface_replace_dstip_mexpr ipassmt ifce) a p = match_iface ifce (p_oiface p))"
    proof(cases "ipassmt ifce")
    case None thus ?thesis
       apply(simp add: matches_ipassmt_iface_replace_dstip_mexpr)
       apply(simp add: ipassmt_iface_replace_dstip_mexpr_def primitive_matcher_generic.Iface_single_not[OF primitive_matcher_generic_common_matcher])
       done
     next
     case (Some ips)
       {  fix ips
          have "matches (common_matcher, \<alpha>)
                 (MatchNot (match_list_to_match_expr (map (Match \<circ> Dst \<circ> (uncurry IpAddrNetmask)) ips))) a p \<longleftrightarrow>
                 (p_dst p \<notin> ipcidr_union_set (set ips))"
        apply(induction ips)
         apply(simp add: bunch_of_lemmata_about_matches ipcidr_union_set_uncurry)
        apply(simp add: MatchOr_MatchNot)
        apply(simp add: ipcidr_union_set_uncurry)
        apply(simp add: match_simplematcher_SrcDst_not)
        apply(thin_tac _)
        apply(simp add: ipt_iprange_to_set_uncurry_IpAddrNetmask)
        done
       } note helper=this
       from Some show ?thesis
         apply(simp add: matches_ipassmt_iface_replace_dstip_mexpr)
         apply(simp add: ipassmt_iface_replace_dstip_mexpr_def)
         apply(simp add: helper)
         done
     qed
     with OIface show ?thesis
      by(simp add: primitive_matcher_generic.Iface_single_not[OF primitive_matcher_generic_common_matcher]
            primitive_matcher_generic.Iface_single[OF primitive_matcher_generic_common_matcher])
  qed(simp_all)


  (*helper2: used in induction base case*)
  private lemma matches_ipassmt_iface_replace_dstip_mexpr_case_Iface:
        fixes ifce::iface
        assumes "ipassmt_sanity_nowildcards ipassmt"
            and "ipassmt_sanity_disjoint ipassmt"
            and "ipassmt (Iface (p_oiface p)) = Some p_ips \<and> p_dst p \<in> ipcidr_union_set (set p_ips)"
        shows   "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_dstip_mexpr ipassmt ifce) a p \<longleftrightarrow>
                 matches (common_matcher, \<alpha>) (Match (OIface ifce)) a p"
  proof -
    have "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_dstip_mexpr ipassmt ifce) a p = match_iface ifce (p_oiface p)"
      proof -
        show ?thesis
        proof(cases "ipassmt ifce")
          case None thus ?thesis by(simp add: matches_ipassmt_iface_replace_dstip_mexpr)
          next
          case (Some y) with assms(2) have "p_dst p \<in> ipcidr_union_set (set y) = match_iface ifce (p_oiface p)"
            using assms(1) assms(3) ipassmt_disjoint_matcheq_iifce_srcip by blast
            with Some show ?thesis by(simp add: matches_ipassmt_iface_replace_dstip_mexpr)
        qed
    qed
    thus ?thesis by(simp add: primitive_matcher_generic.Iface_single[OF primitive_matcher_generic_common_matcher])
  qed



  lemma matches_oiface_rewrite_ipassmt:
       "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_nowildcards ipassmt \<Longrightarrow> ipassmt_sanity_disjoint ipassmt \<Longrightarrow>
        (\<exists>p_ips. ipassmt (Iface (p_oiface p)) = Some p_ips \<and> p_dst p \<in> ipcidr_union_set (set p_ips)) \<Longrightarrow>
        matches (common_matcher, \<alpha>) (oiface_rewrite ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    proof(induction m)
    case MatchAny thus ?case by simp
    next
    case (MatchNot m)
      hence IH: "normalized_nnf_match m \<Longrightarrow>
        matches (common_matcher, \<alpha>) (oiface_rewrite ipassmt m) a p =matches (common_matcher, \<alpha>) m a p" by blast
      with MatchNot.prems IH show ?case by(induction m) (simp_all add: oiface_rewrite_matches_Primitive)
    next
    case(Match x) thus ?case
      proof(cases x)
        case (OIface ifce) with Match show ?thesis
        apply(cases "ipassmt (Iface (p_oiface p))")
         prefer 2
          apply(simp add: matches_ipassmt_iface_replace_dstip_mexpr_case_Iface; fail)
        by auto
      qed(simp_all)
    next
    case (MatchAnd m1 m2) thus ?case by(simp add: bunch_of_lemmata_about_matches)
    qed

  lemma matches_oiface_rewrite:
       "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_nowildcards ipassmt (*TODO: check?*) \<Longrightarrow>
        has_default_route rt \<Longrightarrow>
        correct_routing rt \<Longrightarrow>
        ipassmt = map_of (routing_ipassmt rt) \<Longrightarrow>
        routing_table_semantics rt (p_dst p) = \<lparr> output_iface = oifce, next_hop = ignored\<rparr> \<Longrightarrow>
        (*packet correctly routed:*) p_oiface p = oifce \<Longrightarrow>
        matches (common_matcher, \<alpha>) (oiface_rewrite ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
  apply(rule matches_oiface_rewrite_ipassmt)
     apply(simp; fail)
    apply(simp; fail)
   apply(simp)
   apply(rule routing_ipassmt_ipassmt_sanity_disjoint)
   apply(simp add: correct_routing_def; fail)
  apply(simp)
  apply(rule routing_ipassmt)
     apply(simp_all add: correct_routing_def)
  done
end



lemma oiface_rewrite_preserves_nodisc:
  "\<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<not> has_disc disc m \<Longrightarrow> \<not> has_disc disc (oiface_rewrite ipassmt m)"
  proof(induction ipassmt m rule: oiface_rewrite.induct)
  case 2 
    have "\<forall>a. \<not> disc (Dst a) \<Longrightarrow> \<not> disc (OIface ifce) \<Longrightarrow> \<not> has_disc disc (ipassmt_iface_replace_dstip_mexpr ipassmt ifce)"
      for ifce ipassmt
      apply(simp add: ipassmt_iface_replace_dstip_mexpr_def split: option.split)
      apply(intro allI impI, rename_tac ips)
      apply(drule_tac X=Dst and ls="map (uncurry IpAddrNetmask) ips" in match_list_to_match_expr_not_has_disc)
      apply(simp)
      done
    with 2 show ?case by simp
  qed(simp_all)


end