theory Interface_Replace
imports
  No_Spoof
  Common_Primitive_toString
begin

section{*Abstracting over Primitives*}

definition ipassmt_iface_constrain_srcip_mexpr :: "ipassignment \<Rightarrow> iface \<Rightarrow> common_primitive match_expr" where
  "ipassmt_iface_constrain_srcip_mexpr ipassmt ifce = (case ipassmt ifce of
          None \<Rightarrow> Match (IIface ifce)
        | Some ips \<Rightarrow> MatchAnd
            (Match (IIface ifce))
            (match_list_to_match_expr (map (Match \<circ> Src) (map (\<lambda>(ip, n). (Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) ips)))
        )"

lemma ipv4s_to_set_Ip4AddrNetmask_case: "ipv4s_to_set (case x of (ip, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) x) =
       (case x of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa)"
  by(cases x) (simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)


lemma matches_ipassmt_iface_constrain_srcip_mexpr: 
    "matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow> (case ipassmt ifce of
            None \<Rightarrow> match_iface ifce (p_iiface p)
          | Some ips \<Rightarrow> match_iface ifce (p_iiface p) \<and> p_src p \<in> ipv4cidr_union_set (set ips)
          )"
proof(cases "ipassmt ifce")
case None thus ?thesis by(simp add: ipassmt_iface_constrain_srcip_mexpr_def match_simplematcher_Iface; fail)
next
case (Some ips)
  have "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) ips)) a p \<longleftrightarrow>
       (\<exists>m\<in>set ips. p_src p \<in> (case m of (ip, y) \<Rightarrow> ipv4range_set_from_bitmask ip y))" 
       by(simp add: match_list_to_match_expr_disjunction[symmetric] match_list_matches match_simplematcher_SrcDst ipv4s_to_set_Ip4AddrNetmask_case)
  with Some show ?thesis
    apply(simp add: ipassmt_iface_constrain_srcip_mexpr_def bunch_of_lemmata_about_matches(1))
    apply(simp add: match_simplematcher_Iface ipv4cidr_union_set_def)
    done
qed


(*TODO: rename to constrain_iiface*)
fun rewrite_iiface :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "rewrite_iiface _       MatchAny = MatchAny" |
  "rewrite_iiface ipassmt (Match (IIface ifce)) = ipassmt_iface_constrain_srcip_mexpr ipassmt ifce" |
  "rewrite_iiface ipassmt (Match a) = Match a" |
  "rewrite_iiface ipassmt (MatchNot m) = MatchNot (rewrite_iiface ipassmt m)" |
  "rewrite_iiface ipassmt (MatchAnd m1 m2) = MatchAnd (rewrite_iiface ipassmt m1) (rewrite_iiface ipassmt m2)"


context
begin
  (*helper1: used in induction case MatchNot*)
  private lemma rewrite_iiface_matches_Primitive:
          "matches (common_matcher, \<alpha>) (MatchNot (rewrite_iiface ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<longleftrightarrow>
           matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
  proof(cases x)
  case (IIface ifce)
    have "(matches (common_matcher, \<alpha>) (MatchNot (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce)) a p = (\<not> match_iface ifce (p_iiface p))) \<longleftrightarrow>
      (matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce) a p = match_iface ifce (p_iiface p))"
    proof(cases "ipassmt ifce")
    case None thus ?thesis
       apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
       apply(simp add: ipassmt_iface_constrain_srcip_mexpr_def match_simplematcher_Iface_not)
       done
     next
     case (Some ips)
       {  fix ips
          have "matches (common_matcher, \<alpha>)
                 (MatchNot (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) ips))) a p \<longleftrightarrow>
                 (p_src p \<notin> ipv4cidr_union_set (set ips))"
        apply(induction ips)
         apply(simp add: bunch_of_lemmata_about_matches ipv4cidr_union_set_def)
        apply(simp add: MatchOr_MatchNot)
        apply(simp add: ipv4cidr_union_set_def)
        apply(simp add: match_simplematcher_SrcDst_not)
        apply(thin_tac _)
        apply(simp add: ipv4s_to_set_Ip4AddrNetmask_case)
        done
       } note helper=this
       from Some show ?thesis
         apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
         apply(simp add: ipassmt_iface_constrain_srcip_mexpr_def match_simplematcher_Iface_not)
         apply(simp add: matches_DeMorgan)
         apply(simp add: helper)
         apply(simp add: match_simplematcher_Iface_not)
         by blast
     qed
     with IIface show ?thesis by(simp add: match_simplematcher_Iface_not match_simplematcher_Iface)
  qed(simp_all)
  
  
  (*helper2: used in induction base case*)
  private lemma matches_ipassmt_iface_constrain_srcip_mexpr_case_Iface:
        fixes ifce::iface
        assumes "ipassmt_sanity_nowildcards ipassmt" and "case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)"
        shows   "matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow>
                 matches (common_matcher, \<alpha>) (Match (IIface ifce)) a p"
  proof -
    have "matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce) a p = match_iface ifce (p_iiface p)"
      proof(cases "ipassmt (Iface (p_iiface p))")
      case None
      from None show ?thesis
        proof(cases "ipassmt ifce")
          case None thus ?thesis by(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
          next
          case (Some a)
           from assms(1) have "\<not> match_iface ifce (p_iiface p)"
           apply(rule ipassmt_sanity_nowildcards_match_iface)
            by(simp_all add: Some None)
          with Some show ?thesis by(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
        qed
      next
      case (Some x)
        with assms(2) have assms2: "p_src p \<in> ipv4cidr_union_set (set x)" by(simp) (*unused*)
        show ?thesis
        proof(cases "ipassmt ifce")
          case None thus ?thesis by(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
          next
          case (Some y) with assms(2) have "(match_iface ifce (p_iiface p) \<and> p_src p \<in> ipv4cidr_union_set (set y)) = match_iface ifce (p_iiface p)"
            apply(cases ifce)
            apply(rename_tac ifce_str)
            apply(case_tac "ifce_str = (p_iiface p)")
             apply (simp add: match_iface_refl; fail)
            apply(simp)
            apply(subgoal_tac "\<not> match_iface (Iface ifce_str) (p_iiface p)")
             apply(simp)
            using assms(1) by (metis domI iface.sel iface_is_wildcard_def ipassmt_sanity_nowildcards_def match_iface_case_nowildcard)
            with Some show ?thesis by(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
        qed
    qed
    thus ?thesis by(simp add: match_simplematcher_Iface)
  qed
    

  lemma matches_rewrite_iiface:
       "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_nowildcards ipassmt \<Longrightarrow>
        (case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)) \<Longrightarrow>
        matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    proof(induction m)
    case MatchAny thus ?case by simp
    next
    case (MatchNot m)
      hence IH: "normalized_nnf_match m \<Longrightarrow> matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p = matches (common_matcher, \<alpha>) m a p" by blast
      with MatchNot.prems IH show ?case by(induction m) (simp_all add: rewrite_iiface_matches_Primitive)
    next
    case(Match x) thus ?case
      proof(cases x)
        case (IIface ifce) with Match show ?thesis using matches_ipassmt_iface_constrain_srcip_mexpr_case_Iface by simp
      qed(simp_all)
    next
    case (MatchAnd m1 m2) thus ?case by(simp add: bunch_of_lemmata_about_matches)
    qed
end


(*TODO: we need a good formulation of the assumption. the case stuff is so undefined fo the None case \<dots>
        EX-quantor is too strong
        Also holds if EX replaced by ALL*)
lemma "(\<exists>ips. ipassmt (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipv4cidr_union_set (set ips)) \<Longrightarrow>
       (case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips))"
  apply(cases "ipassmt (Iface (p_iiface p))")
   apply(simp_all)
  done



text{*Sanity check:
      If we assume that there are no spoofed packets, spoofing protection is trivially fulfilled.*}
lemma "\<forall> p::simple_packet. Iface (p_iiface p) \<in> dom ipassmt \<longrightarrow> p_src p \<in> ipv4cidr_union_set (set (the (ipassmt (Iface (p_iiface p))))) \<Longrightarrow> no_spoofing ipassmt rs"
  apply(simp add: no_spoofing_def)
  apply(clarify)
  apply(rename_tac iface ips p)
  apply(thin_tac "_,_\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow") (*not needed*)
  apply(erule_tac x="p\<lparr>p_iiface := iface_sel iface\<rparr>" in allE)
  apply(auto)
  done

text{*Sanity check:
      If the firewall features spoofing protection and we look at a packet which was allowed by the firewall.
      Then the packet's src ip must be according to ipassmt. (case Some)
      We don't case about packets from an interface which are not defined in ipassmt. (case None)*}
lemma "no_spoofing ipassmt rs \<Longrightarrow> (common_matcher, in_doubt_allow),p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow \<Longrightarrow>
       case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips) | None \<Rightarrow> True"
  apply(simp add: no_spoofing_def)
  apply(case_tac "Iface (p_iiface p) \<in> dom ipassmt")
   apply(erule_tac x="Iface (p_iiface p)" in ballE)
    apply(simp_all)
   apply(erule_tac x="p" in allE)
   apply(simp)
   apply fastforce
  by (simp add: case_option_dom)






(**********scratch: getting completely rid of iifaces****)
thm ipassmt_sanity_disjoint_def

definition ipassmt_iface_constrain_srcip_mexpr2 :: "ipassignment \<Rightarrow> iface \<Rightarrow> common_primitive match_expr" where
  "ipassmt_iface_constrain_srcip_mexpr2 ipassmt ifce = (case ipassmt ifce of
          None \<Rightarrow> Match (IIface ifce)
        | Some ips \<Rightarrow> (match_list_to_match_expr (map (Match \<circ> Src) (map (\<lambda>(ip, n). (Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) ips)))
        )"


lemma matches_ipassmt_iface_constrain_srcip_mexpr2: 
    "matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr2 ipassmt ifce) a p \<longleftrightarrow> (case ipassmt ifce of
            None \<Rightarrow> match_iface ifce (p_iiface p)
          | Some ips \<Rightarrow> (*match_iface ifce (p_iiface p) \<and>*) p_src p \<in> ipv4cidr_union_set (set ips)
          )"
proof(cases "ipassmt ifce")
case None thus ?thesis by(simp add: ipassmt_iface_constrain_srcip_mexpr2_def match_simplematcher_Iface)
next
case (Some ips)
  have "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) ips)) a p \<longleftrightarrow>
       (\<exists>m\<in>set ips. p_src p \<in> (case m of (ip, y) \<Rightarrow> ipv4range_set_from_bitmask ip y))" 
       by(simp add: match_list_to_match_expr_disjunction[symmetric] match_list_matches match_simplematcher_SrcDst ipv4s_to_set_Ip4AddrNetmask_case)
  with Some show ?thesis
    apply(simp add: ipassmt_iface_constrain_srcip_mexpr2_def bunch_of_lemmata_about_matches(1))
    apply(simp add: match_simplematcher_Iface ipv4cidr_union_set_def)
    done
qed
  

fun rewrite2_iiface :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "rewrite2_iiface _       MatchAny = MatchAny" |
  "rewrite2_iiface ipassmt (Match (IIface ifce)) = ipassmt_iface_constrain_srcip_mexpr2 ipassmt ifce" |
  "rewrite2_iiface ipassmt (Match a) = Match a" |
  "rewrite2_iiface ipassmt (MatchNot m) = MatchNot (rewrite_iiface ipassmt m)" |
  "rewrite2_iiface ipassmt (MatchAnd m1 m2) = MatchAnd (rewrite_iiface ipassmt m1) (rewrite_iiface ipassmt m2)"


context
begin
  (*helper1: used in induction case MatchNot*)
  private lemma rewrite2_iiface_matches_Primitive:
          "matches (common_matcher, \<alpha>) (MatchNot (rewrite2_iiface ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<longleftrightarrow>
           matches (common_matcher, \<alpha>) (rewrite2_iiface ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
  proof(cases x)
  case (IIface ifce)
    have "(matches (common_matcher, \<alpha>) (MatchNot (ipassmt_iface_constrain_srcip_mexpr2 ipassmt ifce)) a p = (\<not> match_iface ifce (p_iiface p))) \<longleftrightarrow>
      (matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr2 ipassmt ifce) a p = match_iface ifce (p_iiface p))"
    proof(cases "ipassmt ifce")
    case None thus ?thesis
       apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr2)
       apply(simp add: ipassmt_iface_constrain_srcip_mexpr2_def match_simplematcher_Iface_not)
       done
     next
     case (Some ips)
       {  fix ips
          have "matches (common_matcher, \<alpha>)
                 (MatchNot (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) ips))) a p \<longleftrightarrow>
                 (p_src p \<notin> ipv4cidr_union_set (set ips))"
        apply(induction ips)
         apply(simp add: bunch_of_lemmata_about_matches ipv4cidr_union_set_def)
        apply(simp add: MatchOr_MatchNot)
        apply(simp add: ipv4cidr_union_set_def)
        apply(simp add: match_simplematcher_SrcDst_not)
        apply(thin_tac _)
        apply(simp add: ipv4s_to_set_Ip4AddrNetmask_case)
        done
       } note helper=this
       from Some show ?thesis
         apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr2)
         apply(simp add: ipassmt_iface_constrain_srcip_mexpr2_def match_simplematcher_Iface_not)
         apply(simp add: helper)
         done
     qed
     with IIface show ?thesis by(simp add: match_simplematcher_Iface_not match_simplematcher_Iface)
  qed(simp_all)


  (*TODO: move to nospoof*)
  (*TODO: could also work when we ignore UNIVs in the ipassmt?*)
  lemma assumes "ipassmt_sanity_nowildcards ipassmt" and "case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)"
            and disjoint: "ipassmt_sanity_disjoint ipassmt" and "ipassmt ifce = Some ips" and complete: "(\<Union>(ipv4cidr_union_set ` set ` (ran ipassmt))) = UNIV"
        shows   "match_iface ifce (p_iiface p) \<longleftrightarrow> p_src p \<in> ipv4cidr_union_set (set ips)"
    proof
     assume "match_iface ifce (p_iiface p)"
     thus "p_src p \<in> ipv4cidr_union_set (set ips)"
     (*TODO: probably case distinction ifce = p_iiface?*)
     using assms(1) assms(2) assms(4)
     apply (metis (no_types, lifting) WordLemmaBucket.insert_dom case_optionE iface.sel iface_is_wildcard_def insertI1 ipassmt_sanity_nowildcards_def ipassmt_sanity_nowildcards_match_iface match_iface.elims(2) match_iface_case_nowildcard option.sel) 
     done
   next
     assume a: "p_src p \<in> ipv4cidr_union_set (set ips)"
     (*reverse ipassmt lookup requires ipassmt to cover the UNIV*)

     --{*basically, we need to reverse the map @{term ipassmt}*}

     have ipassmt_inj: "\<forall>k. ipassmt k = Some ips \<longrightarrow> k = ifce"
     proof(rule ccontr, simp)
       assume "\<exists>k. ipassmt k = Some ips \<and> k \<noteq> ifce"
       with this obtain k where k: "ipassmt k = Some ips" and "k \<noteq> ifce" by blast
       with assms(4) disjoint have "ipv4cidr_union_set (set (the (ipassmt k))) \<inter> ipv4cidr_union_set (set (the (ipassmt ifce))) = {}"
         apply(simp add: ipassmt_sanity_disjoint_def)
         by fastforce
       thus False using a assms(4) k by auto 
     qed

     have ipassmt_inj_p: "\<forall>ips'. p_src p \<in> ipv4cidr_union_set (set ips') \<and> (\<exists>k. ipassmt k = Some ips') \<longrightarrow> ips' = ips"
       apply(clarify)
       apply(rename_tac ips' k)
       apply(subgoal_tac "k = ifce")
        using assms(4) apply simp
       (*this*)
      sorry

     have "ipassmt (Iface (p_iiface p)) \<noteq> None" sorry (*needs assm*)
     from this obtain ips' where "ipassmt (Iface (p_iiface p)) = Some ips'" by blast
     with assms(2) have "p_src p \<in> ipv4cidr_union_set (set ips')" by simp
     hence "(Iface (p_iiface p)) = ifce"
       using ipassmt_inj_p `ipassmt (Iface (p_iiface p)) = Some ips'` ipassmt_inj by blast 

     thus "match_iface ifce (p_iiface p)" using match_iface_refl by blast 
   oops
   


end