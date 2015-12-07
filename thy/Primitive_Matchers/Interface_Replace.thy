theory Interface_Replace
imports
  No_Spoof
  Common_Primitive_toString
begin

section{*Trying to connect inbound interfaces by their IP ranges*}
subsection{*constraining interfaces*}

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


fun iiface_constrain :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "iiface_constrain _       MatchAny = MatchAny" |
  "iiface_constrain ipassmt (Match (IIface ifce)) = ipassmt_iface_constrain_srcip_mexpr ipassmt ifce" |
  "iiface_constrain ipassmt (Match a) = Match a" |
  "iiface_constrain ipassmt (MatchNot m) = MatchNot (iiface_constrain ipassmt m)" |
  "iiface_constrain ipassmt (MatchAnd m1 m2) = MatchAnd (iiface_constrain ipassmt m1) (iiface_constrain ipassmt m2)"


context
begin
  (*helper1: used in induction case MatchNot*)
  private lemma iiface_constrain_matches_Primitive:
          "matches (common_matcher, \<alpha>) (MatchNot (iiface_constrain ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<longleftrightarrow>
           matches (common_matcher, \<alpha>) (iiface_constrain ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
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
    

  lemma matches_iiface_constrain:
       "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_nowildcards ipassmt \<Longrightarrow>
        (case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)) \<Longrightarrow>
        matches (common_matcher, \<alpha>) (iiface_constrain ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    proof(induction m)
    case MatchAny thus ?case by simp
    next
    case (MatchNot m)
      hence IH: "normalized_nnf_match m \<Longrightarrow> matches (common_matcher, \<alpha>) (iiface_constrain ipassmt m) a p = matches (common_matcher, \<alpha>) m a p" by blast
      with MatchNot.prems IH show ?case by(induction m) (simp_all add: iiface_constrain_matches_Primitive)
    next
    case(Match x) thus ?case
      proof(cases x)
        case (IIface ifce) with Match show ?thesis using matches_ipassmt_iface_constrain_srcip_mexpr_case_Iface by simp
      qed(simp_all)
    next
    case (MatchAnd m1 m2) thus ?case by(simp add: bunch_of_lemmata_about_matches)
    qed
end




subsection{*Sanity checking the assumption*}
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






subsection{*Replacing Interfaces Completely*}
text{*This is a stringer rewriting since it removes the interface completely.
      However, it requires @{const ipassmt_sanity_disjoint}*}

thm ipassmt_sanity_disjoint_def

definition ipassmt_iface_replace_srcip_mexpr :: "ipassignment \<Rightarrow> iface \<Rightarrow> common_primitive match_expr" where
  "ipassmt_iface_replace_srcip_mexpr ipassmt ifce = (case ipassmt ifce of
          None \<Rightarrow> Match (IIface ifce)
        | Some ips \<Rightarrow> (match_list_to_match_expr (map (Match \<circ> Src) (map (\<lambda>(ip, n). (Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) ips)))
        )"


lemma matches_ipassmt_iface_replace_srcip_mexpr: 
    "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow> (case ipassmt ifce of
            None \<Rightarrow> match_iface ifce (p_iiface p)
          | Some ips \<Rightarrow> (*match_iface ifce (p_iiface p) \<and>*) p_src p \<in> ipv4cidr_union_set (set ips)
          )"
proof(cases "ipassmt ifce")
case None thus ?thesis by(simp add: ipassmt_iface_replace_srcip_mexpr_def match_simplematcher_Iface)
next
case (Some ips)
  have "matches (common_matcher, \<alpha>) (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) ips)) a p \<longleftrightarrow>
       (\<exists>m\<in>set ips. p_src p \<in> (case m of (ip, y) \<Rightarrow> ipv4range_set_from_bitmask ip y))" 
       by(simp add: match_list_to_match_expr_disjunction[symmetric] match_list_matches match_simplematcher_SrcDst ipv4s_to_set_Ip4AddrNetmask_case)
  with Some show ?thesis
    apply(simp add: ipassmt_iface_replace_srcip_mexpr_def bunch_of_lemmata_about_matches(1))
    apply(simp add: match_simplematcher_Iface ipv4cidr_union_set_def)
    done
qed


fun iiface_rewrite :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "iiface_rewrite _       MatchAny = MatchAny" |
  "iiface_rewrite ipassmt (Match (IIface ifce)) = ipassmt_iface_replace_srcip_mexpr ipassmt ifce" |
  "iiface_rewrite ipassmt (Match a) = Match a" |
  "iiface_rewrite ipassmt (MatchNot m) = MatchNot (iiface_rewrite ipassmt m)" |
  "iiface_rewrite ipassmt (MatchAnd m1 m2) = MatchAnd (iiface_rewrite ipassmt m1) (iiface_rewrite ipassmt m2)"


context
begin
  (*helper1: used in induction case MatchNot*)
  private lemma iiface_rewrite_matches_Primitive:
          "matches (common_matcher, \<alpha>) (MatchNot (iiface_rewrite ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<longleftrightarrow>
           matches (common_matcher, \<alpha>) (iiface_rewrite ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
  proof(cases x)
  case (IIface ifce)
    have "(matches (common_matcher, \<alpha>) (MatchNot (ipassmt_iface_replace_srcip_mexpr ipassmt ifce)) a p = (\<not> match_iface ifce (p_iiface p))) \<longleftrightarrow>
      (matches (common_matcher, \<alpha>) (ipassmt_iface_replace_srcip_mexpr ipassmt ifce) a p = match_iface ifce (p_iiface p))"
    proof(cases "ipassmt ifce")
    case None thus ?thesis
       apply(simp add: matches_ipassmt_iface_replace_srcip_mexpr)
       apply(simp add: ipassmt_iface_replace_srcip_mexpr_def match_simplematcher_Iface_not)
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
         apply(simp add: matches_ipassmt_iface_replace_srcip_mexpr)
         apply(simp add: ipassmt_iface_replace_srcip_mexpr_def match_simplematcher_Iface_not)
         apply(simp add: helper)
         done
     qed
     with IIface show ?thesis by(simp add: match_simplematcher_Iface_not match_simplematcher_Iface)
  qed(simp_all)


  (*helper2: used in induction base case*)
  private lemma matches_ipassmt_iface_replace_srcip_mexpr_case_Iface:
        fixes ifce::iface
        assumes "ipassmt_sanity_nowildcards ipassmt"
            and "ipassmt_sanity_disjoint ipassmt"
            and "ipassmt (Iface (p_iiface p)) = Some p_ips \<and> p_src p \<in> ipv4cidr_union_set (set p_ips)"
        shows   "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow>
                 matches (common_matcher, \<alpha>) (Match (IIface ifce)) a p"
  proof -
    have "matches (common_matcher, \<alpha>) (ipassmt_iface_replace_srcip_mexpr ipassmt ifce) a p = match_iface ifce (p_iiface p)"
      proof -
        show ?thesis
        proof(cases "ipassmt ifce")
          case None thus ?thesis by(simp add: matches_ipassmt_iface_replace_srcip_mexpr)
          next
          case (Some y) with assms(2) have "p_src p \<in> ipv4cidr_union_set (set y) = match_iface ifce (p_iiface p)"
            using assms(1) assms(3) ipassmt_disjoint_matcheq_iifce_srcip by blast
            with Some show ?thesis by(simp add: matches_ipassmt_iface_replace_srcip_mexpr)
        qed
    qed
    thus ?thesis by(simp add: match_simplematcher_Iface)
  qed



  lemma matches_iiface_rewrite:
       "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_nowildcards ipassmt \<Longrightarrow> ipassmt_sanity_disjoint ipassmt \<Longrightarrow>
        (\<exists>p_ips. ipassmt (Iface (p_iiface p)) = Some p_ips \<and> p_src p \<in> ipv4cidr_union_set (set p_ips)) \<Longrightarrow>
        matches (common_matcher, \<alpha>) (iiface_rewrite ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    proof(induction m)
    case MatchAny thus ?case by simp
    next
    case (MatchNot m)
      hence IH: "normalized_nnf_match m \<Longrightarrow>
        matches (common_matcher, \<alpha>) (iiface_rewrite ipassmt m) a p =matches (common_matcher, \<alpha>) m a p" by blast
      with MatchNot.prems IH show ?case by(induction m) (simp_all add: iiface_rewrite_matches_Primitive)
    next
    case(Match x) thus ?case
      proof(cases x)
        case (IIface ifce) with Match show ?thesis
        apply(cases "ipassmt (Iface (p_iiface p))")
         prefer 2
          apply(simp add: matches_ipassmt_iface_replace_srcip_mexpr_case_Iface; fail)
        by auto
      qed(simp_all)
    next
    case (MatchAnd m1 m2) thus ?case by(simp add: bunch_of_lemmata_about_matches)
    qed

end

  text{*Finally, we show that @{const ipassmt_sanity_disjoint} is really needed.*}
  lemma iface_replace_needs_ipassmt_disjoint:
    assumes "ipassmt_sanity_nowildcards ipassmt"
    and iface_replace: "\<And> ifce p::simple_packet.
          (matches (common_matcher, \<alpha>) (ipassmt_iface_replace_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) (Match (IIface ifce)) a p)" 
    shows "ipassmt_sanity_disjoint ipassmt"
  unfolding ipassmt_sanity_disjoint_def
  proof(intro ballI impI)
    fix i1 i2
    assume "i1 \<in> dom ipassmt" and "i2 \<in> dom ipassmt" and "i1 \<noteq> i2"
    from `i1 \<in> dom ipassmt` obtain i1_ips where i1_ips: "ipassmt i1 = Some i1_ips" by blast
    from `i2 \<in> dom ipassmt` obtain i2_ips where i2_ips: "ipassmt i2 = Some i2_ips" by blast

    { fix p::simple_packet
      from iface_replace[of  i1 "p\<lparr> p_iiface := iface_sel i2\<rparr>"] have
        "(p_src p \<in> ipv4cidr_union_set (set i2_ips) \<Longrightarrow> (p_src p \<in> ipv4cidr_union_set (set i1_ips)) = match_iface i1 (iface_sel i2))"
      apply(simp add: match_simplematcher_Iface  `i1 \<in> dom ipassmt`)
      apply(simp add: matches_ipassmt_iface_replace_srcip_mexpr i1_ips)
      done
      with `i1 \<noteq> i2` have "\<not> (p_src p \<in> ipv4cidr_union_set (set i2_ips) \<and> (p_src p \<in> ipv4cidr_union_set (set i1_ips)))"
        by (metis `i1 \<in> dom ipassmt` assms(1) iface.exhaust_sel iface_is_wildcard_def ipassmt_sanity_nowildcards_def match_iface_case_nowildcard) 
    }
    hence "\<And>src. \<not> (src \<in> ipv4cidr_union_set (set i2_ips) \<and> (src \<in> ipv4cidr_union_set (set i1_ips)))"
      by (metis select_convs(3)) 

    thus "ipv4cidr_union_set (set (the (ipassmt i1))) \<inter> ipv4cidr_union_set (set (the (ipassmt i2))) = {}"
      apply(simp add: i1_ips i2_ips)
      by blast
  qed


text{*In @{file "Transform.thy"} there should be the convenience function @{text "iface_try_rewrite"}*}


(*TODO: optimize interfaces, e.g. eth+ MatchAnd wifi+ is false!*)
(*
definition try_interface_replaceby_srcip :: "ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> common_primitive rule list" where
  "try_interface_replaceby_srcip ipassmt \<equiv> 
    if ipassmt_sanity_disjoint ipassmt
    then optimize_matches (iiface_rewrite ipassmt)
    else if ipassmt_sanity_disjoint (ipassmt_ignore_wildcard ipassmt)
    then optimize_matches (iiface_constrain ipassmt) \<circ> normalize_rules_dnf \<circ> optimize_matches (iiface_rewrite (ipassmt_ignore_wildcard ipassmt))
    else optimize_matches (iiface_constrain ipassmt)"

(* problem: after iiface_rewrite, mexpr no longer nnf normalized.
   it would be possible to avoid normalize_rules_dnf or normalize_match call and the list in the result type*)
*)


(*TODO move to separate files*)
  (*TODO a generic primitive optimization function and a separate file for such things*)

  (*returns: (one positive interface \<times> a list of negated interfaces)
    it matches the conjunction of both
    None if the expression cannot match*)
  definition compress_interfaces :: "iface negation_type list \<Rightarrow> (iface \<times> iface list) option" where
    "compress_interfaces ifces \<equiv> case (compress_pos_interfaces (getPos ifces))
        of None \<Rightarrow> None
        |  Some i \<Rightarrow> if \<exists>negated_ifce \<in> set (getNeg ifces). iface_subset i negated_ifce then None else Some (i, getNeg ifces)"

term map_option
term option_map (*l4v*)

  lemma compress_interfaces_None: "compress_interfaces ifces = None \<Longrightarrow> \<not> matches (common_matcher, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
    apply(simp add: compress_interfaces_def)
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Iface match_simplematcher_Iface_not)
    apply(case_tac "compress_pos_interfaces (getPos ifces)")
     apply(simp_all)
     apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_None)
     apply(simp; fail)
    apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
    apply(simp split:split_if_asm)
    using iface_subset by blast

  lemma compress_interfaces_Some: "compress_interfaces ifces = Some (i_pos, i_neg) \<Longrightarrow>
    matches (common_matcher, \<alpha>) (MatchAnd (Match (IIface i_pos)) (alist_and (NegPos_map IIface (map Neg i_neg)))) a p \<longleftrightarrow>
    matches (common_matcher, \<alpha>) (alist_and (NegPos_map IIface ifces)) a p"
    apply(simp add: compress_interfaces_def)
    apply(simp add: bunch_of_lemmata_about_matches(1))
    apply(simp add: nt_match_list_matches[symmetric] nt_match_list_simp)
    apply(simp add: NegPos_map_simps match_simplematcher_Iface match_simplematcher_Iface_not)
    apply(case_tac "compress_pos_interfaces (getPos ifces)")
     apply(simp_all)
    apply(drule_tac p_i="p_iiface p" in compress_pos_interfaces_Some)
    apply(simp split:split_if_asm)
    done

  
  definition compress_normalize_interfaces :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr option" where 
    "compress_normalize_interfaces m = (case primitive_extractor (is_Iiface, iiface_sel) m  of (ifces, rst) \<Rightarrow>
      (map_option (\<lambda>(i_pos, i_neg). MatchAnd
                                    (alist_and (NegPos_map IIface ((if i_pos = ifaceAny then [] else [Pos i_pos])@(map Neg i_neg))))
                                    rst
                  ) (compress_interfaces ifces)))"

  lemma compress_normalize_interfaces_Some:
  assumes "normalized_nnf_match m" and "compress_normalize_interfaces m = Some m'"
    shows "matches (common_matcher, \<alpha>) m' a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
    using assms(2)
    apply(simp add: compress_normalize_interfaces_def)
    apply(case_tac "primitive_extractor (is_Iiface, iiface_sel) m")
    apply(rename_tac ifces rst, simp)
    apply(drule primitive_extractor_correct(1)[OF assms(1) wf_disc_sel_common_primitive(5), where \<gamma>="(common_matcher, \<alpha>)" and a=a and p=p])
    apply(case_tac "compress_interfaces ifces")
     apply(simp add: compress_interfaces_None bunch_of_lemmata_about_matches; fail)
    apply(rename_tac aaa, case_tac aaa, simp)
    apply(drule compress_interfaces_Some[where \<alpha>=\<alpha> and a=a and p=p])
    apply (simp split:split_if_asm)
     apply(meson bunch_of_lemmata_about_matches(1) match_ifaceAny match_simplematcher_Iface(1))
    by (meson bunch_of_lemmata_about_matches(1))

  lemma compress_normalize_interfaces_None:
  assumes "normalized_nnf_match m" and "compress_normalize_interfaces m = None"
    shows "\<not> matches (common_matcher, \<alpha>) m a p"
    using assms(2)
    apply(simp add: compress_normalize_interfaces_def)
    apply(case_tac "primitive_extractor (is_Iiface, iiface_sel) m")
    apply(rename_tac ifces rst, simp)
    apply(drule primitive_extractor_correct(1)[OF assms(1) wf_disc_sel_common_primitive(5), where \<gamma>="(common_matcher, \<alpha>)" and a=a and p=p])
    apply(case_tac "compress_interfaces ifces")
     apply(simp add: compress_interfaces_None bunch_of_lemmata_about_matches; fail)
    apply(rename_tac aaa, case_tac aaa, simp)
    done


  lemma compress_normalize_interfaces_nnf: "normalized_nnf_match m \<Longrightarrow> compress_normalize_interfaces m = Some m' \<Longrightarrow>
    normalized_nnf_match m'"
    apply(case_tac "primitive_extractor (is_Iiface, iiface_sel) m")
    apply(simp add: compress_normalize_interfaces_def)
    apply(clarify)
    apply (simp add: normalized_nnf_match_alist_and)
    using primitive_extractor_correct(2) wf_disc_sel_common_primitive(5) by blast
    
  
  lemma compress_normalize_interfaces_not_introduces_Iiface:
    assumes notdisc: "\<not> has_disc is_Iiface m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "\<not> has_disc is_Iiface m'"
   proof -
        obtain as ms where asms: "primitive_extractor (is_Iiface, iiface_sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(4)[OF nm wf_disc_sel_common_primitive(5) asms] have 1: "\<not> has_disc is_Iiface ms" by simp
        from notdisc primitive_extractor_correct(7)[OF nm wf_disc_sel_common_primitive(5) asms] have 2: "as = [] \<and> ms = m" by simp
        { fix i_pos is_neg
          assume c: "compress_interfaces [] = Some (i_pos, is_neg)"
          from c have "i_pos = ifaceAny \<and> is_neg = []" by(simp add: compress_interfaces_def)
        } note compress_interfaces_Nil=this
        from 1 2 some show ?thesis
          by(auto simp add: compress_normalize_interfaces_def asms dest: compress_interfaces_Nil split: split_if_asm)[1]
   qed

  lemma compress_normalize_interfaces_not_introduces_Iiface_negated:
    assumes notdisc: "\<not> has_disc_negated is_Iiface False m"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "\<not> has_disc_negated is_Iiface False m'"
   proof -
        obtain as ms where asms: "primitive_extractor (is_Iiface, iiface_sel) m = (as, ms)" by fastforce
        from notdisc primitive_extractor_correct(6)[OF nm wf_disc_sel_common_primitive(5) asms] have 1: "\<not> has_disc_negated is_Iiface False ms" by simp
        from asms notdisc has_disc_negated_primitive_extractor[OF nm, where disc=is_Iiface and sel=iiface_sel] have
          "\<forall>a. Neg a \<notin> set as" by(simp)
        hence "getNeg as = []" by (meson NegPos_set(5) image_subset_iff last_in_set) 
        { fix i_pos is_neg
          assume "compress_interfaces as = Some (i_pos, is_neg)"
          with `getNeg as = []` have "is_neg = []"
          by(simp add: compress_interfaces_def split: option.split_asm)
        } note compress_interfaces_noNeg=this
        from 1 some show ?thesis
          by(auto simp add: compress_normalize_interfaces_def asms dest: compress_interfaces_noNeg split: split_if_asm)
   qed


(*TODO: move*)
lemma has_disc_alist_and: "has_disc disc (alist_and as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc disc (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)
lemma has_disc_negated_alist_and: "has_disc_negated disc neg (alist_and as) \<longleftrightarrow> (\<exists> a \<in> set as. has_disc_negated disc neg (negation_type_to_match_expr a))"
  proof(induction as rule: alist_and.induct)
  qed(simp_all add: negation_type_to_match_expr_simps)


(*TODO: move*)
lemma normalized_n_primitive_alist_and: "normalized_n_primitive disc_sel P (alist_and as) \<longleftrightarrow>
      (\<forall> a \<in> set as. normalized_n_primitive disc_sel P (negation_type_to_match_expr a))"
  proof(induction as)
  case Nil thus ?case by simp
  next
  case (Cons a as) thus ?case
    apply(cases disc_sel, cases a)
    by(simp_all add: negation_type_to_match_expr_simps)
  qed

(*TODO: move*)
lemma NegPos_map_map_Neg: "NegPos_map C (map Neg as) = map Neg (map C as)"
  by(induction as) (simp_all)
lemma NegPos_map_map_Pos: "NegPos_map C (map Pos as) = map Pos (map C as)"
  by(induction as) (simp_all)

  (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_interfaces_hasdisc:
    assumes am: "\<not> has_disc disc m"
        and disc: "(\<forall>a. \<not> disc (IIface a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc disc m'"
   proof -
        from compress_normalize_interfaces_nnf[OF nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (is_Iiface, iiface_sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(4)[OF nm wf_disc_sel_common_primitive(5) asms] have 1: "\<not> has_disc disc ms" by simp
        { fix i_pos is_neg
          from disc have "\<not> has_disc disc (alist_and (NegPos_map IIface ((if i_pos = ifaceAny then [] else [Pos i_pos]) @ map Neg is_neg)))"
            by(simp add: has_disc_alist_and negation_type_to_match_expr_simps NegPos_map_map_Neg)
        }
        with some have "\<not> has_disc disc m'"
          apply(simp add: compress_normalize_interfaces_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed  (* only for arbitrary discs that do not match Iiface*)
  lemma compress_normalize_interfaces_hasdisc_negated:
    assumes am: "\<not> has_disc_negated disc neg m"
        and disc: "(\<forall>a. \<not> disc (IIface a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "normalized_nnf_match m' \<and> \<not> has_disc_negated disc neg m'"
   proof -
        from compress_normalize_interfaces_nnf[OF nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (is_Iiface, iiface_sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct(6)[OF nm wf_disc_sel_common_primitive(5) asms] have 1: "\<not> has_disc_negated disc neg ms" by simp
        { fix i_pos is_neg
          from disc have "\<not> has_disc_negated disc neg (alist_and (NegPos_map IIface ((if i_pos = ifaceAny then [] else [Pos i_pos]) @ map Neg is_neg)))"
            by(simp add: has_disc_negated_alist_and negation_type_to_match_expr_simps NegPos_map_map_Neg)
        }
        with some have "\<not> has_disc_negated disc neg m'"
          apply(simp add: compress_normalize_interfaces_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed


  thm normalize_primitive_extract_preserves_unrelated_normalized_n_primitive (*is similar*)
  lemma compress_normalize_interfaces_preserves_normalized_n_primitive:
    assumes am: "normalized_n_primitive (disc, sel) P m"
        and disc: "(\<forall>a. \<not> disc (IIface a))"
        and nm: "normalized_nnf_match m"
        and some: "compress_normalize_interfaces m = Some m'"
     shows "normalized_nnf_match m' \<and> normalized_n_primitive (disc, sel) P m'"
   proof -
        from compress_normalize_interfaces_nnf[OF nm some] have goal1: "normalized_nnf_match m'" .
        obtain as ms where asms: "primitive_extractor (is_Iiface, iiface_sel) m = (as, ms)" by fastforce
        from am primitive_extractor_correct[OF nm wf_disc_sel_common_primitive(5) asms] have 1: "normalized_n_primitive (disc, sel) P ms" by fast
        { fix i_pos is_neg
          from disc have "normalized_n_primitive (disc, sel) P (alist_and (NegPos_map IIface ((if i_pos = ifaceAny then [] else [Pos i_pos]) @ map Neg is_neg)))"
            apply(simp add: has_disc_alist_and negation_type_to_match_expr_simps NegPos_map_map_Neg)
            apply(induction is_neg)
             apply(simp_all)
            done
        }
        with some have "normalized_n_primitive (disc, sel) P m'"
          apply(simp add: compress_normalize_interfaces_def asms)
          apply(elim exE conjE)
          using 1 by force
        with goal1 show ?thesis by simp
   qed
  

  value[code] "compress_normalize_interfaces 
    (MatchAnd (MatchAnd (MatchAnd (Match (IIface (Iface ''eth+''))) (MatchNot (Match (IIface (Iface ''eth4''))))) (Match (IIface (Iface ''eth1''))))
              (Match (Prot (Proto TCP))))"
    
  value[code] "compress_normalize_interfaces MatchAny"
    

end