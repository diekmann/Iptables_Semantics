theory Interface_Replace
imports
  No_Spoof (*TODO imports boolean semantics, get rid of!*)
  Common_Primitive_toString
  Transform
begin

section{*Abstracting over Primitives*}

term fold

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
  apply(simp split: option.split add: ipassmt_iface_constrain_srcip_mexpr_def)
  apply(intro conjI allI)
   apply(simp add: match_simplematcher_Iface; fail)
   apply(simp add: bunch_of_lemmata_about_matches(1))
  apply(simp add: match_list_to_match_expr_disjunction[symmetric] match_list_matches ipv4cidr_union_set_def)
  apply(simp add: match_simplematcher_SrcDst ipv4s_to_set_Ip4AddrNetmask_case match_simplematcher_Iface)
  done
  

fun rewrite_iiface :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "rewrite_iiface _       MatchAny = MatchAny" |
  "rewrite_iiface ipassmt (Match (IIface ifce)) = ipassmt_iface_constrain_srcip_mexpr ipassmt ifce" |
  "rewrite_iiface ipassmt (Match a) = Match a" |
  "rewrite_iiface ipassmt (MatchNot m) = MatchNot (rewrite_iiface ipassmt m)" |
  "rewrite_iiface ipassmt (MatchAnd m1 m2) = MatchAnd (rewrite_iiface ipassmt m1) (rewrite_iiface ipassmt m2)"


lemma ternary_ternary_eval_match_list_to_match_expr_not_unknown:
      "ternary_ternary_eval (map_match_tac common_matcher p (match_list_to_match_expr (map (Match \<circ> Src) ips))) \<noteq>
           TernaryUnknown"
apply(induction ips)
 apply(simp)
apply(simp)
by (metis bool_to_ternary_simps(2) bool_to_ternary_simps(4) eval_ternary_And_comm eval_ternary_Not.simps(1) eval_ternary_Not_UnknownD eval_ternary_idempotence_Not eval_ternary_simps_simple(2) eval_ternary_simps_simple(4))


lemma ipassmt_iface_constrain_srcip_mexpr_not_unknown: 
  "(ternary_ternary_eval (map_match_tac common_matcher p (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce)) \<noteq> TernaryUnknown)"
apply(simp add: ipassmt_iface_constrain_srcip_mexpr_def split: option.split)
apply(intro conjI allI impI)
 apply (simp add: bool_to_ternary_Unknown)
apply(rename_tac ips)
by (metis (no_types, lifting) bool_to_ternary_simps(1) bool_to_ternary_simps(3) eval_ternary_And_comm eval_ternary_DeMorgan(1) eval_ternary_Not.simps(2) eval_ternary_Not.simps(3) eval_ternary_simps_simple(2) eval_ternary_simps_simple(4) list.map_comp ternary_ternary_eval_match_list_to_match_expr_not_unknown ternaryvalue.distinct(3))
(*wtf*)


lemma "ternary_ternary_eval (map_match_tac common_matcher p (rewrite_iiface ipassmt m)) = TernaryUnknown \<longleftrightarrow>
       ternary_ternary_eval (map_match_tac common_matcher p m) = TernaryUnknown"
apply(induction m rule: rewrite_iiface.induct)
apply(simp_all)
apply(simp_all add: ipassmt_iface_constrain_srcip_mexpr_not_unknown)
oops


lemma MatchNot_helper: "(ternary_ternary_eval (map_match_tac \<beta> p m')) = (ternary_ternary_eval (map_match_tac \<beta> p m)) \<Longrightarrow>
    matches (\<beta>,\<alpha>) (MatchNot m') a p = matches (\<beta>,\<alpha>) (MatchNot m) a p"
by(simp add: matches_tuple)



lemma no_unknowns_ternary_to_bool_Some: "\<not> has_unknowns \<beta> m \<Longrightarrow>
       ternary_to_bool (ternary_ternary_eval (map_match_tac \<beta> p m)) \<noteq> None"
  apply(induction m)
     apply(simp_all)
    using ternary_to_bool.elims apply blast
   using ternary_to_bool_Some apply fastforce
  using ternary_lift(6) ternary_to_bool_Some by auto
  

(*TODO: move*)
lemma matches_MatchNot_no_unknowns: "matches (\<beta>,\<alpha>) m' a p = matches (\<beta>,\<alpha>) m a p \<Longrightarrow>
    \<not> has_unknowns \<beta> m' \<Longrightarrow> \<not> has_unknowns \<beta> m \<Longrightarrow>
    matches (\<beta>,\<alpha>) (MatchNot m') a p = matches (\<beta>,\<alpha>) (MatchNot m) a p"
apply(auto split: option.split_asm simp: matches_case_tuple ternary_eval_def ternary_to_bool_bool_to_ternary elim: ternary_to_bool.elims)
apply(auto simp add: ternary_to_bool_Some no_unknowns_ternary_to_bool_Some)
done


lemma unknown_common_matcher_obtain_Extra: "\<exists>p. common_matcher x p = TernaryUnknown \<Longrightarrow> \<exists>y. x = Extra y"
  apply(cases x)
  by (simp_all add: bool_to_ternary_Unknown)

lemma "matches (common_matcher,\<alpha>) (f m) a p = matches (common_matcher,\<alpha>) m a p \<Longrightarrow>
    \<forall>m. f (MatchNot m) = MatchNot (f m) \<Longrightarrow>
    has_unknowns common_matcher (f m) \<longleftrightarrow> has_unknowns common_matcher m \<Longrightarrow>
    \<forall>x. (f (Match (Extra x))) = (Match (Extra x)) \<Longrightarrow>
    matches (common_matcher,\<alpha>) (MatchNot (f m)) a p = matches (common_matcher,\<alpha>) (MatchNot m) a p"
apply(induction m)
   apply(simp_all)
   apply(case_tac "\<not> has_unknowns common_matcher (f (Match x))")
    apply(simp_all)
    apply(rule matches_MatchNot_no_unknowns, simp_all)
   apply(drule unknown_common_matcher_obtain_Extra)
   apply(elim exE)
   apply(simp)
  apply(simp add: bunch_of_lemmata_about_matches)
oops

lemma xx1: "ternary_eval (TernaryNot t) = None \<Longrightarrow> ternary_ternary_eval t = TernaryUnknown"
by (simp add: eval_ternary_Not_UnknownD ternary_eval_def ternary_to_bool_None)


lemma xx2: "ternary_eval (TernaryNot t) = None \<Longrightarrow> ternary_eval t = None"
by (simp add: eval_ternary_Not_UnknownD ternary_eval_def ternary_to_bool_None)

lemma xx3: "ternary_eval (TernaryNot t) = Some b \<Longrightarrow>  ternary_eval t = Some (\<not> b)"
by (metis eval_ternary_Not.simps(1) eval_ternary_Not.simps(2) ternary_eval_def ternary_ternary_eval.simps(3) ternary_ternary_eval_idempotence_Not ternary_to_bool_Some)

lemma xxxx_x:"\<forall>a. in_doubt_allow a p = (\<not> b) \<Longrightarrow> False"
  apply(subgoal_tac "in_doubt_allow Accept p")
   prefer 2
   apply fastforce
  apply(subgoal_tac "\<not> in_doubt_allow Drop p")
   prefer 2
   apply fastforce
  by auto

(*needs the p in assm*)
lemma xxxx_xx:"\<alpha> Drop p \<noteq> \<alpha> Accept p \<Longrightarrow> \<forall>a. \<alpha> a p = (\<not> b) \<Longrightarrow> False"
  by simp



(*************THIS! refactor and move****************)



(*TODO: only holds for in_doubt_allow or on_doubt_deny because they have opposite results for some actions \<dots>
  generalize! add this to wf_unknown_match_tac:
  Drop \<noteq> Accept*)
lemma "(*\<alpha> Drop \<noteq> \<alpha> Accept \<Longrightarrow>*) \<forall> a. matches (\<beta>,in_doubt_allow) m' a p = matches (\<beta>,in_doubt_allow) m a p \<Longrightarrow>
    matches (\<beta>,in_doubt_allow) (MatchNot m') a p = matches (\<beta>,in_doubt_allow) (MatchNot m) a p"
apply(simp add: matches_case_tuple)
apply(case_tac "ternary_eval (TernaryNot (map_match_tac \<beta> p m'))")
apply(case_tac [!] "ternary_eval (TernaryNot (map_match_tac \<beta> p m))")
apply(simp_all)
apply(drule xx2)
apply(drule xx3)
apply(simp)
using xxxx_x apply metis

apply(drule xx2)
apply(drule xx3)
apply(simp)
using xxxx_x apply metis

apply(drule xx3)+
apply(simp)
done



(*TODO: move or delete*)
lemma ternary_to_bool_unknown_match_tac_eq_cases:
  "ternary_to_bool_unknown_match_tac \<alpha> a p t1 = ternary_to_bool_unknown_match_tac \<alpha> a p t2 \<longleftrightarrow>
  t1 = t2 \<or>
  t1 = TernaryUnknown \<and> (t2 = TernaryTrue \<longleftrightarrow> \<alpha> a p) \<or>
  t2 = TernaryUnknown \<and> (t1 = TernaryTrue \<longleftrightarrow> \<alpha> a p)"
apply(cases t1)
  apply(simp_all)
  apply(case_tac [!] t2)
        apply(simp_all)
done

lemma ipassmt_sanity_haswildcards_helper1: "ipassmt_sanity_haswildcards ipassmt \<Longrightarrow>
       ipassmt (Iface ifce2) = None \<Longrightarrow> ipassmt ifce = Some a \<Longrightarrow> \<not> match_iface ifce ifce2"
apply(simp add: ipassmt_sanity_haswildcards_def)
using iface_is_wildcard_def match_iface_case_nowildcard by fastforce


(*lemma ipv4cidr_union_set_fooo: fixes p::simple_packet
        shows "(p_src p \<notin> ipv4cidr_union_set ({aa} \<union> set x2)) \<longleftrightarrow>
    p_src p \<notin> ((\<lambda>(base, len). ipv4range_set_from_bitmask base len) aa) \<and> p_src p \<notin> ipv4cidr_union_set (set x2)"
by(simp add: ipv4cidr_union_set_def)*)

lemma helper_es_ist_spaet:"matches (common_matcher, \<alpha>) (MatchNot (match_list_to_match_expr (map (Match \<circ> Src \<circ> (\<lambda>(ip, y). Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) y)) x2))) a p \<longleftrightarrow>
       (p_src p \<notin> ipv4cidr_union_set (set x2))"
  thm match_list_to_match_expr_disjunction
  apply(induction x2)
   apply(simp add: bunch_of_lemmata_about_matches ipv4cidr_union_set_def)
  apply(simp add: bunch_of_lemmata_about_matches)
  apply(simp add: ipv4cidr_union_set_def)
  apply(simp add: match_simplematcher_SrcDst_not)
  apply(thin_tac _)
  apply(simp add: ipv4s_to_set_Ip4AddrNetmask_case)
done


(*would be simpler if normalied_nnf is assumed*)
lemma rewrite_iiface_matches_MatchNot_Primitive:
        "matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p \<Longrightarrow>
         matches (common_matcher, \<alpha>) (MatchNot (rewrite_iiface ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p"
     apply(case_tac x)
             apply(simp_all)
     apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
     apply(simp split: option.split_asm)
      apply(simp_all add: match_simplematcher_Iface_not match_simplematcher_Iface)
      apply(simp_all add: ipassmt_iface_constrain_srcip_mexpr_def)
      apply(simp add: match_simplematcher_Iface_not match_simplematcher_Iface; fail)
     apply(simp add: matches_DeMorgan)
     apply(simp add: helper_es_ist_spaet)
     apply(simp add: match_simplematcher_Iface_not)
     by auto

lemma rewrite_iiface_matches_Primitive:
        "matches (common_matcher, \<alpha>) (MatchNot (rewrite_iiface ipassmt (Match x))) a p = matches (common_matcher, \<alpha>) (MatchNot (Match x)) a p \<Longrightarrow>
         matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt (Match x)) a p = matches (common_matcher, \<alpha>) (Match x) a p"
     apply(case_tac x)
             apply(simp_all)
     apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
     apply(simp split: option.split)
     apply(intro conjI)
      apply(simp_all add: match_simplematcher_Iface_not match_simplematcher_Iface)
      apply(simp_all add: ipassmt_iface_constrain_srcip_mexpr_def)
      apply(simp split: option.split_asm)
     apply(simp add: matches_DeMorgan)
     apply(simp add: helper_es_ist_spaet)
     apply(simp add: match_simplematcher_Iface_not)
     by blast


lemma   "matches (common_matcher, \<alpha>) (MatchNot (rewrite_iiface ipassmt m)) a p = matches (common_matcher, \<alpha>) (MatchNot m) a p \<longleftrightarrow>
         matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p = matches (common_matcher, \<alpha>) m a p"
     apply(induction m)
        apply(simp_all add: rewrite_iiface_matches_Primitive)
       apply(simp_all add: bunch_of_lemmata_about_matches(6))
      using rewrite_iiface_matches_MatchNot_Primitive rewrite_iiface_matches_Primitive apply blast
     apply(simp_all add: bunch_of_lemmata_about_matches matches_DeMorgan)
     apply(safe)
     apply(simp_all)
     (**probably last case does not hold**)
     oops

lemma "matches (common_matcher, \<alpha>) m a p \<Longrightarrow> (*\<longleftrightarrow>*)
        matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p"
apply(induction m)
apply(simp_all)
     apply(case_tac x)
             apply(simp_all)
     apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
     apply(simp split: option.split)
     apply(intro conjI)
      apply(simp_all add: match_simplematcher_Iface_not match_simplematcher_Iface)
     defer (*needs*assm*)
defer
apply(simp add: bunch_of_lemmata_about_matches)
defer
oops




(*TODO: ambiguous?*)
lemma matches_ipassmt_iface_constrain_srcip_mexpr_case_Iface:
      fixes ifce::iface
      shows "ipassmt_sanity_haswildcards ipassmt \<Longrightarrow>
            case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips) \<Longrightarrow>
            matches (common_matcher, \<alpha>) (ipassmt_iface_constrain_srcip_mexpr ipassmt ifce) a p =
            matches (common_matcher, \<alpha>) (Match (IIface ifce)) a p"
  apply(simp add: match_simplematcher_Iface)
  apply(case_tac "ipassmt (Iface (p_iiface p))")
   apply(simp)
   apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
   apply(case_tac "ipassmt ifce")
    apply(simp; fail)
   apply(simp)
   apply(drule(2) ipassmt_sanity_haswildcards_helper1)
   apply(simp)
  apply(simp)
  apply(simp add: matches_ipassmt_iface_constrain_srcip_mexpr)
  apply(case_tac "ipassmt ifce")
   apply(simp; fail)
  apply(simp)
  apply(case_tac ifce)
  apply(rename_tac ifce_str)
  apply(case_tac "ifce_str = (p_iiface p)")
   apply (simp add: match_iface_refl)
  apply(simp)
  apply(subgoal_tac "\<not> match_iface (Iface ifce_str) (p_iiface p)")
   apply(simp)
  by (metis domI iface.sel iface_is_wildcard_def ipassmt_sanity_haswildcards_def match_iface_case_nowildcard)
  

lemma matches_rewrite_iiface:
     "normalized_nnf_match m \<Longrightarrow> ipassmt_sanity_haswildcards ipassmt \<Longrightarrow>
      (case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)) \<Longrightarrow>
      matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
  proof(induction m (*arbitrary: a*))
  case MatchAny thus ?case by simp
  next
  case (MatchNot m)
    hence IH: "normalized_nnf_match m \<Longrightarrow> matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p = matches (common_matcher, \<alpha>) m a p" by blast
    with MatchNot.prems IH show ?case
     apply(induction m)
     apply(simp_all add: rewrite_iiface_matches_MatchNot_Primitive)
     done
  next
  case(Match x)
   thus ?case
    apply(cases x)
            apply(simp_all)
    apply(rename_tac ifce)
    using matches_ipassmt_iface_constrain_srcip_mexpr_case_Iface by simp
  next
  case (MatchAnd m1 m2) thus ?case
    by(simp add: bunch_of_lemmata_about_matches)
  qed
    
    


end