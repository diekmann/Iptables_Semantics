theory Interface_Replace
imports
  No_Spoof (*TODO imports boolean semantics, get rid of!*)
  Common_Primitive_toString
  Transform
begin

section{*Abstracting over Primitives*}

term fold

definition ipassmt_iface_to_srcip_mexpr :: "ipassignment \<Rightarrow> iface \<Rightarrow> common_primitive match_expr" where
  "ipassmt_iface_to_srcip_mexpr ipassmt ifce = (case ipassmt ifce of
          None \<Rightarrow> Match (IIface ifce)
        | Some ips \<Rightarrow> match_list_to_match_expr (map (Match \<circ> Src) (map (\<lambda>(ip, n). (Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) n)) ips))
        )"

lemma ipv4s_to_set_Ip4AddrNetmask_case: "ipv4s_to_set (case x of (ip, x) \<Rightarrow> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) x) =
       (case x of (x, xa) \<Rightarrow> ipv4range_set_from_bitmask x xa)"
  by(cases x) (simp add: ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr)

lemma matches_ipassmt_iface_to_srcip_mexpr: 
    "matches (common_matcher, \<alpha>) (ipassmt_iface_to_srcip_mexpr ipassmt ifce) a p \<longleftrightarrow> (case ipassmt ifce of
            None \<Rightarrow> match_iface ifce (p_iiface p)
          | Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)
          )"
  apply(simp split: option.split add: ipassmt_iface_to_srcip_mexpr_def)
  apply(intro conjI allI)
   apply(simp add: match_simplematcher_Iface; fail)
  apply(simp add: match_list_to_match_expr_disjunction[symmetric] match_list_matches ipv4cidr_union_set_def)
  apply(simp add: match_simplematcher_SrcDst ipv4s_to_set_Ip4AddrNetmask_case)
  done
  

fun rewrite_iiface :: "ipassignment \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
  "rewrite_iiface _       MatchAny = MatchAny" |
  "rewrite_iiface ipassmt (Match (IIface ifce)) = ipassmt_iface_to_srcip_mexpr ipassmt ifce" |
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


lemma ipassmt_iface_to_srcip_mexpr_not_unknown: 
  "(ternary_ternary_eval (map_match_tac common_matcher p (ipassmt_iface_to_srcip_mexpr ipassmt ifce)) \<noteq> TernaryUnknown)"
apply(simp add: ipassmt_iface_to_srcip_mexpr_def split: option.split)
apply(intro conjI allI impI)
 apply (simp add: bool_to_ternary_Unknown)
apply(rename_tac ips)
by (metis List.map.compositionality ternary_ternary_eval_match_list_to_match_expr_not_unknown) (*wtf*)


lemma "ternary_ternary_eval (map_match_tac common_matcher p (rewrite_iiface ipassmt m)) = TernaryUnknown \<longleftrightarrow>
       ternary_ternary_eval (map_match_tac common_matcher p m) = TernaryUnknown"
apply(induction m rule: rewrite_iiface.induct)
apply(simp_all)
apply(simp_all add: ipassmt_iface_to_srcip_mexpr_not_unknown)
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

(*TODO: only holds for in_doubt_allow or on_doubt_deny because they have opposite results for some actions \<dots>
  generalize! add this to wf_unknown_match_tac:
  Drop \<noteq> Accept*)
lemma "\<alpha> Drop \<noteq> \<alpha> Accept \<Longrightarrow> \<forall> a. matches (\<beta>,in_doubt_allow) m' a p = matches (\<beta>,in_doubt_allow) m a p \<Longrightarrow>
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

(*need: no wildcards in ipassmt*)
lemma "(case ipassmt (Iface (p_iiface p)) of Some ips \<Rightarrow> p_src p \<in> ipv4cidr_union_set (set ips)) \<Longrightarrow>
    matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p \<longleftrightarrow> matches (common_matcher, \<alpha>) m a p"
  proof(induction m)
  case MatchAny thus ?case by simp
  next
  case (MatchNot m)
    hence IH: "matches (common_matcher, \<alpha>) (rewrite_iiface ipassmt m) a p = matches (common_matcher, \<alpha>) m a p" by blast
    (*hence "ternary_to_bool_unknown_match_tac \<alpha> a p (ternary_ternary_eval (map_match_tac common_matcher p (rewrite_iiface ipassmt m))) =
    ternary_to_bool_unknown_match_tac \<alpha> a p (ternary_ternary_eval (map_match_tac common_matcher p m))"
     by(simp add: matches_tuple)
    hence "(ternary_ternary_eval (map_match_tac common_matcher p (rewrite_iiface ipassmt m))) =
    (ternary_ternary_eval (map_match_tac common_matcher p m))"
     apply -
     apply(subst(asm) ternary_to_bool_unknown_match_tac_eq_cases)
     apply(safe)
     apply(simp_all)
     apply(case_tac "(ternary_ternary_eval (map_match_tac common_matcher p m))")
     apply(case_tac [!] "(ternary_ternary_eval (map_match_tac common_matcher p (rewrite_iiface ipassmt m)))")
     apply(simp_all)
     sorry*)
    thus ?case
     apply -
     apply(simp)
     apply(rule matches_MatchNot_no_unknowns)
       apply(simp)
     sorry
  next
  case(Match a)
   thus ?case
    apply(cases a)
            apply(simp_all)
    apply(rename_tac ifce)
    apply(simp add: Common_Primitive_Matcher.match_simplematcher_Iface)
    apply(case_tac "ipassmt (Iface (p_iiface p))")
     apply(simp)
     apply(simp add: matches_ipassmt_iface_to_srcip_mexpr)
     apply(case_tac "ipassmt ifce")
      apply(simp add: ; fail)
     apply(simp)
     defer (*should be by ipassmt asm*)
    apply(simp)
    apply(simp add: matches_ipassmt_iface_to_srcip_mexpr)
    (*by assumption?*)
    sorry
  next
  case (MatchAnd m1 m2) thus ?case
    by(simp add: bunch_of_lemmata_about_matches)
  qed
    
    


end