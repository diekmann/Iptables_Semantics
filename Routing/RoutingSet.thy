theory RoutingSet
imports Routing
begin

subsection{*Definition*}

fun ipset_destination :: "prefix_routing \<Rightarrow> ipv4addr set \<Rightarrow> (ipv4addr set \<times> port set) set" where
"ipset_destination [] rg = (if rg = {} then  {} else {(rg, {})})" |
"ipset_destination (r # rs) rg = (
  let rpm = ipset_prefix_match (routing_match r) rg in (let m = fst rpm in (let nm = snd rpm in (
    (if m = {}  then {} else { (m, routing_action r) }) \<union> 
    (ipset_destination rs nm)
))))"

lemma ipset_destination_split1: assumes "X \<inter> prefix_to_ipset (routing_match r) \<noteq> {}" 
      shows "ipset_destination (r # rs) X = {(X \<inter> prefix_to_ipset (routing_match r), routing_action r)} \<union> 
      ipset_destination rs (X - prefix_to_ipset (routing_match r))"
using assms by(simp)
lemma ipset_destination_split2: assumes "X \<inter> prefix_to_ipset (routing_match r) = {}" 
      shows "ipset_destination (r # rs) X = ipset_destination rs X"
using assms Diff_triv by force


lemma ipset_destination_complete:
  "UNION (ipset_destination rules rg) fst = rg"
apply(induction rule: ipset_destination.induct)
apply simp 
apply(simp only:)
apply(subst ipset_destination.simps(2))
apply(simp only: Let_def ipset_prefix_match_m ipset_prefix_match_nm)
apply auto
done

lemma ipset_destination_subsets:
  "x \<in> ipset_destination rules rg \<Longrightarrow> fst x \<subseteq> rg"
  using ipset_destination_complete by blast

lemma ipset_destination_not_in:
  "\<not>srg \<subseteq> rg \<Longrightarrow>  (srg, ports) \<notin> ipset_destination rs rg"
  using ipset_destination_complete by fastforce

lemma if_split: "c \<longrightarrow> P x \<Longrightarrow> \<not>c \<longrightarrow> P y \<Longrightarrow> P (if c then x else y)" by simp

lemma ipset_destination_distinct:
  assumes "r1 \<noteq> {}" and "r2 \<noteq> {}" 
  assumes "(r1, p1) \<in> ipset_destination rtbl rg"
  assumes "(r2, p2) \<in> ipset_destination rtbl rg"
  shows "(r1 = r2) \<noteq> (r1 \<inter> r2 = {})"
using assms
proof(induction rtbl arbitrary: rg)
  case Nil thus ?case by(case_tac "rg = {}") simp_all 
next
  case (Cons r rs)
  {
    fix rx px
    have "(rx, px) \<noteq> (rg \<inter> prefix_to_ipset (routing_match r), routing_action r) \<Longrightarrow>
    (rx, px) \<in> ipset_destination (r # rs) rg \<Longrightarrow> (rx, px) \<in> ipset_destination rs (rg - prefix_to_ipset (routing_match r))"
      by(case_tac "rg \<inter> prefix_to_ipset (routing_match r) = {}") auto
  } note hammer = this
  let ?current = "(rg \<inter> prefix_to_ipset (routing_match r), routing_action r)"
  note mIH = Cons(1)[OF Cons(2) Cons(3)]    
  show ?case
  proof(case_tac "(r1, p1) = ?current", case_tac[!] "(r2, p2) = ?current")
    case goal1 thus ?case using assms(1) by simp
  next
    case goal4
    thm goal4(1) Cons.prems(3) hammer
    from mIH[OF hammer[OF goal4(1) Cons.prems(3)] hammer[OF goal4(2) Cons.prems(4)]] show ?case .
  next
    case goal2 
    thm ipset_destination_subsets
    from ipset_destination_subsets[OF hammer[OF goal2(2) Cons.prems(4)]] goal2(1) show ?case using assms(1) by auto
  next
    case goal3
    thm ipset_destination_subsets
    from ipset_destination_subsets[OF hammer[OF goal3(1) Cons.prems(3)]] goal3(2) show ?case using assms(1) by auto
  qed
qed

lemma single_valued_extend: "\<lbrakk>single_valued r; \<forall>z. (x,z) \<notin> r\<rbrakk> \<Longrightarrow> single_valued (insert (x,y) r)"
  unfolding single_valued_def by blast

lemma int_not_in_cut: "a \<inter> b \<noteq> {} \<Longrightarrow> \<not> a \<inter> b \<subseteq> a - b" by blast

lemma single_valued_ipset_destination: "single_valued (ipset_destination rtbl rg)"
proof(induction rtbl arbitrary: rg)
  case goal1 thus ?case using single_valued_def by auto
next
  case goal2
  note IH = goal2
  note single_valued_extend[OF goal2]
  thus ?case
  proof(cases "rg \<inter> prefix_to_ipset (routing_match a) = {}")
    case goal1
    note triv = ipset_destination_split2[OF goal1(2)]
    with goal2 show ?case by simp
  next
    case goal2
    note hard = ipset_destination_split1[OF goal2(2)]
    have "\<not> rg \<inter> prefix_to_ipset (routing_match a) \<subseteq> (rg - prefix_to_ipset (routing_match a))"
      using int_not_in_cut[OF goal2(2)] .
    then show ?case
      using hard insert_is_Un[symmetric] single_valued_extend ipset_destination_not_in IH by metis
  qed
qed


fun ipset_destination_map :: "prefix_routing \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr \<Rightarrow> port set option" where
"ipset_destination_map [] rg = (\<lambda>ip. if ip \<in> rg then Some {} else None)" |
"ipset_destination_map (r#rs) rg = 
  (let rpm = ipset_prefix_match (routing_match r) rg in (let m = fst rpm in (let nm = snd rpm in (\<lambda>ip.
    if ip \<in> rg \<inter> m then Some (routing_action r) else ipset_destination_map rs nm ip))))"

fun ipset_destination_map2 :: "prefix_routing \<Rightarrow> ipv4addr set \<Rightarrow> ipv4addr \<Rightarrow> port set option" where
"ipset_destination_map2 [] rg = (\<lambda>ip. if ip \<in> rg then Some {} else None)" |
"ipset_destination_map2 (r#rs) rg = 
  (let rpm = ipset_prefix_match (routing_match r) rg in (let m = fst rpm in (let nm = snd rpm in (\<lambda>ip.
    if ip \<in> rg \<inter> m then Some (routing_action r) else ipset_destination_map2 rs rg ip))))"

lemma rdm2_extend: "y \<subseteq> x \<Longrightarrow> ip \<in> y \<Longrightarrow> ipset_destination_map2 rs y ip = ipset_destination_map2 rs x ip"
  by(induction rs arbitrary: x y) auto

lemma rdm_not_in_None:  "ip \<notin> rg \<Longrightarrow> ipset_destination_map  rs rg ip = None" by(induction rs arbitrary: rg) force+
lemma rdm2_not_in_None: "ip \<notin> rg \<Longrightarrow> ipset_destination_map2 rs rg ip = None" by(induction rs) force+
  
lemma rdm_rdm2_eq: "ipset_destination_map rtbl rg ip = ipset_destination_map2 rtbl rg ip"
  apply(induction rtbl arbitrary: rg)
   apply force
  apply(rename_tac r rs rg)
  apply(simp only: ipset_destination_map.simps ipset_destination_map2.simps Let_def)
  apply(case_tac "ip \<in> rg \<inter> fst (ipset_prefix_match (routing_match r) rg)")
   apply(simp)
  apply(simp only: if_False ipset_prefix_match_nm not_not)
  apply(case_tac "ip \<notin> rg")
   apply(simp add: rdm_not_in_None rdm2_not_in_None)
  apply(rule rdm2_extend)
   apply force+
done
lemma rdm_rdm2_eq2: "ipset_destination_map = ipset_destination_map2"
  unfolding fun_eq_iff rdm_rdm2_eq by rule+

definition "ipset_rel r = {(ip,port)|ip port rg. (rg,port) \<in> r \<and> ip \<in> rg}"
lemma in_ipset_rel: "in_rel (ipset_rel r) x y = (\<exists>rg. x \<in> rg \<and> (rg,y) \<in> r)"
  unfolding in_rel_def ipset_rel_def by auto

lemma rdm_rd_eq: "(ipset_destination_map rtbl rg ip = Some ports) = in_rel (ipset_rel (ipset_destination rtbl rg)) ip ports"
  apply(induction rtbl arbitrary: rg ports)
   apply(unfold in_ipset_rel)
   apply force
  apply(simp only: ipset_destination_map.simps Let_def)
  apply(rename_tac r rs rg ports)
  apply(case_tac "ip \<in> rg \<inter> fst (ipset_prefix_match (routing_match r) rg)")
   apply(thin_tac "(\<And>rg ports. (ipset_destination_map rs rg ip = Some ports) = (\<exists>rga. ip \<in> rga \<and> (rga, ports) \<in> ipset_destination rs rg))")
   apply(simp_all only: if_True if_False option.inject)
   apply(subgoal_tac "fst (ipset_prefix_match (routing_match r) rg) \<noteq> {}") 
    prefer 2
    apply blast
   apply(rule iffI)
    apply(simp only: ipset_destination.simps Let_def if_False rpm_m_dup_simp)
    apply blast
   apply clarify
   apply(simp only: refl if_True if_False Un_empty_left ipset_destination.simps Let_def)
   apply(subgoal_tac "(rga, ports) \<notin> ipset_destination rs (snd (ipset_prefix_match (routing_match r) rg))")
    apply force
   apply(rule ipset_destination_not_in)
   apply(simp only: ipset_prefix_match_m ipset_prefix_match_nm, blast)
  apply(thin_tac "(\<And>rg ports. (ipset_destination_map rs rg ip = Some ports) = (\<exists>rga. ip \<in> rga \<and> (rga, ports) \<in> ipset_destination rs rg))") (* how the hell does that even still work *)
  apply(rule iffI)
   apply(subst ipset_destination.simps(2))[1]
   apply(unfold Let_def)[1]
   apply(case_tac "fst (ipset_prefix_match (routing_match r) rg) = {}")
    apply(simp_all only: refl if_True if_False Un_empty_left)[2]
   apply blast
  apply(case_tac "fst (ipset_prefix_match (routing_match r) rg) = {}")
   apply(simp_all only: refl if_True if_False Un_empty_left ipset_destination.simps Let_def)[2]
  apply(simp only: rpm_m_dup_simp)
  apply blast
done
(*
lemma "(ipset_destination_map rtbl rg ip = Some ports) = in_rel (ipset_rel (ipset_destination rtbl rg)) ip ports"
unfolding in_ipset_rel
proof(induction rtbl arbitrary: rg ports)
  case Nil thus ?case by force
next
  case (Cons r rs)
  show ?case
  proof(cases "ip \<in> rg \<inter> fst (ipset_prefix_match (routing_match r) rg)")
    case True
    have "fst (ipset_prefix_match (routing_match r) rg) \<noteq> {}" sorry
    have "\<not>(\<exists>rg. ip \<in> rg \<and> (rg, ports) \<in> ipset_destination rs (snd (ipset_prefix_match (routing_match r) rg)))" sorry
    show ?thesis sorry
  next
    case False thus ?thesis sorry
  qed
oops TODO: Maybe *)

lemma single_valued_ipset_destination_rel: "single_valued (ipset_rel (ipset_destination rtbl rg))"
  by (metis (mono_tags) in_rel_def option.inject rdm_rd_eq single_valued_def)

lemma "(ipset_destination_map2 rtbl rg ip = Some ports) = in_rel (ipset_rel (ipset_destination rtbl rg)) ip ports"
  using rdm_rd_eq rdm_rdm2_eq2 by(simp only:)

lemma ipset_destination_empty[simp]: "ipset_destination rtbl {} = {}"
  by(induction rtbl) simp_all

subsection{*Correctness*}

lemma packet_semantics_rdm2_eq:
  assumes "valid_prefixes rtbl"
  assumes rg_elem: "ip \<in> rg"
  shows "(ipset_destination_map2 rtbl rg ip = Some ports) = (routing_table_semantics rtbl ip = ports)"
using assms
proof(induction rtbl) (* Note how this induction is not made over arbitrary rg *)
  case (Cons r rs) 
  let ?match = "routing_match r"
  have v_pfx: "valid_prefix ?match"
    using conjunct1[OF valid_prefixes_split[OF Cons.prems(1)]] .
  show ?case
  proof(cases "prefix_match_semantics ?match ip")
    case True thus ?thesis
      using packet_ipset_prefix_eq2[OF rg_elem v_pfx True] 
      by simp               
    next
      case False thus ?thesis
        using packet_ipset_prefix_eq1[OF rg_elem v_pfx False] 
              Cons.IH[OF conjunct2[OF valid_prefixes_split[OF Cons.prems(1)]]]
        by simp
  qed
qed simp

theorem ipset_destination_correct:
  assumes "valid_prefixes rtbl"
  assumes rg_elem: "ip \<in> rg"
  shows "(routing_table_semantics rtbl ip = ports) = in_rel (ipset_rel (ipset_destination rtbl rg)) ip ports"
proof -
  have "in_rel (ipset_rel (ipset_destination rtbl rg)) ip ports = 
    (ipset_destination_map rtbl rg ip = Some ports)" using rdm_rd_eq ..
  also have "\<dots> = (ipset_destination_map2 rtbl rg ip = Some ports)" unfolding rdm_rdm2_eq ..
  also have "\<dots> = (routing_table_semantics rtbl ip = ports)" 
    unfolding packet_semantics_rdm2_eq[OF `valid_prefixes rtbl` rg_elem]  ..
  finally show ?thesis ..
qed

corollary ipset_destination_correct_UNIV: 
  assumes "valid_prefixes rtbl"
  shows "(packet_routing_table_semantics rtbl packet = ports) = in_rel (ipset_rel (ipset_destination rtbl UNIV)) (dst_addr packet) ports"
unfolding packet_routing_table_semantics_def ipset_destination_correct[OF assms UNIV_I] ..

lemma ipset_left_side_nonempty: "x \<in> (fst ` (ipset_destination rtbl rg)) \<Longrightarrow> x \<noteq> {}"
  apply(induction rtbl arbitrary: rg)
   apply(rename_tac rg)
   apply(case_tac "rg = {}")
    apply(auto)[2]
  apply(rename_tac r rs rg)
  apply(case_tac "fst (ipset_prefix_match (routing_match r) rg) = {}")
   apply(simp)
  apply(clarsimp simp only: Let_def ipset_destination.simps if_False )
  apply(rename_tac r rs rg a b)
  apply(case_tac "(a, b)  = (fst (ipset_prefix_match (routing_match r) rg), routing_action r)")
   apply simp
  apply blast
done

subsection{*Reduction*}

lemma left_reduce_ipset_rel_stable: "ipset_rel R = ipset_rel (left_reduce R)"
  unfolding ipset_rel_def left_reduce_def domain_for_def
  by auto

definition "reduced_ipset_destination tbl r = left_reduce (ipset_destination tbl r)"
lemma reduced_ipset_destination_correct:
  "\<lbrakk> valid_prefixes rtbl; ip \<in> rg \<rbrakk> \<Longrightarrow>
  (routing_table_semantics rtbl ip = ports) = in_rel (ipset_rel (reduced_ipset_destination rtbl rg)) ip ports"
  unfolding reduced_ipset_destination_def
  unfolding left_reduce_ipset_rel_stable[symmetric]
  using ipset_destination_correct .

end
