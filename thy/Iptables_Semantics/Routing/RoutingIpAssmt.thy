theory RoutingIpAssmt
imports "../Primitive_Matchers/Ipassmt"
        RoutingRange
begin

context
begin

definition "routing_ipassmt rt = map prod.swap (reduced_range_destination rt wordinterval_UNIV)"
private lemma "set \<circ> map prod.swap = converse \<circ> set" by auto (* just a reminder *)

lemma "distinct (map fst (routing_ipassmt rt))"
unfolding routing_ipassmt_def
by(simp add: reduced_range_destination_def range_left_reduce_def list_left_reduce_def comp_def)

definition "routing_cidr_assmt rt = map_option cidr_split \<circ> map_of (routing_ipassmt rt) \<circ> (\<lambda>x. case x of Iface x \<Rightarrow> x)"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

private lemma not_ne_then: "a \<noteq> b \<Longrightarrow> \<not>a \<Longrightarrow> b" by clarify

private lemma m2: "\<lbrakk>xb \<noteq> xa; 
(zb, xb) \<in> reduced_ipset_destination rt UNIV; 
(za, xa) \<in> reduced_ipset_destination rt UNIV\<rbrakk>
       \<Longrightarrow> zb \<inter> za = {}"
unfolding reduced_ipset_destination_def
unfolding left_reduce_def domain_for_def
proof (clarsimp, goal_cases)
  case (1 a aa)
  note single_valued_ipset_destination[THEN single_valuedD] \<open>xb \<noteq> xa\<close>
  hence sv: "\<lbrakk>(b, xb) \<in> ipset_destination rt UNIV; (a, xa) \<in> ipset_destination rt UNIV\<rbrakk> \<Longrightarrow> b \<noteq> a" for a b
  by blast
  note ipset_left_side_nonempty hence lsne: "(a, xa) \<in> ipset_destination rt UNIV \<Longrightarrow> a \<noteq> {}" for a xa by blast
  have not_emptyD: "a \<inter> b \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> a \<and> x \<in> b" for a b by blast
  have "\<Union>{x. (x, xb) \<in> ipset_destination rt UNIV} \<inter> \<Union>{x. (x, xa) \<in> ipset_destination rt UNIV} = {}" (is "?undist")
  proof -
    from ipset_destination_distinct[THEN not_ne_then, rotated, rotated, of b xb rt UNIV a xa for a b]
    have *: "\<lbrakk>(b, xb) \<in> ipset_destination rt UNIV; (a, xa) \<in> ipset_destination rt UNIV; b \<noteq> a; b \<noteq> {}; a \<noteq> {}\<rbrakk> \<Longrightarrow> b \<inter> a = {}" for a b .
    have "\<And>x. \<lbrakk>(b, xb) \<in> ipset_destination rt UNIV; x \<in> b; (a, xa) \<in> ipset_destination rt UNIV; x \<in> a\<rbrakk> \<Longrightarrow> False" 
      for a b
      apply(frule (1) *)
      apply(erule (1) sv)
      apply(elim lsne)+
      apply blast
    done
    thus ?undist by blast
  qed
  thus ?case .
qed

private lemma m1: "\<lbrakk>xb \<noteq> xa; 
(zb, xb) \<in> set (reduced_range_destination rt wordinterval_UNIV); 
(za, xa) \<in> set (reduced_range_destination rt wordinterval_UNIV)\<rbrakk>
       \<Longrightarrow> wordinterval_to_set zb \<inter> wordinterval_to_set za = {}"
(*apply(drule m2[unfolded WordInterval.wordinterval_UNIV_set_eq[symmetric], 
               unfolded reduced_range_destination_eq[OF refl] rr_to_sr_def,
               where zb = "wordinterval_to_set zb" and za = "wordinterval_to_set za" and rt = rt])
apply(auto)
done*)
proof goal_cases
  case 1
  let ?wz = "\<lambda>zb xba. (wordinterval_to_set zb, xba) \<in> set (map (\<lambda>(x, y). (wordinterval_to_set x, y)) (reduced_range_destination rt wordinterval_UNIV))"
  from m2[unfolded WordInterval.wordinterval_UNIV_set_eq[symmetric], 
               unfolded reduced_range_destination_eq[OF refl] rr_to_sr_def,
               where zb = "wordinterval_to_set zb" and za = "wordinterval_to_set za" and rt = rt]
  have *: "\<lbrakk>xba \<noteq> xaa; ?wz zb xba; ?wz za xaa\<rbrakk>
  \<Longrightarrow> wordinterval_to_set zb \<inter> wordinterval_to_set za = {}" for xba xaa .
  from 1(2,3) show ?thesis using *[OF 1(1)] by fastforce
qed

lemma "ipassmt_sanity_disjoint (routing_cidr_assmt rt)"
unfolding ipassmt_sanity_disjoint_def routing_cidr_assmt_def comp_def
  apply(clarify)
  apply(subst the_map_option, (simp;fail))+
  apply(simp)
  
  apply(unfold routing_ipassmt_def)
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
  
  apply(rule m1; assumption)
done

end

end