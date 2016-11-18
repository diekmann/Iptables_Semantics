theory Featherweight_OpenFlow_Comparison
imports Semantics_OpenFlow
begin

(* compare to https://github.com/frenetic-lang/featherweight-openflow/blob/master/coq/OpenFlow/OpenFlowSemantics.v#L260 *)
inductive guha_table_semantics :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> 'a option \<Rightarrow> bool" where
guha_matched: "\<gamma> (ofe_fields fe) p = True \<Longrightarrow> 
 \<forall>fe' \<in> set (ft1 @ ft2). ofe_prio fe' > ofe_prio fe \<longrightarrow> \<gamma> (ofe_fields fe') p = False \<Longrightarrow> 
 guha_table_semantics \<gamma> (ft1 @ fe # ft2) p (Some (ofe_action fe))" |
guha_unmatched: "\<forall>fe \<in> set ft. \<gamma> (ofe_fields fe) p = False \<Longrightarrow>
 guha_table_semantics \<gamma> ft p None"

(* 
so... there's the possibility for a flow table with two matching entries.
I'm not so sure it is a good idea to model undefined behavior by nondeterministic but very defined behavior..
*)
lemma guha_table_semantics_ex2res:
    assumes ta: "CARD('a) \<ge> 2" (* if there's only one action, the whole thing is moot. *)
	assumes ms: "\<exists>ff. \<gamma> ff p" (* if our matcher rejects the packet for any match condition, it is borked. *)
	shows "\<exists>ft (a1 :: 'a) (a2 :: 'a). a1 \<noteq> a2 \<and> guha_table_semantics \<gamma> ft p (Some a1) \<and> guha_table_semantics \<gamma> ft p (Some a2)"
proof -
	from ms	obtain ff  where m: "\<gamma> ff p" ..
	from ta obtain a1 a2 :: 'a where as: "a1 \<noteq> a2" using card2_eI by blast
	let ?fe1 = "OFEntry 0 ff a1"
	let ?fe2 = "OFEntry 0 ff a2"
	let ?ft = "[?fe1, ?fe2]"
	find_theorems "_ @ [_]"
	have "guha_table_semantics \<gamma> ?ft p (Some a1)" "guha_table_semantics \<gamma> ?ft p (Some a2)" 
	by(rule guha_table_semantics.intros(1)[of \<gamma> ?fe1 p "[]" "[?fe2]", unfolded append_Nil flow_entry_match.sel] | 
	   rule guha_table_semantics.intros(1)[of \<gamma> ?fe2 p "[?fe1]" "[]", unfolded append_Nil2 flow_entry_match.sel append.simps] |
	   simp add: m)+
	thus ?thesis using as by(intro exI conjI)
qed

lemma guha_umstaendlich: (* or maybe it's Coq where the original formulation is more beneficial *)
	assumes ae: "a = ofe_action fe"
	assumes ele: "fe \<in> set ft"
	assumes rest: "\<gamma> (ofe_fields fe) p" 
	              "\<forall>fe' \<in> set ft. ofe_prio fe' > ofe_prio fe \<longrightarrow> \<not>\<gamma> (ofe_fields fe') p"
 	shows "guha_table_semantics \<gamma> ft p (Some a)"
proof -
	from ele obtain ft1 ft2 where ftspl: "ft = ft1 @ fe # ft2" using split_list by fastforce
	show ?thesis unfolding ae ftspl
		apply(rule guha_table_semantics.intros(1))
		using rest(1) apply(simp)
		using rest(2)[unfolded ftspl] apply simp
	done
qed

lemma guha_matched_rule_inversion:
	assumes "guha_table_semantics \<gamma> ft p (Some a)"
	shows "\<exists>fe \<in> set ft. a = ofe_action fe \<and> \<gamma> (ofe_fields fe) p \<and> (\<forall>fe' \<in> set ft. ofe_prio fe' > ofe_prio fe \<longrightarrow> \<not>\<gamma> (ofe_fields fe') p)"
proof - 
	{
		fix d
		assume "guha_table_semantics \<gamma> ft p d"
		hence "Some a = d \<Longrightarrow> (\<exists>fe \<in> set ft. a = ofe_action fe \<and> \<gamma> (ofe_fields fe) p \<and> (\<forall>fe' \<in> set ft. ofe_prio fe' > ofe_prio fe \<longrightarrow> \<not>\<gamma> (ofe_fields fe') p))"
			by(induction rule: guha_table_semantics.induct) simp_all (* strange to show this by induction, but I don't see an exhaust or cases I could use. *)
	}
	from this[OF assms refl]
	show ?thesis .
qed

lemma guha_equal_Action:
	assumes no: "no_overlaps \<gamma> ft"
	assumes spm: "OF_priority_match \<gamma> ft p = Action a"
	shows "guha_table_semantics \<gamma> ft p (Some a)"
proof -
	note spm[THEN OF_spm3_get_fe] then obtain fe where a: "ofe_action fe = a" and fein: "fe \<in> set ft" and feana: "OF_priority_match_ana \<gamma> ft p = Action fe" by blast
	show ?thesis
		apply(rule guha_umstaendlich)
		apply(rule a[symmetric])
		apply(rule fein)
		using feana unfolding OF_priority_match_ana_def
		apply(auto dest!: filter_singleton split: list.splits)
	done
qed

lemma guha_equal_NoAction:
	assumes no: "no_overlaps \<gamma> ft"
	assumes spm: "OF_priority_match \<gamma> ft p = NoAction"
	shows "guha_table_semantics \<gamma> ft p None"
using spm unfolding OF_priority_match_def
by(auto simp add: filter_empty_conv OF_spm3_noa_none[OF no spm] intro: guha_table_semantics.intros(2) split: list.splits)

lemma guha_equal_hlp:
	assumes no: "no_overlaps \<gamma> ft"
	shows "guha_table_semantics \<gamma> ft p (ftb_to_option (OF_priority_match \<gamma> ft p))"
	unfolding ftb_to_option_def
	apply(cases "(OF_priority_match \<gamma> ft p)")
	apply(simp add: guha_equal_Action[OF no])
	apply(simp add: guha_equal_NoAction[OF no])
	apply(subgoal_tac False, simp)
	apply(simp add: no no_overlaps_not_unefined)
done

lemma guha_deterministic1: "guha_table_semantics \<gamma> ft p (Some x1) \<Longrightarrow> \<not> guha_table_semantics \<gamma> ft p None" 
by(auto simp add: guha_table_semantics.simps)

lemma guha_deterministic2: "\<lbrakk>no_overlaps \<gamma> ft; guha_table_semantics \<gamma> ft p (Some x1); guha_table_semantics \<gamma> ft p (Some a)\<rbrakk> \<Longrightarrow> x1 = a"
proof(rule ccontr, goal_cases)
	case 1
	note 1(2-3)[THEN guha_matched_rule_inversion] then obtain fe1 fe2 where fes:
	"fe1\<in>set ft" "x1 = ofe_action fe1" "\<gamma> (ofe_fields fe1) p" "(\<forall>fe'\<in>set ft. ofe_prio fe1 < ofe_prio fe' \<longrightarrow> \<not> \<gamma> (ofe_fields fe') p)"
    "fe2\<in>set ft" "a  = ofe_action fe2" "\<gamma> (ofe_fields fe2) p" "(\<forall>fe'\<in>set ft. ofe_prio fe2 < ofe_prio fe' \<longrightarrow> \<not> \<gamma> (ofe_fields fe') p)"
    	by blast
    from \<open>x1 \<noteq> a\<close> have fene: "fe1 \<noteq> fe2" using fes(2,6) by blast
    have pe: "ofe_prio fe1 = ofe_prio fe2" using fes(1,3-4,5,7-8) less_linear by blast
    note \<open>no_overlaps \<gamma> ft\<close>[THEN check_no_overlapI, unfolded check_no_overlap_def]
    note this[unfolded Ball_def, THEN spec, THEN mp, OF fes(1), THEN spec, THEN mp, OF fes(5),THEN spec, THEN mp, OF UNIV_I, of p] pe fene fes(3,7)
    thus False by blast
qed

lemma guha_equal:
	assumes no: "no_overlaps \<gamma> ft"
	shows "OF_priority_match \<gamma> ft p = option_to_ftb d \<longleftrightarrow> guha_table_semantics \<gamma> ft p d"
	using guha_equal_hlp[OF no, of p] unfolding ftb_to_option_def option_to_ftb_def
	apply(cases "OF_priority_match \<gamma> ft p"; cases d)
	apply(simp_all)
	using guha_deterministic1 apply fast
	using guha_deterministic2[OF no] apply blast
	using guha_deterministic1 apply fast
	using no_overlaps_not_unefined[OF no] apply fastforce
	using no_overlaps_not_unefined[OF no] apply fastforce 
done

lemma guha_nondeterministicD:
	assumes "\<not>check_no_overlap \<gamma> ft"
	shows "\<exists>fe1 fe2 p. fe1 \<in> set ft \<and> fe2 \<in> set ft
		\<and> guha_table_semantics \<gamma> ft p (Some (ofe_action fe1))
		\<and> guha_table_semantics \<gamma> ft p (Some (ofe_action fe2))"
using assms
apply(unfold check_no_overlap_def)
apply(clarsimp)
apply(rename_tac fe1 fe2 p)
apply(rule_tac x = fe1 in exI)
apply(simp)
apply(rule_tac x = fe2 in exI)
apply(simp)
apply(rule_tac x = p in exI)
apply(rule conjI)
apply(subst guha_table_semantics.simps)
apply(rule disjI1)
apply(clarsimp)
apply(rule_tac x = fe1 in exI)
apply(drule split_list)
apply(clarify)
apply(rename_tac ft1 ft2)
apply(rule_tac x = ft1 in exI)
apply(rule_tac x = ft2 in exI)
apply(simp)
oops (* shadowed overlaps yay! *)

text\<open>The above lemma does indeed not hold, the reason for this are (possibly partially) shadowed overlaps.
This is exemplified below: If there are at least three different possible actions (necessary assumption)
and a match expression that matches all packets (convenience assumption), it is possible to construct a flow 
table that is admonished by @{const check_no_overlap} but still will never run into undefined behavior.
\<close>
(* This is not the terribly most important lemma. Feel free to delete it if the proof gives you trouble. *)
lemma
  assumes "CARD('action) \<ge> 3"
  assumes "\<forall>p. \<gamma> x p" (* with a sane \<gamma>, x = {} *)
	shows "\<exists>ft::('a, 'action) flow_entry_match list. \<not>check_no_overlap \<gamma> ft \<and>
	  \<not>(\<exists>fe1 fe2 p. fe1 \<in> set ft \<and> fe2 \<in> set ft \<and> fe1 \<noteq> fe2 \<and> ofe_prio fe1 = ofe_prio fe2
		\<and> guha_table_semantics \<gamma> ft p (Some (ofe_action fe1))
		\<and> guha_table_semantics \<gamma> ft p (Some (ofe_action fe2)))"
proof -
  obtain adef aa ab :: 'action where anb[simp]: "aa \<noteq> ab" "adef \<noteq> aa" "adef \<noteq> ab" using assms(1) card3_eI by blast
  let ?cex = "[OFEntry 1 x adef, OFEntry 0 x aa, OFEntry 0 x ab]"
  have ol: "\<not>check_no_overlap \<gamma> ?cex"
    unfolding check_no_overlap_def ball_simps
    apply(rule bexI[where x = "OFEntry 0 x aa", rotated], (simp;fail))
    apply(rule bexI[where x = "OFEntry 0 x ab", rotated], (simp;fail))
    apply(simp add: assms)
  done
  have df: "guha_table_semantics \<gamma> ?cex p oc \<Longrightarrow> oc = Some adef" for p oc 
  unfolding guha_table_semantics.simps
    apply(elim disjE; clarsimp simp: assms)
    subgoal for fe ft1 ft2
    apply(cases "ft1 = []")
    apply(fastforce)
    apply(cases "ft2 = []")
    apply(fastforce)
    apply(subgoal_tac "ft1 = [OFEntry 1 x adef] \<and> fe = OFEntry 0 x aa \<and> ft2 = [OFEntry 0 x ab]")
    apply(simp;fail)
    apply(clarsimp simp add: List.neq_Nil_conv)
    apply(rename_tac ya ys yz)
    apply(case_tac ys; clarsimp simp add: List.neq_Nil_conv)
  done done
  show ?thesis
    apply(intro exI[where x = ?cex], intro conjI, fact ol)
    apply(clarify)
    apply(unfold set_simps)
    apply(elim insertE; clarsimp)
    apply((drule df)+; unfold option.inject; (elim anb[symmetric, THEN notE] | (simp;fail))?)+
  done
qed



end
