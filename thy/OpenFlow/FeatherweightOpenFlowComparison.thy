theory FeatherweightOpenFlowComparison
imports Semantics_OpenFlow
begin

(* compare to https://github.com/frenetic-lang/featherweight-openflow/blob/master/coq/OpenFlow/OpenFlowSemantics.v#L260 *)
inductive guha_table_semantics :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> 'p \<Rightarrow> 'a option \<Rightarrow> bool" where
"\<gamma> (ofe_fields fe) p = True \<Longrightarrow> 
 \<forall>fe' \<in> set (ft1 @ ft2). ofe_prio fe' > ofe_prio fe \<longrightarrow> \<gamma> (ofe_fields fe') p = False \<Longrightarrow> 
 guha_table_semantics \<gamma> (ft1 @ fe # ft2) p (Some (ofe_action fe))" |
"\<forall>fe \<in> set ft. \<gamma> (ofe_fields fe) p = False \<Longrightarrow>
 guha_table_semantics \<gamma> ft p None"

(* 
so\<dots> there's the possibility for a flow table with two matching entries.
I'm not so sure it is a good idea to model undefined behavior by nondeterministic but very defined behavior..
*)
lemma
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

lemma guha_equal_Action:
	assumes no: "no_overlaps \<gamma> ft"
	assumes spm: "OF_same_priority_match3 \<gamma> ft p = Action a"
	shows "guha_table_semantics \<gamma> ft p (Some a)"
proof -
	note spm[THEN OF_spm3_get_fe] then obtain fe where a: "ofe_action fe = a" and fein: "fe \<in> set ft" and feana: "OF_same_priority_match3_ana \<gamma> ft p = Action fe" by blast
	show ?thesis
		apply(rule guha_umstaendlich)
		apply(rule a[symmetric])
		apply(rule fein)
		using feana unfolding OF_same_priority_match3_ana_def
		apply(auto dest!: filter_singleton split: list.splits)
	done
qed

lemma guha_equal_NoAction:
	assumes no: "no_overlaps \<gamma> ft"
	assumes spm: "OF_same_priority_match3 \<gamma> ft p = NoAction"
	shows "guha_table_semantics \<gamma> ft p None"
using spm unfolding OF_same_priority_match3_def
by(auto simp add: filter_empty_conv OF_spm3_noa_none[OF no spm] intro: guha_table_semantics.intros(2) split: list.splits)

lemma
	assumes no: "no_overlaps \<gamma> ft"
	shows "guha_table_semantics \<gamma> ft p (ftb_to_option (OF_same_priority_match3 \<gamma> ft p))"
unfolding ftb_to_option_def
	apply(cases "(OF_same_priority_match3 \<gamma> ft p)")
	apply(simp add: guha_equal_Action[OF no])
	apply(simp add: guha_equal_NoAction[OF no])
	apply(subgoal_tac False, simp)
	using check_no_overlapI no no_overlap_not_unefined no_overlaps_defeq by fastforce

end