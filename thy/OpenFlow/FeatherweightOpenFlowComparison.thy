theory FeatherweightOpenFlowComparison
imports Semantics_OpenFlow
begin

(* compare to https://github.com/frenetic-lang/featherweight-openflow/blob/master/coq/OpenFlow/OpenFlowSemantics.v#L260 *)
inductive guha_match :: "('m, 'p) field_matcher \<Rightarrow> ('m, 'a) flowtable \<Rightarrow> (('m, 'a) flow_entry_match) \<Rightarrow> 'p \<Rightarrow> bool" where
"fe \<in> set ft \<Longrightarrow> \<gamma> (ofe_fields fe) p = True \<Longrightarrow> \<forall>fe' \<in> set ft. ofe_prio fe' > ofe_prio fe \<longrightarrow> \<gamma> (ofe_fields fe') p = False \<Longrightarrow> guha_match \<gamma> ft fe p"

(* so\<dots> there's the possibility for a flow table with two matching entries. yay\<dots>? *)
lemma 
	assumes "\<exists>ff1 ff2. ff1 \<noteq> ff2 \<and> \<gamma> ff1 p \<and> \<gamma> ff2 p"
	shows "\<exists>ft fe1 fe2. fe1 \<noteq> fe2 \<and> guha_match \<gamma> ft fe1 p \<and> guha_match \<gamma> ft fe2 p"
proof -
	from assms 
	obtain ff1 ff2 where ffs: "ff1 \<noteq> ff2" and m1: "\<gamma> ff1 p" and m2: "\<gamma> ff2 p" by (metis card2_eI mem_Collect_eq)
	let ?fe1 = "OFEntry 0 ff1 undefined"
	let ?fe2 = "OFEntry 0 ff2 undefined"
	let ?ft = "[?fe1, ?fe2]"
	have "guha_match \<gamma> ?ft ?fe1 p" "guha_match \<gamma> ?ft ?fe2 p" by(rule guha_match.intros; simp add: m1 m2)+
	thus ?thesis using ffs by blast
qed

end