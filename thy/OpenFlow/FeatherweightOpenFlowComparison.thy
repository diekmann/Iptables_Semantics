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
	thus ?thesis using as by blast
qed

end