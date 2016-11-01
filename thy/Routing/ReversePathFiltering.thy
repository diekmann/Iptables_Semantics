theory ReversePathFiltering
imports Routing_Table "../Simple_Firewall/Simple_Packet"
begin

abbreviation "routing_prefix r \<equiv> pfxm_length (routing_match r)"

definition "rpf_strict rtbl p \<equiv> output_iface (routing_table_semantics rtbl (p_src p)) = p_iiface p"
definition "rpf_lax    rtbl p \<equiv> \<exists>rr \<in> set rtbl. 
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_oiface rr = p_iiface p (* rule applies and routes to right interface *)
\<and> (\<forall>ra \<in> set rtbl. routing_prefix ra > routing_prefix rr \<longrightarrow>  \<not>prefix_match_semantics (routing_match ra) (p_src p)) (* no rules more specific than this one apply *)
"

corollary rpf_strict_correct: 
assumes vpfx: "valid_prefixes rtbl"
shows "rpf_strict rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (routing_ipassmt_wi rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
unfolding rpf_strict_def
  apply(intro iffI[rotated])
  apply(clarify)
  apply(auto dest: routing_ipassmt_wi_sound[OF vpfx])[1]
  apply(subst(asm) routing_ipassmt_wi[OF vpfx])
  apply blast
done

definition "rpf_lax_round rtbl n space \<equiv>
let res = [(routing_oiface rr, wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space) . rr \<leftarrow> rtbl, routing_prefix rr = n] in (res,
wordinterval_setminus space (wordinterval_Union (map snd res)))"

primrec rpf_lax_assignment_dups where
"rpf_lax_assignment_dups _ _ 0 = []" |
"rpf_lax_assignment_dups rtbl space (Suc n) = (let 
  (res,rspace) = rpf_lax_round rtbl n space in
  res @ rpf_lax_assignment_dups rtbl rspace n)"                                       

definition "rpf_lax_wi (rtbl::'a :: len routing_rule list) \<equiv> reduce_range_destination 
  (rpf_lax_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0)))"
text\<open>One might think that @{term "Suc (len_of TYPE ('a :: len))"} is the right length of prefix to start from.
Unfortunately, @{const valid_prefix} does not ensure that the prefix isn't longer than what the type permits, 
and so you'd miss those broken prefixes. Nobody cares, except for the proofs.
\<close>

lemma rpf_lax_round_fst: "(\<exists>rr \<in> set rtbl. routing_prefix rr = n \<and> rspace = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space \<and> ifce = routing_oiface rr)
   \<longleftrightarrow> (\<exists>(p,spc) \<in> set (fst (rpf_lax_round rtbl n space)). ifce = p \<and> rspace = spc)"
   unfolding rpf_lax_round_def Let_def fst_conv by(simp; blast)

lemma rpf_lax_round_snd: "rr \<in> set rtbl \<Longrightarrow> routing_prefix rr = n \<Longrightarrow> wordinterval_empty (wordinterval_intersection (snd (rpf_lax_round rtbl n space)) (prefix_to_wordinterval (routing_match rr)))"
  unfolding rpf_lax_round_def Let_def snd_conv by(auto simp add: wordinterval_Union)

lemma rpf_lax_round_snd': 
  assumes vpfx: "valid_prefixes rtbl"
  assumes nm: "\<forall>ra\<in>set rtbl. routing_prefix ra = n \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) ip"
  assumes e: "ip \<in> wordinterval_to_set space"
  shows "ip \<in> wordinterval_to_set (snd (rpf_lax_round rtbl n space))"
proof -
  have " \<forall>x\<in>set rtbl \<inter> {rr. pfxm_length (routing_match rr) = n}. ip \<notin> prefix_to_wordset (routing_match x)"
    using nm prefix_match_semantics_wordset valid_prefixes_alt_def vpfx by fastforce
  with e show ?thesis by(simp add:  rpf_lax_round_def Let_def wordinterval_Union)
qed

lemma ex_prod_splitI: "\<exists>(a,b) \<in> S. P (a,b) \<Longrightarrow> \<exists>a \<in> S. P a" by simp

lemma rpf_lax_assignment_subset: "(p, spc) \<in> set (rpf_lax_assignment_dups rtbl space n) \<Longrightarrow> wordinterval_subset spc space"
proof(induction n arbitrary: space)
  case (Suc n)
  from Suc.prems[unfolded rpf_lax_assignment_dups.simps Let_def case_prod_unfold set_append Set.Un_iff]
  have "(p, spc) \<in> set (fst (rpf_lax_round rtbl n space)) \<or> (p, spc) \<in> set (rpf_lax_assignment_dups rtbl (snd (rpf_lax_round rtbl n space)) n)" .
  thus ?case proof(elim disjE, goal_cases)
    case 1 thus ?case unfolding rpf_lax_round_def Let_def fst_conv by force
  next
    case 2 with Suc.IH have "wordinterval_subset spc (snd (rpf_lax_round rtbl n space))" .
    thus ?case unfolding rpf_lax_round_def Let_def snd_conv by force
  qed
qed simp

lemma rpf_lax_assignment_dups_fst: 
  assumes vpfx: "valid_prefixes rtbl" 
  assumes space: "ip \<in> wordinterval_to_set space"
shows "
    (\<exists>rr \<in> set rtbl. routing_prefix rr < n \<and> prefix_match_semantics (routing_match rr) ip \<and> ifce = routing_oiface rr \<and> 
    (\<forall>ra \<in> set rtbl.  routing_prefix ra < n \<longrightarrow> routing_prefix ra > routing_prefix rr \<longrightarrow>  \<not>prefix_match_semantics (routing_match ra) ip))
   \<longleftrightarrow> (\<exists>(p,spc) \<in> set (rpf_lax_assignment_dups rtbl space n). ifce = p \<and> ip \<in> wordinterval_to_set spc)"
proof(rule iffI, goal_cases)
  case 1 show ?case proof(insert 1 space, elim bexE conjE, induction n arbitrary: space)
    case (Suc n rr)
    show ?case proof(cases "routing_prefix rr = n")
      case False
      with \<open>routing_prefix rr < Suc n\<close> have *: "routing_prefix rr < n" by linarith
      have **: "\<forall>ra\<in>set rtbl. routing_prefix ra < n \<longrightarrow> routing_prefix rr < routing_prefix ra \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) ip"
        using Suc.prems(6) by simp
      have ***: "ip \<in> wordinterval_to_set (snd (rpf_lax_round rtbl n space))" 
        by (simp add: * Suc.prems(1) Suc.prems(6) rpf_lax_round_snd' vpfx) (* it werks™ *)
      note Suc.IH[OF *** Suc.prems(2) * Suc.prems(4-5) **]
      thus ?thesis by(auto simp add: case_prod_unfold Let_def)
    next
      case True
      have "(\<exists>rra\<in>set rtbl.
      routing_prefix rra = n \<and>
      wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space =
      wordinterval_intersection (prefix_to_wordinterval (routing_match rra)) space \<and>
      ifce = routing_oiface rra)" by(intro bexI[where x=rr]; simp add: Suc.prems True)
      with rpf_lax_round_fst obtain p spc where pspc:
        "(p, spc)\<in>set (fst (rpf_lax_round rtbl n space))" "ifce = p"
        "spc = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space" by fast
      have m: "ip \<in> prefix_to_wordset (routing_match rr)"
        using Suc.prems(2) Suc.prems(4) prefix_match_semantics_wordset valid_prefixes_alt_def vpfx by blast
      show ?thesis unfolding rpf_lax_assignment_dups.simps Let_def case_prod_unfold fst_conv set_append bex_Un
        apply(intro disjI1)
        apply(rule ex_prod_splitI)
        apply(rule bexI[where x="(p,spc)",rotated])
        apply(fact pspc)
        apply(simp add: pspc m Suc.prems(1))
      done
    qed
  qed(subgoal_tac False; simp; fail)
next
  case 2
  then obtain p spc where 
    "(p, spc)\<in>set (rpf_lax_assignment_dups rtbl space n)" "ifce = p" "ip \<in> wordinterval_to_set spc" by blast
  with space show ?case proof(induction n arbitrary: space)
    case 0 thus ?case by simp
  next
    case (Suc n)
    from Suc.prems(2)[unfolded rpf_lax_assignment_dups.simps Let_def case_prod_unfold fst_conv set_append Set.Un_iff]
    have *: "(p, spc) \<in> set (fst (rpf_lax_round rtbl n space)) \<or> (p, spc) \<in> set (rpf_lax_assignment_dups rtbl (snd (rpf_lax_round rtbl n space)) n)" .
    show ?case proof(cases "\<exists>ra\<in>set rtbl. routing_prefix ra = n \<and> prefix_match_semantics (routing_match ra) ip")
      case True
      hence "\<not>(p, spc) \<in> set (rpf_lax_assignment_dups rtbl (snd (rpf_lax_round rtbl n space)) n)" (is "\<not>?f")
      proof(intro notI)
        from True guess ra .. note ra = this
        hence *: "ip \<in> prefix_to_wordset (routing_match ra)" using vpfx using prefix_match_semantics_wordset valid_prefixes_alt_def by blast
        with Suc.prems have "prefix_to_wordset (routing_match ra) \<inter> wordinterval_to_set spc \<noteq> {}" by blast
        from rpf_lax_round_snd[OF ra(1) ra(2)[THEN conjunct1]] 
        have **: "wordinterval_empty (wordinterval_intersection (snd (rpf_lax_round rtbl n space)) (prefix_to_wordinterval (routing_match ra)))" .
        assume ?f
        with rpf_lax_assignment_subset have ***: "wordinterval_subset spc (snd (rpf_lax_round rtbl n space))" .
        show False using Suc.prems(4) * **  *** by fastforce
      qed
      hence True': "(p, spc) \<in> set (fst (rpf_lax_round rtbl n space))" using * by blast
      note True' Suc.prems(1,3-) rpf_lax_round_fst[of rtbl n spc space ifce]
      then obtain rr where rr: "rr\<in>set rtbl"
        "routing_prefix rr = n"
        "spc = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space"
        "p = routing_oiface rr" by blast
      have a: "prefix_match_semantics (routing_match rr) ip" 
        using Suc.prems(4) prefix_match_semantics_wordset rr(1) rr(3) valid_prefixes_alt_def vpfx by fastforce
      show ?thesis
        by(intro bexI[where x=rr]) (simp_all add: rr Suc a)
    next
      case False
      have "(p, spc) \<notin> set (fst (rpf_lax_round rtbl n space))" (is "\<not>?f")
      proof(intro notI)
        assume ?f with rpf_lax_round_fst[of rtbl n spc space ifce] Suc.prems(3)
        obtain rr where rr: "rr\<in>set rtbl"
        "routing_prefix rr = n" "spc = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space" "ifce = routing_oiface rr"  by blast
        hence "prefix_match_semantics (routing_match rr) ip" using vpfx Suc.prems(4) 
          using prefix_match_semantics_wordset valid_prefixes_alt_def Int_iff prefix_to_wordinterval_set_eq wordinterval_intersection_set_eq by auto
        with False rr show False by blast
      qed
      with * have *: "(p, spc) \<in> set (rpf_lax_assignment_dups rtbl (snd (rpf_lax_round rtbl n space)) n)" by clarify
      have **: "ip \<in> wordinterval_to_set (snd (rpf_lax_round rtbl n space))" using Suc.prems(4) * rpf_lax_assignment_subset by fastforce
      from Suc.IH[OF ** * Suc.prems(3,4)] obtain rr where rr:
        "rr\<in>set rtbl"
        "routing_prefix rr < n"
        "prefix_match_semantics (routing_match rr) ip"
        "ifce = routing_oiface rr"
        "(\<forall>ra\<in>set rtbl. routing_prefix ra < n \<longrightarrow> routing_prefix rr < routing_prefix ra \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) ip)" by blast
      show ?thesis
        apply(intro bexI[where x=rr])
        apply(simp_all add: rr)
        apply(intro conjI)
        using rr(2) apply(simp;fail)
        using rr(5) False apply fastforce
      done
    qed
  qed
qed

lemma fold_max_append: "fold max l (a::nat) = max a (fold max l 0)"
proof(induction l arbitrary: a)
  case (Cons l ls)
  show ?case by(simp add: Cons[of "(max l a) "] Cons[of l])
qed simp

lemma fold_max: "(f :: nat) \<in> set l \<Longrightarrow> f < Suc (fold max l 0)"
by(induction l; simp) (metis (no_types, lifting) fold_max_append lessI max_less_iff_conj not_less_eq) (* It werks™ *)


corollary rpf_lax_correct: 
  assumes vpfx: "valid_prefixes rtbl"
  shows "rpf_lax rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_lax_wi rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
unfolding rpf_lax_def rpf_lax_wi_def
unfolding reduce_range_destination_def Let_def comp_def
proof(goal_cases)
  case 1 
  let ?rs = "rpf_lax_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))" (* rs wie rattenschwanz *)
  show ?case (is "?l = ?r") proof -
  have maxpfx: "\<forall>ra\<in>set rtbl. routing_prefix ra < Suc (fold max (map routing_prefix rtbl) 0)"
    using fold_max[where l="map routing_prefix rtbl"] by simp
  have "?l = (\<exists>rr\<in>set rtbl.
      routing_prefix rr < Suc (fold max (map routing_prefix rtbl) 0) \<and>
      prefix_match_semantics (routing_match rr) (p_src p) \<and>
      p_iiface p = routing_oiface rr \<and>
      (\<forall>ra\<in>set rtbl.
          routing_prefix ra < Suc (fold max (map routing_prefix rtbl) 0) \<longrightarrow>
          routing_prefix rr < routing_prefix ra \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) (p_src p)))"
    using maxpfx by auto
  with rpf_lax_assignment_dups_fst[OF vpfx, of "p_src p" wordinterval_UNIV "Suc (fold max (map routing_prefix rtbl) 0)" "p_iiface p", 
      unfolded wordinterval_UNIV_set_eq, OF UNIV_I]
  have "?l = (\<exists>(pa, spc)\<in>set ?rs.
        p_iiface p = pa \<and> p_src p \<in> wordinterval_to_set spc)" by linarith
  moreover have "(\<exists>(pa, spc)\<in>set (rpf_lax_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))).
        p_iiface p = pa \<and> p_src p \<in> wordinterval_to_set spc) = ?r" (is "?l1 = ?r")
  proof
    assume ?l1
    then obtain pa spc where paspc: 
      "(pa, spc)\<in>set ?rs"
      "p_iiface p = pa" "p_src p \<in> wordinterval_to_set spc" by blast
    from this(1) have *: "pa \<in> set (remdups (map fst (?rs)))" by force
    let ?rss = "wordinterval_Union(map snd [x\<leftarrow>?rs. pa = fst x])"
    show ?r
      apply(intro bexI[where x="(pa, ?rss)"])
      subgoal
        apply(simp add: paspc(2))
        apply(unfold wordinterval_Union set_map set_filter UN_iff)
        apply(intro bexI[where x=spc])
        apply(simp add: paspc(3);fail)
        using paspc(1) apply force
      done
      subgoal
        using * by fastforce
    done
  next
    assume ?r
    then obtain k l where kl: "(k, l)\<in>set (map (\<lambda>p. (p, wordinterval_Union
                              (map snd [x\<leftarrow>rpf_lax_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0)) . p = fst x])))
                 (remdups (map fst (rpf_lax_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))))))"
     "p_iiface p = k" " p_src p \<in> wordinterval_to_set l" by blast
    from kl have "k \<in> set (remdups (map fst ?rs))" by auto
    from kl have "l = wordinterval_Union (map snd [x\<leftarrow>?rs . k = fst x])" by fastforce
    with kl(3) obtain lo where lo: "p_src p \<in> wordinterval_to_set lo" "(k, lo) \<in>  set ?rs" by(auto simp add: wordinterval_Union)
    show ?l1 by(intro bexI[where x="(k,lo)"]) (simp add: lo kl, fact lo)
  qed
  ultimately show ?case by linarith
  qed
qed

end