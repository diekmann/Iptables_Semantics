theory ReversePathFiltering
imports Routing_Table "../Simple_Firewall/Simple_Packet"
begin

text\<open>RFC3704 style RPF\<close>

text\<open>\begin{quote}The procedure is that the
   source address is looked up in the Forwarding Information Base (FIB)
   - and if the packet is received on the interface which would be used
   to forward the traffic to the source of the packet, it passes the
   check.\end{quote}\<close>
(* There's an iptables rpf in ./net/ipv4/netfilter/ipt_rpfilter.c:35 
   More interesting is ./net/ipv4/fib_frontend.c:323 though
*)
definition "rpf_strict rtbl p \<equiv> output_iface (routing_table_semantics rtbl (p_src p)) = p_iiface p"

text\<open>\begin{quote}
   Feasible Path Reverse Path Forwarding (Feasible RPF) is an extension
   of Strict RPF.  The source address is still looked up in the FIB (or
   an equivalent, RPF-specific table) but instead of just inserting one
   best route there, the alternative paths (if any) have been added as
   well, and are valid for consideration.
\end{quote}\<close>
definition "rpf_feasible rtbl p \<equiv> \<exists>rr \<in> set rtbl.
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_oiface rr = p_iiface p"
definition "rpf_loose rtbl p \<equiv> \<exists>rr \<in> set rtbl. prefix_match_semantics (routing_match rr) (p_src p)"
definition "rpf_loose_ign_default rtbl p \<equiv> \<exists>rr \<in> set rtbl. 
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_match rr \<noteq> PrefixMatch 0 0"
text\<open>Note that this clearly exposes a weakness of our models: The FIB we modelled really only considers the routing table. We have not taken care to avoid un-routable address spaces. As such, @{const rpf_loose} is not very useful:\<close>
lemma "valid_prefixes rtbl \<Longrightarrow> has_default_route rtbl \<Longrightarrow> \<forall>p. rpf_loose rtbl p"
  by(induction rtbl) (auto simp add: valid_prefixes_alt_def zero_prefix_match_all rpf_loose_def[abs_def])

text\<open>One might ask: What (nonstandard) formulations of reverse path filtering are possible? This is an example that fits into the hierarchy, between feasible and strict RPF:\<close>
definition "rpf_semifeasible    rtbl p \<equiv> \<exists>rr \<in> set rtbl. 
  prefix_match_semantics (routing_match rr) (p_src p) \<and> routing_oiface rr = p_iiface p (* rule applies and routes to right interface *)
\<and> (\<forall>ra \<in> set rtbl. routing_prefix ra > routing_prefix rr \<longrightarrow>  \<not>prefix_match_semantics (routing_match ra) (p_src p)) (* no rules more specific than this one apply *)
"
text\<open>Unlinke feasible RPF, this only considers alternate routes if these routes have the same prefix length as the best route.\<close>
text\<open>The insight we are not going to prove here is: There is an infinite number of levels in this hierarchy.
(For example we might only allow alternate routes whose metric difference it at max @{term n}. However, there are more interesting formulations of RPF that we did not discuss.)\<close>

lemma "prefix_match_semantics (PrefixMatch 0 0) any" by (simp add: valid_prefix_00 zero_prefix_match_all)

text\<open>The hierarchy unfolds:\<close>
lemma 
  assumes "valid_prefixes rtbl" "is_longest_prefix_routing rtbl" "has_default_route rtbl" "unambiguous_routing rtbl"
  shows "rpf_strict rtbl p \<Longrightarrow> rpf_semifeasible rtbl p"
unfolding rpf_semifeasible_def rpf_strict_def
(* meh, the thing is subtly different enough from existential_routing that we can't use that directly *)
proof goal_cases
  case 1
  then obtain act where *: "routing_table_semantics rtbl (p_src p) = act" by blast
  with existential_routing[OF assms]
  have ex: "(\<exists>rr\<in>set rtbl.
        prefix_match_semantics (routing_match rr) (p_src p) \<and>
        output_iface (routing_action rr) = output_iface act \<and> (\<forall>ra\<in>set rtbl. routing_rule_sort_key ra < routing_rule_sort_key rr \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) (p_src p)))" by auto
  from * 1 have act: "p_iiface p = output_iface act" by simp
  have **: "routing_prefix rr < routing_prefix ra \<Longrightarrow> routing_rule_sort_key ra < routing_rule_sort_key rr" for rr ra by(auto simp add: act routing_rule_sort_key_def linord_helper_less int_of_nat_def)
  from ex show ?case using ** by (simp add: act) blast
qed

lemma "rpf_semifeasible rtbl p \<Longrightarrow> rpf_feasible rtbl p"
unfolding rpf_semifeasible_def rpf_feasible_def by blast
lemma "rpf_feasible rtbl p \<Longrightarrow> rpf_loose rtbl p"
unfolding rpf_loose_def rpf_feasible_def by blast
lemma "rpf_loose_ign_default rtbl p \<Longrightarrow> rpf_loose rtbl p"
unfolding rpf_loose_def rpf_loose_ign_default_def by blast
text\<open>Unfortunately, nothing stronger can be said about @{const rpf_loose_ign_default}:\<close>
context begin
private definition "all_valid rtbl \<equiv> valid_prefixes rtbl \<and> is_longest_prefix_routing rtbl \<and> has_default_route rtbl \<and> unambiguous_routing rtbl" 

lemma "\<exists>rtbl :: 'a :: len prefix_routing. all_valid rtbl \<and> (\<forall>p. \<not>rpf_loose_ign_default rtbl p) \<and> (\<exists>p :: 'a simple_packet. rpf_strict rtbl p)" (is "\<exists>x. ?t1 x") 
text\<open>Read: There are routing tables where @{const rpf_loose_ign_default} is strongly stricter than @{const rpf_strict}.\<close>
proof text\<open>The catch here is that the routing table only containing the default rule will forbid all packets with @{term rpf_loose_ign_default}.\<close>
  have "rpf_strict [
    \<lparr>routing_match = PrefixMatch 0 0, metric = 418, routing_action = \<lparr>output_iface = ''e'', next_hop = Some 1\<rparr>\<rparr>] 
    \<lparr> p_iiface = ''e'', p_oiface = '''', p_src = 0, p_dst = 0 :: 'a word, p_proto = TCP, p_sport = 0, p_dport = 0, p_tcp_flags = {}, p_payload = '''' \<rparr>"
  unfolding rpf_strict_def by(simp add: valid_prefix_00 zero_prefix_match_all)
  thus "?t1 [\<lparr>routing_match = PrefixMatch 0 0, metric = 418, routing_action = \<lparr>output_iface = ''e'', next_hop = Some 1\<rparr>\<rparr>]"
  unfolding rpf_loose_ign_default_def unfolding all_valid_def by (auto simp add: valid_prefixes_alt_def valid_prefix_00 is_longest_prefix_routing_def unambiguous_routing_code)  
qed

lemma
  shows "\<exists>rtbl :: 32 prefix_routing. all_valid rtbl \<and> (\<forall>p. rpf_loose rtbl p \<longleftrightarrow> rpf_loose_ign_default rtbl p)" (is "\<exists>x. _ \<and> (\<forall>p. ?t2 x p)")
  text\<open>Read: There are routing tables where @{const rpf_loose_ign_default} is just as weak as @{const rpf_loose}. (Even though they contain a default route, mind you!)\<close>
  text\<open>And yes, this could be shown for a more general type, but I suspect that would be a lot more annoying.\<close>
proof (intro exI allI conjI) text\<open>The catch here is that the functionality of the default route can entirely be taken over by other routes.\<close>
    let ?c = "[\<lparr>routing_match = PrefixMatch 0 1, metric = 0, routing_action = \<lparr>output_iface = ''e'', next_hop = None\<rparr>\<rparr>,
        \<lparr>routing_match = PrefixMatch 2147483648 1, metric = 0, routing_action = \<lparr>output_iface = ''e'', next_hop = None\<rparr>\<rparr>,
        \<lparr>routing_match = PrefixMatch 0 0, metric = 0, routing_action = \<lparr>output_iface = ''e'', next_hop = None\<rparr>\<rparr>] :: 32 prefix_routing"
    show "all_valid ?c" by eval (* I'd like to make this part of the lemma, but\<dots> Isabelle bug? *)
    have l: "~~ mask 31 && p = 0 \<Longrightarrow> prefix_match_semantics (PrefixMatch 0 1) p" for p :: "32 word" unfolding prefix_match_semantics_def pfxm_prefix_def pfxm_mask_def by simp
    have m: "~~(mask 31 :: 32 word) = 0x80000000" by eval
    have s: "(1 << 31) && p \<noteq> 0 \<Longrightarrow> (1 << 31) && p = 1 << 31" for p :: "32 word"
      unfolding word_bw_comms word_and_1_shiftl by(simp split: if_splits)
    have u: "~~ mask 31 && p \<noteq> 0 \<Longrightarrow> prefix_match_semantics (PrefixMatch 0x80000000 1)  p" for p :: "32 word" 
      unfolding prefix_match_semantics_def pfxm_prefix_def pfxm_mask_def using s by(simp add: m)
    show "?t2 ?c p" for p unfolding rpf_loose_def rpf_loose_ign_default_def
      by(cases "~~ mask 31 && p_src p = 0"; (drule l | drule u); simp)
qed
end

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

definition "rpf_semifeasible_round rtbl n space \<equiv>
let res = [(routing_oiface rr, wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space) . rr \<leftarrow> rtbl, routing_prefix rr = n] in (res,
wordinterval_setminus space (wordinterval_Union (map snd res)))"

primrec rpf_semifeasible_assignment_dups where
"rpf_semifeasible_assignment_dups _ _ 0 = []" |
"rpf_semifeasible_assignment_dups rtbl space (Suc n) = (let 
  (res,rspace) = rpf_semifeasible_round rtbl n space in
  res @ rpf_semifeasible_assignment_dups rtbl rspace n)"                                       

definition "rpf_semifeasible_wi (rtbl::'a :: len routing_rule list) \<equiv> reduce_range_destination 
  (rpf_semifeasible_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0)))"
text\<open>One might think that @{term "Suc (len_of TYPE ('a :: len))"} is the right length of prefix to start from.
Unfortunately, @{const valid_prefix} does not ensure that the prefix isn't longer than what the type permits, 
and so you'd miss those broken prefixes. Nobody cares, except for the proofs.
\<close>

lemma rpf_semifeasible_round_fst: "(\<exists>rr \<in> set rtbl. routing_prefix rr = n \<and> rspace = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space \<and> ifce = routing_oiface rr)
   \<longleftrightarrow> (\<exists>(p,spc) \<in> set (fst (rpf_semifeasible_round rtbl n space)). ifce = p \<and> rspace = spc)"
   unfolding rpf_semifeasible_round_def Let_def fst_conv by(simp; blast)

lemma rpf_semifeasible_round_snd: "rr \<in> set rtbl \<Longrightarrow> routing_prefix rr = n \<Longrightarrow> wordinterval_empty (wordinterval_intersection (snd (rpf_semifeasible_round rtbl n space)) (prefix_to_wordinterval (routing_match rr)))"
  unfolding rpf_semifeasible_round_def Let_def snd_conv by(auto simp add: wordinterval_Union)

lemma rpf_semifeasible_round_snd': 
  assumes vpfx: "valid_prefixes rtbl"
  assumes nm: "\<forall>ra\<in>set rtbl. routing_prefix ra = n \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) ip"
  assumes e: "ip \<in> wordinterval_to_set space"
  shows "ip \<in> wordinterval_to_set (snd (rpf_semifeasible_round rtbl n space))"
proof -
  have " \<forall>x\<in>set rtbl \<inter> {rr. pfxm_length (routing_match rr) = n}. ip \<notin> prefix_to_wordset (routing_match x)"
    using nm prefix_match_semantics_wordset valid_prefixes_alt_def vpfx by fastforce
  with e show ?thesis by(simp add:  rpf_semifeasible_round_def Let_def wordinterval_Union)
qed

lemma ex_prod_splitI: "\<exists>(a,b) \<in> S. P (a,b) \<Longrightarrow> \<exists>a \<in> S. P a" by simp

lemma rpf_semifeasible_assignment_subset: "(p, spc) \<in> set (rpf_semifeasible_assignment_dups rtbl space n) \<Longrightarrow> wordinterval_subset spc space"
proof(induction n arbitrary: space)
  case (Suc n)
  from Suc.prems[unfolded rpf_semifeasible_assignment_dups.simps Let_def case_prod_unfold set_append Set.Un_iff]
  have "(p, spc) \<in> set (fst (rpf_semifeasible_round rtbl n space)) \<or> (p, spc) \<in> set (rpf_semifeasible_assignment_dups rtbl (snd (rpf_semifeasible_round rtbl n space)) n)" .
  thus ?case proof(elim disjE, goal_cases)
    case 1 thus ?case unfolding rpf_semifeasible_round_def Let_def fst_conv by force
  next
    case 2 with Suc.IH have "wordinterval_subset spc (snd (rpf_semifeasible_round rtbl n space))" .
    thus ?case unfolding rpf_semifeasible_round_def Let_def snd_conv by force
  qed
qed simp

lemma rpf_semifeasible_assignment_dups_fst: 
  assumes vpfx: "valid_prefixes rtbl" 
  assumes space: "ip \<in> wordinterval_to_set space"
shows "
    (\<exists>rr \<in> set rtbl. routing_prefix rr < n \<and> prefix_match_semantics (routing_match rr) ip \<and> ifce = routing_oiface rr \<and> 
    (\<forall>ra \<in> set rtbl.  routing_prefix ra < n \<longrightarrow> routing_prefix ra > routing_prefix rr \<longrightarrow>  \<not>prefix_match_semantics (routing_match ra) ip))
   \<longleftrightarrow> (\<exists>(p,spc) \<in> set (rpf_semifeasible_assignment_dups rtbl space n). ifce = p \<and> ip \<in> wordinterval_to_set spc)"
proof(rule iffI, goal_cases)
  case 1 show ?case proof(insert 1 space, elim bexE conjE, induction n arbitrary: space)
    case (Suc n rr)
    show ?case proof(cases "routing_prefix rr = n")
      case False
      with \<open>routing_prefix rr < Suc n\<close> have *: "routing_prefix rr < n" by linarith
      have **: "\<forall>ra\<in>set rtbl. routing_prefix ra < n \<longrightarrow> routing_prefix rr < routing_prefix ra \<longrightarrow> \<not> prefix_match_semantics (routing_match ra) ip"
        using Suc.prems(6) by simp
      have ***: "ip \<in> wordinterval_to_set (snd (rpf_semifeasible_round rtbl n space))" 
        by (simp add: * Suc.prems(1) Suc.prems(6) rpf_semifeasible_round_snd' vpfx) (* it werks™ *)
      note Suc.IH[OF *** Suc.prems(2) * Suc.prems(4-5) **]
      thus ?thesis by(auto simp add: case_prod_unfold Let_def)
    next
      case True
      have "(\<exists>rra\<in>set rtbl.
      routing_prefix rra = n \<and>
      wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space =
      wordinterval_intersection (prefix_to_wordinterval (routing_match rra)) space \<and>
      ifce = routing_oiface rra)" by(intro bexI[where x=rr]; simp add: Suc.prems True)
      with rpf_semifeasible_round_fst obtain p spc where pspc:
        "(p, spc)\<in>set (fst (rpf_semifeasible_round rtbl n space))" "ifce = p"
        "spc = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space" by fast
      have m: "ip \<in> prefix_to_wordset (routing_match rr)"
        using Suc.prems(2) Suc.prems(4) prefix_match_semantics_wordset valid_prefixes_alt_def vpfx by blast
      show ?thesis unfolding rpf_semifeasible_assignment_dups.simps Let_def case_prod_unfold fst_conv set_append bex_Un
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
    "(p, spc)\<in>set (rpf_semifeasible_assignment_dups rtbl space n)" "ifce = p" "ip \<in> wordinterval_to_set spc" by blast
  with space show ?case proof(induction n arbitrary: space)
    case 0 thus ?case by simp
  next
    case (Suc n)
    from Suc.prems(2)[unfolded rpf_semifeasible_assignment_dups.simps Let_def case_prod_unfold fst_conv set_append Set.Un_iff]
    have *: "(p, spc) \<in> set (fst (rpf_semifeasible_round rtbl n space)) \<or> (p, spc) \<in> set (rpf_semifeasible_assignment_dups rtbl (snd (rpf_semifeasible_round rtbl n space)) n)" .
    show ?case proof(cases "\<exists>ra\<in>set rtbl. routing_prefix ra = n \<and> prefix_match_semantics (routing_match ra) ip")
      case True
      hence "\<not>(p, spc) \<in> set (rpf_semifeasible_assignment_dups rtbl (snd (rpf_semifeasible_round rtbl n space)) n)" (is "\<not>?f")
      proof(intro notI)
        from True guess ra .. note ra = this
        hence *: "ip \<in> prefix_to_wordset (routing_match ra)" using vpfx using prefix_match_semantics_wordset valid_prefixes_alt_def by blast
        with Suc.prems have "prefix_to_wordset (routing_match ra) \<inter> wordinterval_to_set spc \<noteq> {}" by blast
        from rpf_semifeasible_round_snd[OF ra(1) ra(2)[THEN conjunct1]] 
        have **: "wordinterval_empty (wordinterval_intersection (snd (rpf_semifeasible_round rtbl n space)) (prefix_to_wordinterval (routing_match ra)))" .
        assume ?f
        with rpf_semifeasible_assignment_subset have ***: "wordinterval_subset spc (snd (rpf_semifeasible_round rtbl n space))" .
        show False using Suc.prems(4) * **  *** by fastforce
      qed
      hence True': "(p, spc) \<in> set (fst (rpf_semifeasible_round rtbl n space))" using * by blast
      note True' Suc.prems(1,3-) rpf_semifeasible_round_fst[of rtbl n spc space ifce]
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
      have "(p, spc) \<notin> set (fst (rpf_semifeasible_round rtbl n space))" (is "\<not>?f")
      proof(intro notI)
        assume ?f with rpf_semifeasible_round_fst[of rtbl n spc space ifce] Suc.prems(3)
        obtain rr where rr: "rr\<in>set rtbl"
        "routing_prefix rr = n" "spc = wordinterval_intersection (prefix_to_wordinterval (routing_match rr)) space" "ifce = routing_oiface rr"  by blast
        hence "prefix_match_semantics (routing_match rr) ip" using vpfx Suc.prems(4) 
          using prefix_match_semantics_wordset valid_prefixes_alt_def Int_iff prefix_to_wordinterval_set_eq wordinterval_intersection_set_eq by auto
        with False rr show False by blast
      qed
      with * have *: "(p, spc) \<in> set (rpf_semifeasible_assignment_dups rtbl (snd (rpf_semifeasible_round rtbl n space)) n)" by clarify
      have **: "ip \<in> wordinterval_to_set (snd (rpf_semifeasible_round rtbl n space))" using Suc.prems(4) * rpf_semifeasible_assignment_subset by fastforce
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


corollary rpf_semifeasible_correct: 
  assumes vpfx: "valid_prefixes rtbl"
  shows "rpf_semifeasible rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_semifeasible_wi rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
unfolding rpf_semifeasible_def rpf_semifeasible_wi_def
unfolding reduce_range_destination_def Let_def comp_def
proof(goal_cases)
  case 1 
  let ?rs = "rpf_semifeasible_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))" (* rs wie rattenschwanz *)
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
  with rpf_semifeasible_assignment_dups_fst[OF vpfx, of "p_src p" wordinterval_UNIV "Suc (fold max (map routing_prefix rtbl) 0)" "p_iiface p", 
      unfolded wordinterval_UNIV_set_eq, OF UNIV_I]
  have "?l = (\<exists>(pa, spc)\<in>set ?rs.
        p_iiface p = pa \<and> p_src p \<in> wordinterval_to_set spc)" by linarith
  moreover have "(\<exists>(pa, spc)\<in>set (rpf_semifeasible_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))).
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
                              (map snd [x\<leftarrow>rpf_semifeasible_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0)) . p = fst x])))
                 (remdups (map fst (rpf_semifeasible_assignment_dups rtbl wordinterval_UNIV (Suc (fold max (map routing_prefix rtbl) 0))))))"
     "p_iiface p = k" " p_src p \<in> wordinterval_to_set l" by blast
    from kl have "k \<in> set (remdups (map fst ?rs))" by auto
    from kl have "l = wordinterval_Union (map snd [x\<leftarrow>?rs . k = fst x])" by fastforce
    with kl(3) obtain lo where lo: "p_src p \<in> wordinterval_to_set lo" "(k, lo) \<in>  set ?rs" by(auto simp add: wordinterval_Union)
    show ?l1 by(intro bexI[where x="(k,lo)"]) (simp add: lo kl, fact lo)
  qed
  ultimately show ?case by linarith
  qed
qed

definition "rpf_feasible_wi rtbl \<equiv> reduce_range_destination (map (\<lambda>rr. (routing_oiface rr, prefix_to_wordinterval (routing_match rr))) rtbl)"

lemma rpf_feasible_correct:
  assumes vpfx: "valid_prefixes rtbl"
  shows "rpf_feasible rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_feasible_wi rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
  using vpfx unfolding reduce_range_destination_def rpf_feasible_def rpf_feasible_wi_def
  by(force simp add: wordinterval_Union prefix_match_semantics_wordset valid_prefixes_alt_def)

definition "rpf_loose_wi ifs rtbl \<equiv> let routed_space = foldr (wordinterval_union \<circ> prefix_to_wordinterval \<circ> routing_match) rtbl Empty_WordInterval in [(iface,routed_space). iface \<leftarrow> ifs]"
lemma rpf_loose_correct:
  assumes vpfx: "valid_prefixes rtbl"
  assumes ifsane: "p_iiface p \<in> set ifs"
  shows "rpf_loose rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_loose_wi ifs rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
proof -
  from vpfx have *: "(\<exists>rr\<in>set rtbl. prefix_match_semantics (routing_match rr) (p )) =
        (p  \<in> wordinterval_to_set (foldr (wordinterval_union \<circ> prefix_to_wordinterval \<circ> routing_match) rtbl Empty_WordInterval))" for p
  proof(induction rtbl)
    case (Cons rr rtbl)
    have vpfx: "valid_prefix (routing_match rr)" using Cons.prems valid_prefixes_split by blast
    show ?case proof(cases "prefix_match_semantics (routing_match rr) p")
      case True thus ?thesis by(simp add: prefix_match_semantics_wordset[OF vpfx])
    next
      have vpfxs: "valid_prefixes rtbl" using Cons.prems valid_prefixes_split by blast 
      case False
      with vpfx have ni: "p \<notin> prefix_to_wordset (routing_match rr)" using prefix_match_semantics_wordset by blast
      with False show ?thesis using Cons.IH[OF vpfxs] by simp
    qed
  qed simp
  thus ?thesis
  using vpfx ifsane
  unfolding rpf_loose_wi_def rpf_loose_def by simp
qed

definition "rpf_loose_ign_default_wi ifs \<equiv> rpf_loose_wi ifs \<circ> filter (\<lambda>rr. routing_match rr \<noteq> PrefixMatch 0 0)"
lemma rpf_loose_ign_default_correct:
  assumes vpfx: "valid_prefixes rtbl"
  assumes ifsane: "p_iiface p \<in> set ifs"
  shows "rpf_loose_ign_default rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_loose_ign_default_wi ifs rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
proof -
  let ?rtf = "filter (\<lambda>rr. routing_match rr \<noteq> PrefixMatch 0 0)"
  have f: "rpf_loose_ign_default rtbl p = rpf_loose (?rtf rtbl) p" unfolding rpf_loose_def rpf_loose_ign_default_def by auto
  from vpfx have fpfx: "valid_prefixes (?rtf rtbl)" unfolding valid_prefixes_alt_def by simp
  show ?thesis
    unfolding rpf_loose_ign_default_wi_def comp_def f
    using rpf_loose_correct[OF fpfx ifsane] .
qed

datatype rpf_type = RPF_Strict | RPF_Feasible | RPF_Loose | RPF_LooseIgnDef | RPF_Semifeasible
primrec rpf_def_lookup where
"rpf_def_lookup RPF_Strict = rpf_strict" |
"rpf_def_lookup RPF_Feasible = rpf_feasible" |
"rpf_def_lookup RPF_Loose = rpf_loose" |
"rpf_def_lookup RPF_LooseIgnDef = rpf_loose_ign_default" |
"rpf_def_lookup RPF_Semifeasible = rpf_semifeasible"
fun rpf_wi_lookup where
"rpf_wi_lookup RPF_Strict _ = routing_ipassmt_wi" |
"rpf_wi_lookup RPF_Feasible _ = rpf_feasible_wi" |
"rpf_wi_lookup RPF_Loose ifs = rpf_loose_wi ifs" |
"rpf_wi_lookup RPF_LooseIgnDef ifs = rpf_loose_ign_default_wi ifs" |
"rpf_wi_lookup RPF_Semifeasible _ = rpf_semifeasible_wi"

theorem
assumes vpfx: "valid_prefixes rtbl"
assumes ifsane: "rpf \<in> {RPF_Loose, RPF_LooseIgnDef} \<Longrightarrow> p_iiface p \<in> set ifs"
shows "rpf_def_lookup rpf rtbl p \<longleftrightarrow> (\<exists>(k,l) \<in> set (rpf_wi_lookup rpf ifs rtbl). p_iiface p = k \<and> p_src p \<in> wordinterval_to_set l)"
using assms by(cases rpf; simp_all add: rpf_strict_correct rpf_semifeasible_correct rpf_feasible_correct rpf_loose_correct rpf_loose_ign_default_correct)

end