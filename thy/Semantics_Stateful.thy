theory Semantics_Stateful
imports Semantics
begin

section\<open>Semantics Stateful\<close>

subsection\<open>Model 1 -- Curried Stateful Matcher\<close>

text\<open>Processing a packet with state can be modeled as follows:
  The state is @{term \<sigma>}.
  The primitive matcher @{term \<gamma>\<^sub>\<sigma>} is a curried function where the first argument is the state and
  it returns a stateless primitive matcher, i.e. @{term "\<gamma> = (\<gamma>\<^sub>\<sigma> \<sigma>)"}.
  With this stateless primitive matcher @{term \<gamma>}, the @{const iptables_bigstep} semantics are executed.
  As entry point, the iptables built-in chains @{term "''INPUT''"}, @{term "''OUTPUT''"}, and @{term "''FORWARD''"} with their
  default-policy (@{const Accept} or @{const Drop} are valid for iptables) are chosen.
  The semantics must yield a @{term "Decision X"}.
  Due to the default-policy, this is always the case if the ruleset is well-formed.
  When a decision is made, the state @{term \<sigma>} is updated.\<close>

inductive semantics_stateful ::
  "'a ruleset \<Rightarrow>
   ('\<sigma> \<Rightarrow> ('a, 'p) matcher) \<Rightarrow> (*matcher, first parameter is the state*)
   ('\<sigma> \<Rightarrow> final_decision \<Rightarrow> 'p \<Rightarrow> '\<sigma>) \<Rightarrow> (*state update function after firewall has decision for a packet*)
   '\<sigma> \<Rightarrow> (*Starting state. constant*)
   (string \<times> action) \<Rightarrow> (*The chain and default policy the firewall evaluates. For example ''FORWARD'', Drop*)
   'p list \<Rightarrow> (*packets to be processed*)
   ('p \<times> final_decision) list \<Rightarrow> (*packets which have been processed and their decision. ordered the same as the firewall processed them. oldest packet first*)
   '\<sigma> \<Rightarrow> (*final state*)
   bool" for \<Gamma> and \<gamma>\<^sub>\<sigma> and state_update and \<sigma>\<^sub>0 where
  --\<open>A list of packets @{term ps} waiting to be processed. Nothing has happened, start and final state are the same, the list of processed packets is empty.\<close>
  "semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) ps [] \<sigma>\<^sub>0" |

  --\<open>Processing one packet\<close>
  "semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) (p#ps) ps_processed \<sigma>' \<Longrightarrow>
   \<Gamma>,(\<gamma>\<^sub>\<sigma> \<sigma>'),p\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy],Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
    semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) ps (ps_processed@[(p, X)]) (state_update \<sigma>' X p)"


lemma semantics_stateful_intro_process_one: "semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) (p#ps) ps_processed_old \<sigma>_old \<Longrightarrow>
       \<Gamma>,\<gamma>\<^sub>\<sigma> \<sigma>_old,p\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy], Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
       \<sigma>' = state_upate \<sigma>_old X p \<Longrightarrow>
       ps_processed = ps_processed_old@[(p, X)] \<Longrightarrow>
       semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) ps ps_processed \<sigma>'"
  by(auto intro: semantics_stateful.intros)

lemma semantics_stateful_intro_start: "\<sigma>\<^sub>0 = \<sigma>' \<Longrightarrow> ps_processed = [] \<Longrightarrow>
       semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) ps ps_processed \<sigma>'"
  by(auto intro: semantics_stateful.intros)


text\<open>Example below\<close>

subsection\<open>Model 2 -- Packets Tagged with State Information\<close>

text\<open>In this model, the matcher is completely stateless but packets are previously tagged with
      (static) stateful information.\<close>

inductive semantics_stateful_packet_tagging ::
   "'a ruleset \<Rightarrow>
    ('a, 'ptagged) matcher \<Rightarrow>
    ('\<sigma> \<Rightarrow> 'p \<Rightarrow> 'ptagged) \<Rightarrow> (*taggs the packet accordig to the current state before processing by firewall*)
    ('\<sigma> \<Rightarrow> final_decision \<Rightarrow> 'p \<Rightarrow> '\<sigma>) \<Rightarrow> (*state updater*)
    '\<sigma> \<Rightarrow> (*Starting state. constant*)
    (string \<times> action) \<Rightarrow>
    'p list \<Rightarrow> (*packets to be processed*)
    ('p \<times> final_decision) list \<Rightarrow> (*packets which have been processed*)
    '\<sigma> \<Rightarrow> (*final state*)
    bool" for \<Gamma> and \<gamma> and packet_tagger and state_update and \<sigma>\<^sub>0 where
  "semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) ps [] \<sigma>\<^sub>0" |

  "semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) (p#ps) ps_processed \<sigma>' \<Longrightarrow>
   \<Gamma>,\<gamma>,(packet_tagger \<sigma>' p)\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy],Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
    semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_update \<sigma>\<^sub>0 (built_in_chain, default_policy) ps (ps_processed@[(p, X)]) (state_update \<sigma>' X p)"


lemma semantics_stateful_packet_tagging_intro_start: "\<sigma>\<^sub>0 = \<sigma>' \<Longrightarrow> ps_processed = [] \<Longrightarrow>
       semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) ps ps_processed \<sigma>'"
  by(auto intro: semantics_stateful_packet_tagging.intros)

lemma semantics_stateful_packet_tagging_intro_process_one:
      "semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) (p#ps) ps_processed_old \<sigma>_old \<Longrightarrow>
       \<Gamma>,\<gamma>,(packet_tagger \<sigma>_old p)\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy], Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
       \<sigma>' = state_upate \<sigma>_old X p \<Longrightarrow>
       ps_processed = ps_processed_old@[(p, X)] \<Longrightarrow>
       semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_upate \<sigma>\<^sub>0 (built_in_chain, default_policy) ps ps_processed \<sigma>'"
  by(auto intro: semantics_stateful_packet_tagging.intros)


lemma semantics_bigstep_state_vs_tagged: 
  assumes "\<forall>m::'m. stateful_matcher' \<sigma> m p = stateful_matcher_tagged' m (packet_tagger' \<sigma> p)" 
  shows "\<Gamma>,stateful_matcher' \<sigma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow>
         \<Gamma>,stateful_matcher_tagged',packet_tagger' \<sigma> p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t"
proof -
  { fix m::"'m match_expr"
   from assms have
    "matches (stateful_matcher' \<sigma>) m p \<longleftrightarrow> matches stateful_matcher_tagged' m (packet_tagger' \<sigma> p)"
      by(induction m) (simp_all)
  } note matches_stateful_matcher_stateful_matcher_tagged=this

  show ?thesis (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    thus ?rhs
     proof(induction rs Undecided t rule: iptables_bigstep_induct)
     case (Seq _ _ _ t)
       thus ?case
         apply(cases t)
          apply (simp add: seq)
         apply(auto simp add: decision seq dest: decisionD)
         done
     qed(auto intro: iptables_bigstep.intros simp add: matches_stateful_matcher_stateful_matcher_tagged)
  next
    assume ?rhs
    thus ?lhs
     proof(induction rs Undecided t rule: iptables_bigstep_induct)
     case (Seq _ _ _ t)
       thus ?case
         apply(cases t)
          apply (simp add: seq)
         apply(auto  simp add: decision seq dest: decisionD)
         done
     qed(auto intro: iptables_bigstep.intros simp add: matches_stateful_matcher_stateful_matcher_tagged)
  qed
qed
   


text\<open>Both semantics are equal\<close>
theorem semantics_stateful_vs_tagged:
  assumes "\<forall>m \<sigma> p. stateful_matcher' \<sigma> m p = stateful_matcher_tagged' m (packet_tagger' \<sigma> p)" 
  shows "semantics_stateful rs stateful_matcher' state_update' \<sigma>\<^sub>0 start ps ps_processed \<sigma>' =
       semantics_stateful_packet_tagging rs stateful_matcher_tagged' packet_tagger' state_update' \<sigma>\<^sub>0 start ps ps_processed \<sigma>'"
  proof -
   from semantics_bigstep_state_vs_tagged[of stateful_matcher' _ _ stateful_matcher_tagged' packet_tagger'] assms
     have vs_tagged:
     "rs,stateful_matcher' \<sigma>',p\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy], Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow>
      rs,stateful_matcher_tagged',packet_tagger' \<sigma>' p\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy], Undecided\<rangle> \<Rightarrow> t"
      for t p \<sigma>' built_in_chain default_policy by blast
   from assms have stateful_matcher_eq:
    "(\<lambda>a b. stateful_matcher_tagged' a (packet_tagger' \<sigma>' b)) = stateful_matcher' \<sigma>'" for \<sigma>' by presburger  
  show ?thesis (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume ?lhs thus ?rhs
        proof(induction rule: semantics_stateful.induct)
        case 1 thus ?case by(auto intro: semantics_stateful_packet_tagging_intro_start)[1]
        next
        case (2 built_in_chain default_policy p ps  ps_processed \<sigma>')
          from 2 have
            "semantics_stateful_packet_tagging rs stateful_matcher_tagged' packet_tagger' state_update' \<sigma>\<^sub>0 (built_in_chain, default_policy) (p # ps) ps_processed \<sigma>'"
            by blast
          with 2(2,3) show ?case
          apply -
          apply(rule semantics_stateful_packet_tagging_intro_process_one)
             apply(simp_all add: vs_tagged)
          done
       qed
    next
      assume ?rhs thus ?lhs
      proof(induction rule: semantics_stateful_packet_tagging.induct)
        case 1 thus ?case by(auto intro: semantics_stateful_intro_start)
        next
        case (2 built_in_chain default_policy p ps ps_processed \<sigma>') thus ?case
           apply -
           apply(rule semantics_stateful_intro_process_one)
              apply(simp_all add: stateful_matcher_eq vs_tagged)
           done
      qed
    qed
  qed


text\<open>Examples\<close>
context
begin
subsection\<open>Example: Conntrack with curried matcher\<close>
  text\<open>We illustrate stateful semantics with a simple example. We allow matching on the states New
  and Established. In addition, we introduce a primitive match to match on outgoing ssh packets (dst port = 22).
  The state is managed in a state table where accepted connections are remembered.\<close>


  text\<open>SomePacket with source and destination port or something we don't know about\<close>
  private datatype packet = SomePacket "nat \<times> nat" | OtherPacket

  private datatype primitive_matches = New | Established | IsSSH

  text\<open>In the state, we remember the packets which belong to an established connection.\<close>
  private datatype conntrack_state = State "packet set"

  text\<open>The stateful primitive matcher: It is given the current state table. 
    If match on @{const Established}, the packet must be known in the state table.
    If match on @{const New}, the packet must not be in the state table.
    If match on @{const IsSSH}, the dst port of the packet must be 22.\<close>
  private fun stateful_matcher :: "conntrack_state \<Rightarrow> (primitive_matches, packet) matcher" where
    "stateful_matcher (State state_table) = (\<lambda>m p. m = Established \<and> p \<in> state_table \<or>
                                           m = New \<and> p \<notin> state_table \<or>
                                           m = IsSSH \<and> (\<exists>dst_port. p = SomePacket (22, dst_port)))"

  text\<open>Connections are always bi-directional.\<close>
  private fun reverse_direction :: "packet \<Rightarrow> packet" where
    "reverse_direction OtherPacket = OtherPacket" |
    "reverse_direction (SomePacket (src, dst)) = SomePacket (dst,src)"

  text\<open>If a packet is accepted, the state for its bi-directional connection is saved in the state table.\<close>
  private fun state_update' :: "conntrack_state \<Rightarrow> final_decision \<Rightarrow> packet \<Rightarrow> conntrack_state" where
    "state_update' (State state_table) FinalAllow p = State (state_table \<union> {p, reverse_direction p})" |
    "state_update' (State state_table) FinalDeny p = State state_table"

  text\<open>Allow everything that is established and allow new ssh connections.
    Drop everything else (default policy, see below)\<close>
  private definition "ruleset == [''INPUT'' \<mapsto> [Rule (Match Established) Accept, Rule (MatchAnd (Match IsSSH) (Match New)) Accept]]"

  text\<open>The @{const ruleset} does not allow @{const OtherPacket}\<close>
  lemma "semantics_stateful ruleset stateful_matcher state_update' (State {}) (''INPUT'', Drop) []
    [(OtherPacket, FinalDeny)] (State {})"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro_process_one)
        apply(simp_all)
       apply(rule semantics_stateful_intro_start)
        apply(simp_all)
     apply(rule seq_cons)
      apply(rule call_result)
        apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros)
    done


  text\<open>The @{const ruleset} allows ssh packets, i.e. any packets with destination port 22 in the @{const New} rule.
        The state is updated such that everything which belongs to the connection will now be accepted.\<close>
  lemma "semantics_stateful ruleset stateful_matcher state_update' (State {}) (''INPUT'', Drop)
          []
          [(SomePacket (22, 1024), FinalAllow)]
          (State {SomePacket (1024, 22), SomePacket (22, 1024)})"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro_process_one)
        apply(simp_all)
       apply(rule semantics_stateful_intro_start)
        apply(simp_all)
     apply(rule seq_cons)
      apply(rule call_result)
        apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros)
    done

  text\<open>If we continue with this state, answer packets are now allowed\<close>
  lemma "semantics_stateful ruleset stateful_matcher state_update' (State {}) (''INPUT'', Drop)
          []
          [(SomePacket (22, 1024), FinalAllow), (SomePacket (1024, 22), FinalAllow)]
          (State {SomePacket (1024, 22), SomePacket (22, 1024)})"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro_process_one)
        apply(simp_all)
      apply(rule semantics_stateful_intro_process_one)
         apply(simp_all)
        apply(rule semantics_stateful_intro_start)
         apply(simp_all)
      apply(rule seq_cons, rule call_result, simp_all, rule seq_cons)
        apply(auto intro: iptables_bigstep.intros)
    apply(rule seq_cons, rule call_result, simp_all, rule seq_cons)
      apply(auto intro: iptables_bigstep.intros)
    done

  text\<open>In contrast, without having previously established a state, answer packets are prohibited\<close>
  text\<open>If we continue with this state, answer packets are now allowed\<close>
  lemma "semantics_stateful ruleset stateful_matcher state_update' (State {}) (''INPUT'', Drop)
          []
          [(SomePacket (1024, 22), FinalDeny), (SomePacket (22, 1024), FinalAllow), (SomePacket (1024, 22), FinalAllow)]
          (State {SomePacket (1024, 22), SomePacket (22, 1024)})"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro_process_one)
        apply(simp_all)
      apply(rule semantics_stateful_intro_process_one)
         apply(simp_all)
       apply(rule semantics_stateful_intro_process_one)
          apply(simp_all)
        apply(rule semantics_stateful_intro_start)
         apply(simp_all)
       apply(rule seq_cons, rule call_result, simp_all, rule seq_cons, auto intro: iptables_bigstep.intros)+
    done


subsection\<open>Example: Conntrack with packet tagging\<close>

  datatype packet_tag = TagNew | TagEstablished
  datatype packet_tagged = SomePacket_tagged "nat \<times> nat \<times> packet_tag" | OtherPacket_tagged packet_tag

  fun get_packet_tag :: "packet_tagged \<Rightarrow> packet_tag" where
    "get_packet_tag (SomePacket_tagged (_,_, tag)) = tag" |
    "get_packet_tag (OtherPacket_tagged tag) = tag"

  definition stateful_matcher_tagged :: "(primitive_matches, packet_tagged) matcher" where
    "stateful_matcher_tagged \<equiv> \<lambda>m p. m = Established \<and> (get_packet_tag p = TagEstablished) \<or>
                                           m = New \<and> (get_packet_tag p = TagNew) \<or>
                                           m = IsSSH \<and> (\<exists>dst_port tag. p = SomePacket_tagged (22, dst_port, tag))"

  fun calculate_packet_tag :: "conntrack_state \<Rightarrow> packet \<Rightarrow> packet_tag" where
    "calculate_packet_tag (State state_table) p = (if p \<in> state_table then TagEstablished else TagNew)"

  fun packet_tagger :: "conntrack_state \<Rightarrow> packet \<Rightarrow> packet_tagged" where
    "packet_tagger \<sigma> (SomePacket (s,d)) = (SomePacket_tagged (s,d, calculate_packet_tag \<sigma> (SomePacket (s,d))))" |
    "packet_tagger \<sigma> OtherPacket = (OtherPacket_tagged (calculate_packet_tag \<sigma> OtherPacket))"

  text\<open>If a packet is accepted, the state for its bi-directional connection is saved in the state table.\<close>
  fun state_update_tagged :: "conntrack_state \<Rightarrow> final_decision \<Rightarrow> packet \<Rightarrow> conntrack_state" where
    "state_update_tagged (State state_table) FinalAllow p = State (state_table \<union> {p, reverse_direction p})" |
    "state_update_tagged (State state_table) FinalDeny p = State state_table"


  
  text\<open>Both semantics are equal\<close>
  lemma "semantics_stateful rs stateful_matcher state_update' \<sigma>\<^sub>0 start ps ps_processed \<sigma>' =
    semantics_stateful_packet_tagging rs stateful_matcher_tagged packet_tagger state_update' \<sigma>\<^sub>0 start ps ps_processed \<sigma>'"
    apply(rule semantics_stateful_vs_tagged)
    apply(intro allI, rename_tac m \<sigma> p)
    apply(case_tac \<sigma>)
    apply(case_tac p)
     apply(simp_all add: stateful_matcher_tagged_def)
    apply force
    done
end

end
