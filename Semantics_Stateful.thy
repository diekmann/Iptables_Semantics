theory Semantics_Stateful
imports Semantics
begin

section{*Semantics Stateful*}

subsection{*Model 1*}

text{*Processing a packet with state can be modeled as follows:
  The state is @{term \<sigma>}.
  The primitive matcher @{term \<gamma>\<^sub>\<sigma>} is a curried function where the first argument is the state and
  it returns a stateless primitive matcher, i.e. @{term "\<gamma> = (\<gamma>\<^sub>\<sigma> \<sigma>)"}.
  With this stateless primitive matcher @{term \<gamma>}, the @{const iptables_bigstep} semantics are executed.
  As entry point, the iptables built-in chains @{term "''INPUT''"}, @{term "''OUTPUT''"}, and @{term "''FORWARD''"} with their
  default-policy (@{const Accept} or @{const Drop} are valid for iptables) are chosen.
  The semantics must yield a @{term "Decision X"}.
  Due to the default-policy, this is always the case if the ruleset is well-formed.
  When a decision is made, the state @{term \<sigma>} is updated.*}

inductive semantics_stateful ::
  "'a ruleset \<Rightarrow> ('\<sigma> \<Rightarrow> ('a, 'p) matcher) \<Rightarrow> ('\<sigma> \<Rightarrow> final_decision \<Rightarrow> 'p \<Rightarrow> '\<sigma>) \<Rightarrow>
   (string \<times> action) \<Rightarrow> '\<sigma> \<Rightarrow> 'p \<Rightarrow>
   ('\<sigma> \<times> final_decision) \<Rightarrow> bool" for \<Gamma> and \<gamma>\<^sub>\<sigma> and state_update where
  "\<Gamma>,(\<gamma>\<^sub>\<sigma> \<sigma>),p\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy],Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
    semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_update (built_in_chain, default_policy) \<sigma> p (state_update \<sigma> X p, X)"


lemma semantics_stateful_intro: "\<Gamma>,\<gamma>\<^sub>\<sigma> \<sigma>,p\<turnstile> \<langle>[Rule MatchAny (Call state_update), Rule MatchAny default_policy], Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
       \<sigma>' = state_upate \<sigma> X p \<Longrightarrow>
       semantics_stateful \<Gamma> \<gamma>\<^sub>\<sigma> state_upate (state_update, default_policy) \<sigma> p (\<sigma>', X)"
  by(auto intro: semantics_stateful.intros)


subsection{*Example: Conntrack*}
context
begin
  text{*We illustrate stateful semantics with a simple example. We allow matching on the states New
  and Established. In addition, we introduce a primitive match to match on outgoing ssh packets (dst port = 22).
  The state is managed in a state table where accepted connections are remembered.*}


  text{*SomePacket with source and destination port or something we don't know about*}
  datatype packet = SomePacket "nat \<times> nat" | OtherPacket

  datatype primitive_matches = New | Established | IsSSH

  datatype conntrack_state = State "packet set"

  text{*The stateful primitive matcher: It is given the current state table. 
    If match on @{const Established}, the packet must be known in the state table.
    If match on @{const New}, the packet must not be in the state table.
    If match on @{const IsSSH}, the dst port of the packet must be 22.*}
  fun stateful_matcher :: "conntrack_state \<Rightarrow> (primitive_matches, packet) matcher" where
    "stateful_matcher (State state_table) = (\<lambda>m p. m = Established \<and> p \<in> state_table \<or>
                                           m = New \<and> p \<notin> state_table \<or>
                                           m = IsSSH \<and> (\<exists>dst_port. p = SomePacket (22, dst_port)))"

  text{*Connections are always bi-directional.*}
  fun reverse_direction :: "packet \<Rightarrow> packet" where
    "reverse_direction OtherPacket = OtherPacket" |
    "reverse_direction (SomePacket (src, dst)) = SomePacket (dst,src)"

  text{*If a packet is accepted, the state for its bi-directional connection is saved in the state table.*}
  fun state_update :: "conntrack_state \<Rightarrow> final_decision \<Rightarrow> packet \<Rightarrow> conntrack_state" where
    "state_update (State state_table) FinalAllow p = State (state_table \<union> {p, reverse_direction p})" |
    "state_update (State state_table) FinalDeny p = State state_table"

  text{*Allow everything that is established and allow new ssh connections.
    Drop everything else (default policy, see below)*}
  definition "ruleset == [''INPUT'' \<mapsto> [Rule (Match Established) Accept, Rule (MatchAnd (Match IsSSH) (Match New)) Accept]]"

  text{*The @{const ruleset} does not allow @{const OtherPacket}*}
  lemma "semantics_stateful ruleset stateful_matcher state_update (''INPUT'', Drop)
    (State {}) OtherPacket ((State {}), FinalDeny)"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro)
     apply(simp_all)
    apply(rule seq_cons)
     apply(rule call_result)
       apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros simp add: stateful_matcher_def)
    done


  text{*The @{const ruleset} allows ssh packets, i.e. any packets with destination port 22 in the @{const New} rule.
        The state is updated such that everything which belongs to the connection will now be accepted.*}
  lemma "semantics_stateful ruleset stateful_matcher state_update (''INPUT'', Drop)
          (State {})
          (SomePacket (22, 1024))
          (State {SomePacket (1024, 22), SomePacket (22, 1024)}, FinalAllow)"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro)
     apply(simp_all)
    apply(rule seq_cons)
     apply(rule call_result)
       apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros simp add: stateful_matcher_def)
    done

  text{*If we continue with this state, answer packets are now allowed*}
  lemma "semantics_stateful ruleset stateful_matcher state_update (''INPUT'', Drop)
          (State {SomePacket (1024, 22), SomePacket (22, 1024)})
          (SomePacket (22, 1024))
          (State {SomePacket (1024, 22), SomePacket (22, 1024)}, FinalAllow)"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro)
     apply(simp_all)
    apply(rule seq_cons)
     apply(rule call_result)
       apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros simp add: stateful_matcher_def)
    done

  text{*In contrast, without having previously established a state, answer packets are prohibited*}
  lemma "semantics_stateful ruleset stateful_matcher state_update (''INPUT'', Drop)
    (State {})
    (SomePacket (1024, 22))
    (State {}, FinalDeny)"
    unfolding ruleset_def
    apply(rule semantics_stateful_intro)
     apply(simp_all)
    apply(rule seq_cons)
     apply(rule call_result)
       apply(simp_all)
      apply(rule seq_cons)
       apply(auto intro: iptables_bigstep.intros simp add: stateful_matcher_def)
    done
end


subsection{*Model 2*}

(*TODO: describe*)
inductive semantics_stateful_packet_tagging ::
  "'a ruleset \<Rightarrow> ('a, 'ptagged) matcher \<Rightarrow> ('\<sigma> \<Rightarrow> 'p \<Rightarrow> 'ptagged) \<Rightarrow> ('\<sigma> \<Rightarrow> final_decision \<Rightarrow> 'p \<Rightarrow> '\<sigma>) \<Rightarrow>
   (string \<times> action) \<Rightarrow> '\<sigma> \<Rightarrow> 'p \<Rightarrow>
   ('\<sigma> \<times> final_decision) \<Rightarrow> bool" for \<Gamma> and \<gamma> and packet_tagger and state_update where
  "\<Gamma>,\<gamma>,(packet_tagger \<sigma> p)\<turnstile> \<langle>[Rule MatchAny (Call built_in_chain), Rule MatchAny default_policy],Undecided\<rangle> \<Rightarrow> Decision X \<Longrightarrow>
    semantics_stateful_packet_tagging \<Gamma> \<gamma> packet_tagger state_update (built_in_chain, default_policy) \<sigma> p (state_update \<sigma> X p, X)"


subsection{*Example: Conntrack with packet tagging*}
context
begin
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

  text{*If a packet is accepted, the state for its bi-directional connection is saved in the state table.*}
  fun state_update_tagged :: "conntrack_state \<Rightarrow> final_decision \<Rightarrow> packet \<Rightarrow> conntrack_state" where
    "state_update_tagged (State state_table) FinalAllow p = State (state_table \<union> {p, reverse_direction p})" |
    "state_update_tagged (State state_table) FinalDeny p = State state_table"


  lemma matches_stateful_matcher_stateful_matcher_tagged:
  "matches (stateful_matcher \<sigma>) m p \<longleftrightarrow> matches stateful_matcher_tagged m (packet_tagger \<sigma> p)"
    apply(induction m)
       apply(simp_all)
    apply(cases p)
     apply(simp_all add: stateful_matcher_tagged_def)
     apply(case_tac \<sigma>)
     apply(simp_all)
     apply force
    apply(case_tac \<sigma>)
    apply(simp)
    done

  lemma semantics_bigstep_state_vs_tagged: "\<Gamma>,stateful_matcher \<sigma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t \<longleftrightarrow>
         \<Gamma>,stateful_matcher_tagged,packet_tagger \<sigma> p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t"
  apply(rule iffI)
   apply(induction rs Undecided t rule: iptables_bigstep_induct)
   apply(auto intro: iptables_bigstep.intros simp add: matches_stateful_matcher_stateful_matcher_tagged)[8]
   apply (metis  decision decisionD  seq    state.exhaust)
  apply(induction rs Undecided t rule: iptables_bigstep_induct)
  apply(auto intro: iptables_bigstep.intros simp add: matches_stateful_matcher_stateful_matcher_tagged)[8]
  apply (metis  decision decisionD  seq    state.exhaust)
  done
   
  
  text{*Both semantics are equal*}
  lemma "semantics_stateful rs stateful_matcher state_update start \<sigma> p t =
    semantics_stateful_packet_tagging rs stateful_matcher_tagged packet_tagger state_update start \<sigma> p t"
    apply(rule iffI)
     apply(induction rule: semantics_stateful.induct)
     apply(simp add: semantics_bigstep_state_vs_tagged)
     apply(auto intro: semantics_stateful_packet_tagging.intros)[1]
    apply(induction rule: semantics_stateful_packet_tagging.induct)
    apply(rule semantics_stateful_intro, simp_all)
    apply(simp add: semantics_bigstep_state_vs_tagged)
    done
    

end

end
