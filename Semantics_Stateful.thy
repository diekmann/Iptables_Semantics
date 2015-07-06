theory Semantics_Stateful
imports Semantics
begin

section{*Semantics Stateful*}

text{*Processing a packet with state can be modeled as follows:
  The primitive matcher @{term \<gamma>\<^sub>\<sigma>} is a curried function where the first argument is its state and
  it returns a stateless primitive matcher.*}

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

context
begin
  text{*SomePacket with source and destination port or something we don't know about*}
  datatype packet = SomePacket "nat \<times> nat" | OtherPacket
  datatype primitive_matches = New | Established | IsSSH

  definition stateful_matcher :: "packet set \<Rightarrow> (primitive_matches, packet) matcher" where
    "stateful_matcher state_table \<equiv> \<lambda>m p. m = Established \<and> p \<in> state_table \<or>
                                           m = New \<and> p \<notin> state_table \<or>
                                           m = IsSSH \<and> (\<exists>dst_port. p = SomePacket (22, dst_port))"

  fun reverse_direction :: "packet \<Rightarrow> packet" where
    "reverse_direction OtherPacket = OtherPacket" |
    "reverse_direction (SomePacket (src, dst)) = SomePacket (dst,src)"

  fun state_update :: "packet set \<Rightarrow> final_decision \<Rightarrow> packet \<Rightarrow> packet set" where
    "state_update state_table FinalAllow p = state_table \<union> {p, reverse_direction p}" |
    "state_update state_table FinalDeny p = state_table"

  definition "ruleset == [''INPUT'' \<mapsto> [Rule (Match Established) Accept, Rule (MatchAnd (Match IsSSH) (Match New)) Accept]]"

  text{*The @{const ruleset} does not allow @{const OtherPacket}*}
  lemma "semantics_stateful ruleset
          stateful_matcher state_update (''INPUT'', Drop) {} OtherPacket ({}, FinalDeny)"
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
        The state is updated such that everything with belongs to the connection will now be accepted.*}
  lemma "semantics_stateful ruleset
          stateful_matcher state_update (''INPUT'', Drop) {} 
              (SomePacket (22, 1024)) ({SomePacket (1024, 22), SomePacket (22, 1024)}, FinalAllow)"
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
  lemma "semantics_stateful ruleset
          stateful_matcher state_update (''INPUT'', Drop) {SomePacket (1024, 22), SomePacket (22, 1024)} 
              (SomePacket (22, 1024)) ({SomePacket (1024, 22), SomePacket (22, 1024)}, FinalAllow)"
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
  lemma "semantics_stateful ruleset
          stateful_matcher state_update (''INPUT'', Drop) {} (SomePacket (1024, 22)) ({}, FinalDeny)"
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


end
