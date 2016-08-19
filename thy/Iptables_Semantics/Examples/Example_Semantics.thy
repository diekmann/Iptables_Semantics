theory Example_Semantics
imports "../Call_Return_Unfolding" "../Primitive_Matchers/Common_Primitive_Matcher"
begin


section\<open>Examples Big Step Semantics\<close>
text\<open>We use a primitive matcher which always applies. We don't care about matching in this example.\<close>
  fun applies_Yes :: "('a, 'p) matcher" where
  "applies_Yes m p = True" 
  lemma[simp]: "Semantics.matches applies_Yes MatchAny p" by simp
  lemma[simp]: "Semantics.matches applies_Yes (Match e) p" by simp

  definition "m=Match (Src (IpAddr (0::ipv4addr)))"
  lemma[simp]: "Semantics.matches applies_Yes m p" by (simp add: m_def)

  lemma "[''FORWARD'' \<mapsto> [(Rule m Log), (Rule m Accept), (Rule m Drop)]],applies_Yes,p\<turnstile>
      \<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalAllow)"
  apply(rule call_result)
    apply(auto)
  apply(rule seq_cons)
   apply(auto intro:Semantics.log)
  apply(rule seq_cons)
   apply(auto intro: Semantics.accept)
  apply(rule Semantics.decision)
  done
  
  lemma "[''FORWARD'' \<mapsto> [(Rule m Log), (Rule m (Call ''foo'')), (Rule m Accept)],
          ''foo'' \<mapsto> [(Rule m Log), (Rule m Return)]],applies_Yes,p\<turnstile>
      \<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalAllow)"
  apply(rule call_result)
    apply(auto)
  apply(rule seq_cons)
   apply(auto intro: Semantics.log)
  apply(rule seq_cons)
   apply(rule Semantics.call_return[where rs\<^sub>1="[Rule m Log]" and rs\<^sub>2="[]"])
      apply(simp)+
   apply(auto intro: Semantics.log)
  apply(auto intro: Semantics.accept)
  done
  
  lemma "[''FORWARD'' \<mapsto> [Rule m (Call ''foo''), Rule m Drop], ''foo'' \<mapsto> []],applies_Yes,p\<turnstile>
            \<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalDeny)"
  apply(rule call_result)
    apply(auto)
  apply(rule Semantics.seq_cons)
   apply(rule Semantics.call_result)
     apply(auto)
   apply(rule Semantics.skip)
  apply(auto intro: deny)
  done

  lemma "((\<lambda>rs. process_call [''FORWARD'' \<mapsto> [Rule m (Call ''foo''), Rule m Drop], ''foo'' \<mapsto> []] rs)^^2)
                    [Rule MatchAny (Call ''FORWARD'')]
         = [Rule (MatchAnd MatchAny m) Drop]" by eval

  hide_const m
  
  definition "pkt=\<lparr>p_iiface=''+'', p_oiface=''+'', p_src=0, p_dst=0,
                   p_proto=TCP, p_sport=0, p_dport=0, p_tcp_flags = {TCP_SYN},
                   p_payload='''',p_tag_ctstate= CT_New\<rparr>"

  text\<open>We tune the primitive matcher to support everything we need in the example. Note that the undefined cases cannot be handled with these exact semantics!\<close>
  fun applies_exampleMatchExact :: "(32 common_primitive, 32 tagged_packet) matcher" where
  "applies_exampleMatchExact (Src (IpAddr addr)) p \<longleftrightarrow> p_src p = addr" |
  "applies_exampleMatchExact (Dst (IpAddr addr)) p \<longleftrightarrow> p_dst p = addr" |
  "applies_exampleMatchExact (Prot ProtoAny) p \<longleftrightarrow> True" |
  "applies_exampleMatchExact (Prot (Proto pr)) p \<longleftrightarrow> p_proto p = pr"
  (* not exhaustive, only an example!!*)

  lemma "[''FORWARD'' \<mapsto> [ Rule (MatchAnd (Match (Src (IpAddr 0))) (Match (Dst (IpAddr 0)))) Reject, 
                          Rule (Match (Dst (IpAddr 0))) Log, 
                          Rule (Match (Prot (Proto TCP))) Accept,
                          Rule (Match (Prot (Proto TCP))) Drop]
         ],applies_exampleMatchExact, pkt\<lparr>p_src:=(ipv4addr_of_dotdecimal (1,2,3,4)), p_dst:=(ipv4addr_of_dotdecimal (0,0,0,0))\<rparr>\<turnstile>
            \<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalAllow)"
  apply(rule call_result)
    apply(auto)
  apply(rule Semantics.seq_cons)
   apply(auto intro: Semantics.nomatch simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
  apply(rule Semantics.seq_cons)
   apply(auto intro: Semantics.log simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
  apply(rule Semantics.seq_cons)
   apply(auto simp add: pkt_def intro: Semantics.accept)
  apply(auto intro: Semantics.decision)
  done

end
