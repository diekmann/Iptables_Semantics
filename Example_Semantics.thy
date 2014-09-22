theory Example_Semantics
imports Call_Return_Unfolding "Primitive_Matchers/IPSpace_Syntax"
begin


section{*Examples Big Step Semantics*}
text{*we use a primitive matcher which always apllies.*}
  fun applies_Yes :: "('a, 'p) matcher" where
  "applies_Yes m p = True" 
  lemma[simp]: "Semantics.matches applies_Yes MatchAny p" by simp
  lemma[simp]: "Semantics.matches applies_Yes (Match e) p" by simp

  definition "m=Match (Src (Ip4Addr (0,0,0,0)))"
  definition "p=\<lparr>src_ip=0, dst_ip=0, prot=protPacket.ProtTCP\<rparr>"
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

  hide_const m p

  text{*We tune the primitive matcher to support everything we need in the example. Note that the undefined cases cannot be handled with these exact semantics!*}
  fun applies_exampleMatchExact :: "(iptrule_match, packet) matcher" where
  "applies_exampleMatchExact (Src (Ip4Addr addr)) p \<longleftrightarrow> src_ip p = (ipv4addr_of_dotteddecimal addr)" |
  "applies_exampleMatchExact (Dst (Ip4Addr addr)) p \<longleftrightarrow> dst_ip p = (ipv4addr_of_dotteddecimal addr)" |
  "applies_exampleMatchExact (Prot ProtAll) p \<longleftrightarrow> True" |
  "applies_exampleMatchExact (Prot ipt_protocol.ProtTCP) p \<longleftrightarrow> prot p = protPacket.ProtTCP" |
  "applies_exampleMatchExact (Prot ipt_protocol.ProtUDP) p \<longleftrightarrow> prot p = protPacket.ProtUDP"
  (*TODO, not exhaustive, only an example!!*)

  lemma "[''FORWARD'' \<mapsto> [ Rule (MatchAnd (Match (Src (Ip4Addr (0,0,0,0)))) (Match (Dst (Ip4Addr (0,0,0,0))))) Reject, 
                          Rule (Match (Dst (Ip4Addr (0,0,0,0)))) Log, 
                          Rule (Match (Prot ipt_protocol.ProtTCP)) Accept,
                          Rule (Match (Prot ipt_protocol.ProtTCP)) Drop]
         ],applies_exampleMatchExact,\<lparr>src_ip=(ipv4addr_of_dotteddecimal (1,2,3,4)), dst_ip=(ipv4addr_of_dotteddecimal (0,0,0,0)), prot=protPacket.ProtTCP\<rparr>\<turnstile>
            \<langle>[Rule MatchAny (Call ''FORWARD'')], Undecided\<rangle> \<Rightarrow> (Decision FinalAllow)"
  apply(rule call_result)
  apply(auto)
  apply(rule Semantics.seq_cons)
  apply(auto intro: Semantics.nomatch simp add: ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)
  apply(rule Semantics.seq_cons)
  apply(auto intro: Semantics.log simp add: ipv4addr_of_dotteddecimal.simps ipv4addr_of_nat_def)
  apply(rule Semantics.seq_cons)
  apply(auto intro: Semantics.accept)
  apply(auto intro: Semantics.decision)
  done


end
