theory Analyze_Synology_Diskstation
imports iptables_Ln_tuned_parsed (*2014 firewall dump*)
  "../../Primitive_Matchers/Parser"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Semantics_Ternary/Optimizing"
begin


section{*Example: Synology Diskstation 2014*}
text{*We analyze a dump of a NAS. The dump was created 2014. Unfortunately, we don't have an 
      @{text "iptables-save"} dump from that time and have to rely on the @{text "iptables -L -n"}
      dump. This dump was translated by our legacy python importer.*}


text{*we removed the established,related rule*}
  definition "example_ruleset == firewall_chains(''INPUT'' \<mapsto> 
    remove1 (Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0))))
            (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0))))
            (MatchAnd (Match (Prot (ProtoAny)))
            (Match (Extra (''state RELATED,ESTABLISHED'')))))) (action.Accept)) (the (firewall_chains ''INPUT'')))"

text{*Infix pretty-printing for @{const MatchAnd} and @{const MatchNot}.*}
abbreviation MatchAndInfix :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" (infixr "MATCHAND" 65) where
  "MatchAndInfix m1 m2 \<equiv> MatchAnd m1 m2"
abbreviation MatchNotPrefix :: "'a match_expr \<Rightarrow> 'a match_expr" ("\<not> \<langle>_\<rangle>" 66) where
  "MatchNotPrefix m \<equiv> MatchNot m"
(*abbreviation MatchPrefix :: "'a \<Rightarrow> 'a match_expr" ("\<lozenge> _" 67) where (*This is too slow*)
  "MatchPrefix m \<equiv> Match m"*)
(*This syntax can be pretty confusing when mixing it with other theories. Do not use outside this example!*)


lemma "unfold_ruleset_INPUT action.Accept example_ruleset =
 [Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04''))
   action.Drop,
  Rule (\<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (Extra ''Prot icmp'') MATCHAND Match (Extra ''icmptype 8 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')\<rangle> MATCHAND
        \<not> \<langle>Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')\<rangle> MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp flags:0x17/0x02''))
   action.Drop,
  Rule (Match (Prot (Proto TCP)) MATCHAND Match (Extra ''tcp dpt:22'')) action.Drop,
  Rule (Match (Prot (Proto TCP)) MATCHAND Match (Extra ''multiport dports 21,873,5005,5006,80,548,111,2049,892''))
   action.Drop,
  Rule (Match (Prot (Proto UDP)) MATCHAND Match (Extra ''multiport dports 123,111,2049,892,5353'')) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop,
  Rule MatchAny action.Accept, Rule MatchAny action.Accept]
  " by eval

  lemma "good_ruleset (unfold_ruleset_INPUT action.Accept example_ruleset)" by eval
  lemma "simple_ruleset (unfold_ruleset_INPUT action.Accept example_ruleset)" by eval


  text{*packets from the local LAN are allowed (@{const in_doubt_allow})*}
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr>
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalAllow" by eval

  text{*However, they might also be rate-limited, ... (we don't know about icmp)*}
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr>
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalDeny" by eval
  
  text{*But we can guarantee that packets from the outside are blocked!*}
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (8,8,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80,
     p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr> 
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalDeny" by eval



text{*in doubt allow closure*}
lemma upper: "upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset) =
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop, Rule MatchAny action.Accept]" by eval

text{*in doubt deny closure*}
lemma lower: "lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset) =
 [Rule MatchAny action.Drop, Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Accept]" by eval



text{*upper closure*}
lemma "rmshadow (common_matcher, in_doubt_allow) (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset)) UNIV = 
  [Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16))) action.Accept, Rule MatchAny action.Drop]"
(*<*)apply(subst upper)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
apply(intro conjI impI)
 apply(rule_tac x="\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (8,8,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr> " in exI)
 apply(simp add: ipv4addr_of_dotdecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)
apply(thin_tac "\<exists>p. x p" for x)
apply(rule_tac x="\<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr> " in exI)
apply(simp add: ipv4addr_of_dotdecimal.simps ipv4range_set_from_bitmask_def ipv4range_set_from_netmask_def Let_def ipv4addr_of_nat_def)
done(*>*)


text{*lower closure*}
lemma "rmshadow (common_matcher, in_doubt_deny) (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset)) UNIV =  
  [Rule MatchAny action.Drop]"
apply(subst lower)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
done



lemma "check_simple_fw_preconditions (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset))" by eval

value[code] "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset)))"
lemma "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset))) =
  [''ACCEPT     all  --  192.168.0.0/16            0.0.0.0/0    '',
   ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '',
   ''ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval (*will break when simple_rule_toString is changed*)

lemma "check_simple_fw_preconditions (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset))" by eval
value[code] "map simple_rule_toString (to_simple_firewall (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset)))"


lemma "length (unfold_ruleset_INPUT action.Accept example_ruleset) = 19" by eval
text{*Wow, normalization has exponential(?) blowup here.*}
lemma "length (normalize_rules_dnf (unfold_ruleset_INPUT action.Accept example_ruleset)) = 259" by eval


section{*Synology Diskstation 2015*}
text{*This is a snapshot from 2015, available as @{text "iptables-save"} format. The firewall definition
      and structure has changed with various firmware updates to the device.
      Also, the new parser also parses ports and interfaces*}

parse_iptables_save ds2015_fw="iptables-save"

thm ds2015_fw_def
thm ds2015_fw_INPUT_default_policy_def


text{*this time, we don't removed the established,related rule*}


value[code] "unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)"
lemma "unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw) =
[Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth1'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth1'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})))
   action.Drop,
  Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})) MATCHAND
           Match (Extra ''-m limit --limit 10000/sec --limit-burst 100'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth1'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})))
   action.Drop,
  Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})) MATCHAND
           Match (Extra ''-m limit --limit 10000/sec --limit-burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8''))
   action.Drop,
  Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})) MATCHAND
           Match (Extra ''-m limit --limit 10000/sec --limit-burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})))
   action.Drop,
  Rule (\<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth1'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})) MATCHAND
           Match (Extra ''-m limit --limit 10000/sec --limit-burst 100'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8 -m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_RST})) MATCHAND Match (Extra ''-m limit --limit 1/sec'')\<rangle> MATCHAND
        \<not> \<langle>Match (IIface (Iface ''eth0'')) MATCHAND
           Match (Prot (Proto TCP)) MATCHAND
           Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})) MATCHAND
           Match (Extra ''-m limit --limit 10000/sec --limit-burst 100'')\<rangle> MATCHAND
        Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND Match (L4_Flags (TCP_Flags {TCP_FIN, TCP_SYN, TCP_RST, TCP_ACK} {TCP_SYN})))
   action.Drop,
  Rule (Match (IIface (Iface ''lo''))) action.Accept, Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x16, 0x16)])) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND
        Match (Dst_Ports
                [(0x15, 0x15), (0x369, 0x369), (0x138D, 0x138D), (0x138E, 0x138E), (0x50, 0x50), (0x224, 0x224), (0x6F, 0x6F), (0x37C, 0x37C),
                 (0x801, 0x801)]))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x7B, 0x7B), (0x6F, 0x6F), (0x37C, 0x37C), (0x801, 0x801), (0x14E9, 0x14E9)]))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (192, 168, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Accept,
  Rule (Match (IIface (Iface ''eth0''))) action.Drop, Rule MatchAny action.Accept]" by eval

value[code] "map common_primitive_rule_toString (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))"

value[code] "(upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))"
(*TODO: remove the following  \<not> \<langle>Match (L4_Flags (TCP_Flags {} {TCP_SYN}))\<rangle>
                              \<not> \<langle>Match (Prot (Proto ICMP))\<rangle> MATCHAND \<not> \<langle>Match (Prot (Proto TCP))\<rangle>
                              \<not> \<langle>Match (IIface (Iface ''eth0''))\<rangle> MATCHAND Match (IIface (Iface ''eth0'')) 
*)

(*TODO: we can get a better simple firewall!*)

value[code] "optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))"


lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))))" by eval

value[code] "map simple_rule_toString (to_simple_firewall
              (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)))))))"



end
