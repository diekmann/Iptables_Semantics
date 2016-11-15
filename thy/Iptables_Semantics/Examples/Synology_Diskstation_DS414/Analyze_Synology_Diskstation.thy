theory Analyze_Synology_Diskstation
imports iptables_Ln_tuned_parsed (*2014 firewall dump*)
  "../../Primitive_Matchers/Parser"
  "../../Primitive_Matchers/Parser6"
begin


section\<open>Example: Synology Diskstation 2014\<close>
text\<open>We analyze a dump of a NAS. The dump was created 2014. Unfortunately, we don't have an 
      @{text "iptables-save"} dump from that time and have to rely on the @{text "iptables -L -n"}
      dump. This dump was translated by our legacy python importer.\<close>


text\<open>we removed the established,related rule\<close>
  definition "example_ruleset == firewall_chains(''INPUT'' \<mapsto> 
    remove1 (Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0)))
            (MatchAnd (Match (Dst (IpAddrNetmask 0 0)))
            (MatchAnd (Match (Prot (ProtoAny)))
            (Match (Extra (''state RELATED,ESTABLISHED'')))))) (action.Accept)) (the (firewall_chains ''INPUT'')))"

text\<open>Infix pretty-printing for @{const MatchAnd} and @{const MatchNot}.\<close>
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
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 16))) action.Accept, Rule MatchAny action.Drop,
  Rule MatchAny action.Accept, Rule MatchAny action.Accept]
  " by eval

  lemma "good_ruleset (unfold_ruleset_INPUT action.Accept example_ruleset)" by eval
  lemma "simple_ruleset (unfold_ruleset_INPUT action.Accept example_ruleset)" by eval


  text\<open>packets from the local LAN are allowed (@{const in_doubt_allow})\<close>
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_payload='''', p_tag_ctstate = CT_New\<rparr>
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalAllow" by eval

  text\<open>However, they might also be rate-limited, ... (we don't know about icmp)\<close>
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (8,8,8,8),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN}, p_payload='''', p_tag_ctstate = CT_New\<rparr>
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalDeny" by eval
  
  text\<open>But we can guarantee that packets from the outside are blocked!\<close>
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (8,8,8,8), p_dst= 0, p_proto=TCP, p_sport=2065, p_dport=80,
     p_tcp_flags = {TCP_SYN}, p_payload='''', p_tag_ctstate = CT_New\<rparr> 
        (unfold_ruleset_INPUT action.Accept example_ruleset)
        Undecided = Decision FinalDeny" by eval



text\<open>in doubt allow closure\<close>
lemma upper: "upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset) =
  [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 16))) action.Accept,
   Rule MatchAny action.Drop]" by eval

text\<open>in doubt deny closure\<close>
lemma lower: "lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset) =
 [Rule MatchAny action.Drop]" by eval


text\<open>upper closure\<close>
lemma "rmshadow (common_matcher, in_doubt_allow) (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset)) UNIV = 
  [Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 16))) action.Accept, Rule MatchAny action.Drop]"
(*<*)apply(subst upper)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
apply(intro conjI impI)
 apply(rule_tac x="undefined\<lparr>p_iiface := ''eth0'', p_oiface := ''eth1'',
                   p_src := ipv4addr_of_dotdecimal (8,8,8,8), p_dst := 0,
                   p_proto := TCP, p_sport:=2065, p_dport:=80\<rparr>" in exI)
 apply(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipset_from_cidr_alt mask_def; fail)
apply(thin_tac "\<exists>p. x p" for x)
apply(rule_tac x="undefined\<lparr>p_iiface := ''eth0'', p_oiface := ''eth1'',
                            p_src := ipv4addr_of_dotdecimal (192,168,8,8), p_dst:= 0,
                            p_proto:=TCP, p_sport:=2065, p_dport:=80\<rparr> " in exI)
apply(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def ipset_from_cidr_alt mask_def; fail)
done(*>*)


text\<open>lower closure\<close>
lemma "rmshadow (common_matcher, in_doubt_deny) (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset)) UNIV =  
  [Rule MatchAny action.Drop]"
apply(subst lower)
apply(subst rmshadow.simps)
apply(simp del: rmshadow.simps)
apply(simp add: Matching_Ternary.matches_def)
done



lemma "check_simple_fw_preconditions (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset))" by eval

value[code] "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset)))"
lemma "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure (unfold_ruleset_INPUT action.Accept example_ruleset))) =
  [''ACCEPT     all  --  192.168.0.0/16            0.0.0.0/0    '',
   ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval (*will break when simple_rule_ipv4_toString is changed*)

lemma "check_simple_fw_preconditions (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset))" by eval
value[code] "map simple_rule_ipv4_toString (to_simple_firewall (lower_closure (unfold_ruleset_INPUT action.Accept example_ruleset)))"


lemma "length (unfold_ruleset_INPUT action.Accept example_ruleset) = 19" by eval
text\<open>Wow, normalization has exponential(?) blowup here.\<close>
lemma "length (normalize_rules_dnf (unfold_ruleset_INPUT action.Accept example_ruleset)) = 259" by eval


section\<open>Synology Diskstation 2015\<close>
text\<open>This is a snapshot from 2015, available as @{text "iptables-save"} format. The firewall definition
      and structure has changed with various firmware updates to the device.
      Also, the new parser also parses ports and interfaces\<close>

parse_iptables_save ds2015_fw="iptables-save"

thm ds2015_fw_def
thm ds2015_fw_INPUT_default_policy_def


text\<open>this time, we don't removed the established,related rule\<close>


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
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x16, 0x16)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto TCP)) MATCHAND
        Match (Dst_Ports (L4Ports TCP 
                [(0x15, 0x15), (0x369, 0x369), (0x138D, 0x138D), (0x138E, 0x138E), (0x50, 0x50), (0x224, 0x224), (0x6F, 0x6F), (0x37C, 0x37C),
                 (0x801, 0x801)])))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND
        Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x7B, 0x7B), (0x6F, 0x6F), (0x37C, 0x37C), (0x801, 0x801), (0x14E9, 0x14E9)])))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Accept,
  Rule (Match (IIface (Iface ''eth0''))) action.Drop, Rule MatchAny action.Accept]" by eval

value[code] "map common_primitive_rule_toString (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))"

value[code] "(upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))"

value[code] "optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))"

value[code] "upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)))"

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw))))))" by eval

value[code] "map simple_rule_ipv4_toString (to_simple_firewall
              (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)))))))"
lemma "simple_fw_valid (to_simple_firewall
              (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)))))))" by eval
lemma "simple_fw_valid (to_simple_firewall
              (lower_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new (unfold_ruleset_INPUT ds2015_fw_INPUT_default_policy (map_of ds2015_fw)))))))" by eval

parse_iptables_save ds2015_2_fw="iptables-save_jun_2015_cleanup"
text\<open>In 2015 there was also an update and a cleanup of the ruleset.
The following should be fulfilled:
Port 80 globally blocked (fulfilled, only reachable by localhost).
Port 22 globally blocked (not fulfilled, error in the ruleset).
Port 8080 only reachable from 192.168.0.0/24 and localhost (fulfilled).
\<close>

value[code] "unfold_ruleset_INPUT ds2015_2_fw_INPUT_default_policy (map_of ds2015_2_fw)"

lemma "access_matrix_pretty_ipv4 parts_connection_ssh
        (to_simple_firewall_without_interfaces ipassmt_generic_ipv4 None
          (unfold_ruleset_INPUT ds2015_2_fw_INPUT_default_policy (map_of ds2015_2_fw))) =
  ([(''0.0.0.0'', ''{0.0.0.0 .. 255.255.255.255}'')
   ],
   [(''0.0.0.0'', ''0.0.0.0'')])" by eval


lemma "access_matrix_pretty_ipv4 parts_connection_http
        (to_simple_firewall_without_interfaces ipassmt_generic_ipv4 None
          (unfold_ruleset_INPUT ds2015_2_fw_INPUT_default_policy (map_of ds2015_2_fw))) =
  ([(''0.0.0.0'', ''{0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 255.255.255.255}''),
    (''127.0.0.0'', ''{127.0.0.0 .. 127.255.255.255}'')
   ],
   [(''127.0.0.0'', ''0.0.0.0''),
    (''127.0.0.0'', ''127.0.0.0'')])" by eval

lemma "access_matrix_pretty_ipv4 (mk_parts_connection_TCP 10000 8080)
        (to_simple_firewall_without_interfaces ipassmt_generic_ipv4 None
          (unfold_ruleset_INPUT ds2015_2_fw_INPUT_default_policy (map_of ds2015_2_fw))) = 
  ([(''127.0.0.0'', ''{127.0.0.0 .. 127.255.255.255} u {192.168.0.0 .. 192.168.255.255}''),
    (''0.0.0.0'', ''{0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 192.167.255.255} u {192.169.0.0 .. 255.255.255.255}'')
   ],
   [(''127.0.0.0'', ''127.0.0.0''),
    (''127.0.0.0'', ''0.0.0.0'')])" by eval



text\<open>The 2016 version with IPv6 is very interesting. 
 Some source ports for UDP are just allowed.
 Is this a typo? The original structure with the @{const Return}s is very complicated.
 Here is what is actually dropped and accepted:\<close>
parse_ip6tables_save ds_2016_ipv6 = "ip6tables-save_jul_2016" (*5s*)

lemma "map simple_rule_ipv6_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD ds_2016_ipv6_FORWARD_default_policy
                      (map_of ds_2016_ipv6))))))) =
[ ''ACCEPT     all  --  ::/0            ::/0 in: lo   '',
  ''ACCEPT     ipv6-icmp  --  fe80::/10            ::/0    '',
  ''DROP     tcp  --  ::/0            ::/0    dports: 21'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 873'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 631'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 515'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 3260:3262'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 22:23'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 548'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 3493'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 3306'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 67:68'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 123'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 514'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 161'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 19999'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 5353'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 67:68'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 123'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 514'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 161'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 19999'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 5353'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 67:68'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 123'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 514'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 161'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 19999'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 5353'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 67:68'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 123'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 514'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 161'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 19999'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 5353'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 111'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 892'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 2049'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 111'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 892'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 2049'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 111'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 892'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 2049'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 111'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 892'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 2049'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 111'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 892'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 2049'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 0:79'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 81:442'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 444:9024'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 9041:50000'',
  ''DROP     tcp  --  ::/0            ::/0    dports: 50003:65535'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0   sports: 0:5001 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5003 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0   sports: 5005:65000 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0   sports: 65002:65535 dports: 65002:65535'',
  (*The following eth0 rules are shadowed*)
  ''DROP     tcp  --  ::/0            ::/0 in: eth0   dports: 0:79'',
  ''DROP     tcp  --  ::/0            ::/0 in: eth0   dports: 81:442'',
  ''DROP     tcp  --  ::/0            ::/0 in: eth0   dports: 444:9024'',
  ''DROP     tcp  --  ::/0            ::/0 in: eth0   dports: 9041:50000'',
  ''DROP     tcp  --  ::/0            ::/0 in: eth0   dports: 50003:65535'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 0:5001 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 0:5001 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 0:5001 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 0:5001 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 0:5001 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5003 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5003 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5003 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5003 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5003 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5005:65000 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5005:65000 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5005:65000 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5005:65000 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 5005:65000 dports: 65002:65535'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 65002:65535 dports: 0:1899'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 65002:65535 dports: 1901:5001'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 65002:65535 dports: 5003'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 65002:65535 dports: 5005:65000'',
  ''DROP     udp  --  ::/0            ::/0 in: eth0  sports: 65002:65535 dports: 65002:65535'',
  ''ACCEPT     all  --  ::/0            ::/0    '']"
by eval (*50s*)

end
