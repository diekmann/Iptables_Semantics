section\<open>Examples where our Tool/Theory Fails\<close>
theory Ports_Fail
imports "../../Primitive_Matchers/Code_Interface"
begin

text\<open>Nobody is perfect. We try to document all issues here. OverlyHonestScience\<close>

subsection\<open>Port Numbers Belong to a Specific Protocol\<close>
text\<open>
Description: 
@{url "https://github.com/diekmann/Iptables_Semantics/issues/113"}

Likeliness of triggering the issue: low
Severity: may cause wrong analysis. fffuu should reject such wrong results.
Fix: Add the @{typ primitive_protocol} to @{const Src_Ports} and @{const Dst_Ports}.
Is it fixed yet: Yes (!)

The @{const simple_fw} is not affected since it does not allow negated protocols.

By the way: Look at all the related work for firewall analysis. Almost all make the same error. 
We are probably the first ones to have explicitly discovered this issue.
\<close>

text\<open>Here is a minimal example. 
It demonstrates how @{const TCP} and @{const UDP} ports were mixed together. 
You could only cause this issue if you cleverly construct complex negated match expressions exploiting 
the @{const Return} semantics. Note: this is 100 percent valid iptables!\<close>

text\<open>Examples relies on the default action being @{const action.Accept}\<close>
definition allow_only_tcpsport_22_and_udp_dport80 :: "(string \<times> 32 common_primitive rule list) list"
  where
  "allow_only_tcpsport_22_and_udp_dport80 \<equiv>
    [(''FORWARD'', [Rule MatchAny (Call ''CHAIN'')]),
     (''CHAIN'',
      [Rule (MatchAnd (Match (Prot (Proto TCP)))
              (Match (Src_Ports (L4Ports TCP [(22, 22)]))))
        Return,
       Rule (MatchAnd (Match (Prot (Proto UDP)))
              (Match (Dst_Ports (L4Ports UDP [(80,80)]))))
        Return,
       Rule MatchAny action.Drop])
    ]"

text\<open>No problem here:\<close>
lemma "unfold_ruleset_FORWARD action.Accept
                      (map_of_string_ipv4 allow_only_tcpsport_22_and_udp_dport80) =
  [Rule (MatchAnd (MatchNot (MatchAnd (Match (Prot (Proto TCP))) (Match (Src_Ports (L4Ports TCP [(0x16, 0x16)])))))
         (MatchNot (MatchAnd (Match (Prot (Proto UDP))) (Match (Dst_Ports (L4Ports UDP [(0x50, 0x50)]))))))
   action.Drop,
  Rule MatchAny action.Accept]" by eval

text\<open>
Without having the protocol again in the type for ports, the nnf normalization would mix up
tcp and udp ports and we would end up with a firewall which
accepts everything for every protocol from source port 22 to dst port 80 and drop everything else. 
This was wrong. Now it is correct. Here is exactly how it should (and does) look like:\<close>
lemma "map simple_rule_ipv4_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD action.Accept
                      (map_of_string_ipv4 allow_only_tcpsport_22_and_udp_dport80))))))) =
[ ''DROP     udp  --  0.0.0.0/0            0.0.0.0/0    dports: 0:79'',
  ''DROP     udp  --  0.0.0.0/0            0.0.0.0/0    dports: 81:65535'',
  ''DROP     tcp  --  0.0.0.0/0            0.0.0.0/0   sports: 0:21 '',
  ''DROP     tcp  --  0.0.0.0/0            0.0.0.0/0   sports: 23:65535 '',
  ''ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval

text\<open>Before the fix, we had:
@{term "[''DROP     all  --  0.0.0.0/0            0.0.0.0/0   sports: 0:21 dports: 0:79'',
         ''DROP     all  --  0.0.0.0/0            0.0.0.0/0   sports: 0:21 dports: 81:65535'',
         ''DROP     all  --  0.0.0.0/0            0.0.0.0/0   sports: 23:65535 dports: 0:79'',
         ''DROP     all  --  0.0.0.0/0            0.0.0.0/0   sports: 23:65535 dports: 81:65535'',
         ''ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0    '']"}
Note that we completely lost the protocols!

In a transition period, we had a firewall which accepts everything, which is a sound overapproximation.
(Sound, but useless).
\<close>


subsection\<open>Things the Simple Firewall Cannot Express\<close>
text\<open>This example is based on the same pattern as above. 
It does not cause an error but is a minimal example of what the simple firewall just cannot express 
(and approximation is occurs).\<close>
text\<open>
Description: 
Let's assume we want to write a firewall which first makes sure than only @{const TCP} and @{const UDP} 
is allowed and continues with more fine-grained filtering afterwards.
Basically, we want a first rule which drops everything which is not tcp or udp.
The @{const simple_fw} just cannot express this (other firewall systems can't express this neither).
It needs a bit of work to get this behavior in iptables.
\<close>
definition only_allow_tcp_and_udp :: "(string \<times> 32 common_primitive rule list) list"
  where
  "only_allow_tcp_and_udp \<equiv>
    [(''FORWARD'',
      [Rule MatchAny (Call ''OnlyTCPandUDP''),
       Rule (Match (Extra ''more fine-grained filtering'')) action.Drop
      (*now further more fine-grained filtering rules here*)]),
     (''OnlyTCPandUDP'',
      [Rule (Match (Prot (Proto TCP))) Return,
       Rule (Match (Prot (Proto UDP))) Return,
       Rule MatchAny Log,
       Rule MatchAny Reject])
    ]"

text\<open>Overapproximation removes the check for tcp and udp because the simple firewall cannot
match on negated protocols. This particular example could be expressed by the simple firewall
but the pattern to check for tcp/udp first and do more fine-grained filtering afterwards cannot be 
directly expressed.\<close>
lemma "map simple_rule_ipv4_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD action.Accept
                      (map_of_string_ipv4 only_allow_tcp_and_udp))))))) =
  [''ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval
end
