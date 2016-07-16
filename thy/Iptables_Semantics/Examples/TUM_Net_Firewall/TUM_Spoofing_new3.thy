theory TUM_Spoofing_new3
imports 
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: Chair for Network Architectures and Services (TUM)\<close>
subsection\<open>General Setup\<close>
  
  text\<open>Our IP ranges. If a packet comes from there but from a wrong interface, it is spoofed.\<close>
  (* 
      131.159.14.0/23
      131.159.20.0/23
      192.168.212.0/23
      188.95.233.0/24
      188.95.232.192/27
      188.95.234.0/23
      192.48.107.0/24
      188.95.236.0/22
      185.86.232.0/22
  *)
  definition "everything_but_my_ips = all_but_those_ips [
    (ipv4addr_of_dotdecimal (131,159,14,0), 23),
    (ipv4addr_of_dotdecimal (131,159,20,0), 23),
    (ipv4addr_of_dotdecimal (192,168,212,0), 23),
    (ipv4addr_of_dotdecimal (188,95,233,0), 24),
    (ipv4addr_of_dotdecimal (188,95,232,192), 27),
    (ipv4addr_of_dotdecimal (188,95,234,0), 23),
    (ipv4addr_of_dotdecimal (192,48,107,0), 24),
    (ipv4addr_of_dotdecimal (188,95,236,0), 22),
    (ipv4addr_of_dotdecimal (185,86,232,0), 22)
    ]"
  
  
  definition "ipassmt = [(Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,213,4), 24)]),
  (Iface ''eth1.96'', [(ipv4addr_of_dotdecimal (131,159,14,3), 25)]),
  (Iface ''eth1.108'', [(ipv4addr_of_dotdecimal (131,159,14,129), 26)]),
  (Iface ''eth1.109'', [(ipv4addr_of_dotdecimal (131,159,20,11), 24)]),
  (Iface ''eth1.110'', everything_but_my_ips), (*INET*)
  (Iface ''eth1.116'', [(ipv4addr_of_dotdecimal (131,159,15,131), 26)]),
  (Iface ''eth1.152'', [(ipv4addr_of_dotdecimal (131,159,15,252), 28)]),
  (Iface ''eth1.171'', [(ipv4addr_of_dotdecimal (131,159,15,2), 26)]),
  (Iface ''eth1.173'', [(ipv4addr_of_dotdecimal (131,159,21,252), 24)]),
  (Iface ''eth1.1010'', [(ipv4addr_of_dotdecimal (131,159,15,227), 28)]),
  (Iface ''eth1.1011'', [(ipv4addr_of_dotdecimal (131,159,14,194), 27)]),
  (Iface ''eth1.1012'', [(ipv4addr_of_dotdecimal (131,159,14,238), 28)]),
  (Iface ''eth1.1014'', [(ipv4addr_of_dotdecimal (131,159,15,217), 27)]),
  (Iface ''eth1.1016'', [(ipv4addr_of_dotdecimal (131,159,15,66), 26)]),
  (Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,242), 28)]),
  (Iface ''eth1.1111'', [(ipv4addr_of_dotdecimal (192,168,212,4), 24)]),
  (Iface ''eth1.97'', [(ipv4addr_of_dotdecimal (188,95,233,2), 24)]),
  (Iface ''eth1.1019'', [(ipv4addr_of_dotdecimal (188,95,234,2), 23)]),
  (Iface ''eth1.1020'', [(ipv4addr_of_dotdecimal (192,48,107,2), 24)]),
  (Iface ''eth1.1023'', [(ipv4addr_of_dotdecimal (188,95,236,2), 22)]),
  (Iface ''eth1.1025'', [(ipv4addr_of_dotdecimal (185,86,232,2), 22)]),
  (Iface ''eth1.1024'', everything_but_my_ips) (*transfer net*)]"
  
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt)" by eval

  
  text\<open>We check for all interfaces, except for @{term "Iface ''eth0''"}, which does not need spoofing protection.\<close>
  definition "interfaces = tl (map (iface_sel \<circ> fst) ipassmt)"
  
  lemma "interfaces = 
    [''eth1.96'', ''eth1.108'', ''eth1.109'', ''eth1.110'',
     ''eth1.116'', ''eth1.152'', ''eth1.171'', ''eth1.173'', ''eth1.1010'',
     ''eth1.1011'', ''eth1.1012'', ''eth1.1014'', ''eth1.1016'', ''eth1.1017'',
     ''eth1.1111'', ''eth1.97'', ''eth1.1019'', ''eth1.1020'', ''eth1.1023'',
     ''eth1.1025'', ''eth1.1024'']" by eval
  
  
  
  definition "spoofing_protection fw \<equiv> map (\<lambda>ifce. (ifce, no_spoofing_iface (Iface ifce) (map_of_ipassmt ipassmt) fw)) interfaces"
  
  text\<open>We only consider packets which are @{const CT_New} and @{const ipt_tcp_syn}. Packets which already belong to an established connection are okay be definition.\<close>
  definition "preprocess default_policy fw \<equiv> (upper_closure (packet_assume_new (unfold_ruleset_FORWARD default_policy (map_of_string_ipv4 fw))))"


  value[code] "debug_ipassmt_ipv4 ipassmt []"

text\<open>In all three iterations, we have removed two rules from the ruleset. The first rule excluded
from analysis is the ESTABLISHED rule, as discussed earlier.
The second rule we removed was an exception for an asterisk server. This rule is probably an error 
because this rule prevents any spoofing protection. It was a temporary rule and it should have been
removed but was forgotten. We are investigating ...
\<close>
section\<open>Checking spoofing Protection\<close>

subsubsection\<open>Try 1\<close>
  (*457.224s*)
  parse_iptables_save net_fw_1="iptables-save-2015-05-13_10-53-20_cheating"


  (* _cheating means we needed to remove one "temporary work around" rule.
     This rule prevented all spoofing protection.
     It was for an asterisk server, a temporary rule and it should have been removed but was forgotten, we are investigating ...

  $ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-13_10-53-20 iptables-save-2015-05-13_10-53-20_cheating 
  --- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-13_10-53-20	2015-05-15 15:24:22.768698000 +0200
  +++ iptables-save-2015-05-13_10-53-20_cheating	2015-07-30 11:12:27.515970799 +0200
  @@ -148,7 +148,6 @@
   -A FORWARD -s 131.159.14.197/32 -i eth1.1011 -j ACCEPT
   -A FORWARD -s 131.159.14.221/32 -i eth1.1011 -j ACCEPT
   -A FORWARD -s 131.159.15.252/32 -i eth1.152 -p udp -j ACCEPT
  --A FORWARD -d 131.159.15.252/32 -o eth1.152 -p udp -m multiport --dports 4569,5000:65535 -j ACCEPT
   -A FORWARD -s 131.159.15.247/32 -i eth1.152 -o eth1.110 -j ACCEPT
   -A FORWARD -d 131.159.15.247/32 -i eth1.110 -o eth1.152 -j ACCEPT
   -A FORWARD -s 131.159.15.248/32 -i eth1.152 -o eth1.110 -j ACCEPT
  *)

  value[code] "debug_ipassmt_ipv4 ipassmt (preprocess net_fw_1_FORWARD_default_policy net_fw_1)"
  
  text\<open>the parsed firewall:\<close>
  (*339.034s*)
  value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) net_fw_1"

  (*
  check if pretty-printing is the bottleneck: 
  value[code] "let x = (preprocess net_fw_1_FORWARD_default_policy net_fw_1) in ()"
  *)

  (*372.806s*)
  value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (preprocess net_fw_1_FORWARD_default_policy net_fw_1)"
  
  text\<open>sanity check that @{const ipassmt} is complete\<close>
  (*226.773s*)
  lemma "ipassmt_sanity_defined (preprocess net_fw_1_FORWARD_default_policy net_fw_1) (map_of_ipassmt ipassmt)" by eval
  
  (*287.938s*)
  lemma "spoofing_protection (preprocess net_fw_1_FORWARD_default_policy net_fw_1) =
   [(''eth1.96'',   True),
    (''eth1.108'',  False),
    (''eth1.109'',  False),
    (''eth1.110'',  False),
    (''eth1.116'',  False),
    (''eth1.152'',  False),
    (''eth1.171'',  False),
    (''eth1.173'',  False),
    (''eth1.1010'', False),
    (''eth1.1011'', False),
    (''eth1.1012'', False),
    (''eth1.1014'', False),
    (''eth1.1016'', False),
    (''eth1.1017'', False),
    (''eth1.1111'', False),
    (''eth1.97'',   False),
    (''eth1.1019'', False),
    (''eth1.1020'', False),
    (''eth1.1023'', False),
    (''eth1.1025'', False),
    (''eth1.1024'', False)
   ]" by eval
   text\<open>Spoofing protection fails for all but the 96 VLAN.
   The reason is that the @{text filter_96} chain allows spoofed packets.
   
   An empirical test reveals that the kernel's automatic reverse-path filter (rp) blocks most spoofing attempts.
   Without rp, spoofed packets pass the firewall. We got lucky that rp could be used in our scenario.
   However, the firewall ruleset also features a MAC address filter. This filter was constructed 
   analogously to the spoofing protection filter and, hence, was also broken. rp cannot help in this
   situation.
\<close>

   text\<open>Here is a spoofed packet from IP address @{term "0::ipv4addr"} which is (probably, @{const in_doubt_allow}) accepted in 
         the @{text filter_96} chain.
         Manual inspection of the ruleset and an empirical test demonstrate that this kind of packets is actually accepted.\<close>
   lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''anything but 1.96'', p_oiface = ''eth1.96'',
     p_src = 0, p_dst = ipv4addr_of_dotdecimal (131,159,14,9),
     p_proto = TCP, p_sport = 12345, p_dport = 22, p_tcp_flags= {TCP_SYN},
     p_payload='''', p_tag_ctstate = CT_New\<rparr>
     (unfold_ruleset_FORWARD net_fw_1_FORWARD_default_policy (map_of_string_ipv4 net_fw_1)) Undecided
    = Decision FinalAllow" by eval (*88.265s*)

  

subsubsection\<open>Try 2\<close>

  parse_iptables_save net_fw_2="iptables-save-2015-05-15_14-14-46_cheating"
  (*$ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_14-14-46 iptables-save-2015-05-15_14-14-46_cheating
    --- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_14-14-46	2015-05-15 15:24:22.948698000 +0200
    +++ iptables-save-2015-05-15_14-14-46_cheating	2015-07-30 11:26:37.387934437 +0200
    @@ -148,7 +148,6 @@
     -A FORWARD -s 131.159.14.197/32 -i eth1.1011 -j ACCEPT
     -A FORWARD -s 131.159.14.221/32 -i eth1.1011 -j ACCEPT
     -A FORWARD -s 131.159.15.252/32 -i eth1.152 -p udp -j ACCEPT
    --A FORWARD -d 131.159.15.252/32 -o eth1.152 -p udp -m multiport --dports 4569,5000:65535 -j ACCEPT
     -A FORWARD -s 131.159.15.247/32 -i eth1.152 -o eth1.110 -j ACCEPT
     -A FORWARD -d 131.159.15.247/32 -i eth1.110 -o eth1.152 -j ACCEPT
     -A FORWARD -s 131.159.15.248/32 -i eth1.152 -o eth1.110 -j ACCEPT
  *)

  text\<open>the parsed firewall:\<close>
  value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) net_fw_2"
  
  text\<open>sanity check that @{const ipassmt} is complete\<close>
  (*198.191s*)
  lemma "ipassmt_sanity_defined (preprocess net_fw_2_FORWARD_default_policy net_fw_2) (map_of_ipassmt ipassmt)" by eval
  
  (*255.760s*)
  lemma "spoofing_protection (preprocess net_fw_2_FORWARD_default_policy net_fw_2) =
   [(''eth1.96'',   True),
    (''eth1.108'',  True),
    (''eth1.109'',  True),
    (''eth1.110'',  False), (*INET*)
    (''eth1.116'',  True),
    (''eth1.152'',  True),
    (''eth1.171'',  True),
    (''eth1.173'',  True),
    (''eth1.1010'', True),
    (''eth1.1011'', True),
    (''eth1.1012'', True),
    (''eth1.1014'', True),
    (''eth1.1016'', True),
    (''eth1.1017'', True),
    (''eth1.1111'', True),
    (''eth1.97'',   False), (*VLAN for internal testing, no spoofing protection*)
    (''eth1.1019'', True),
    (''eth1.1020'', True),
    (''eth1.1023'', True),
    (''eth1.1025'', True),
    (''eth1.1024'', False) (*transfer net*)
   ]" by eval

   text\<open>Success for all internal VLANs\<close>


subsection\<open>Try 3\<close>
  parse_iptables_save net_fw_3="iptables-save-2015-05-15_15-23-41_cheating"
  (* $ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_15-23-41 iptables-save-2015-05-15_15-23-41_cheating
  --- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_15-23-41	2015-05-15 15:24:23.180698000 +0200
  +++ iptables-save-2015-05-15_15-23-41_cheating	2015-07-30 11:27:53.583931177 +0200
  @@ -150,7 +150,6 @@
   -A FORWARD -s 131.159.14.197/32 -i eth1.1011 -j ACCEPT
   -A FORWARD -s 131.159.14.221/32 -i eth1.1011 -j ACCEPT
   -A FORWARD -s 131.159.15.252/32 -i eth1.152 -p udp -j ACCEPT
  --A FORWARD -d 131.159.15.252/32 -o eth1.152 -p udp -m multiport --dports 4569,5000:65535 -j ACCEPT
   -A FORWARD -s 131.159.15.247/32 -i eth1.152 -o eth1.110 -j ACCEPT
   -A FORWARD -d 131.159.15.247/32 -i eth1.110 -o eth1.152 -j ACCEPT
   -A FORWARD -s 131.159.15.248/32 -i eth1.152 -o eth1.110 -j ACCEPT
  *)


  text\<open>In the simplified firewall, we see a lot of DROPs in the beginning now\<close>
  value[code] "let x = to_simple_firewall (upper_closure
                      (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))
               in map simple_rule_ipv4_toString x" (*225.039s*)
  
  
  text\<open>the parsed firewall:\<close>
  value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) net_fw_3"
  
  
  text\<open>sanity check that @{const ipassmt} is complete\<close>
  (*177.848s*)
  lemma "ipassmt_sanity_defined (preprocess net_fw_3_FORWARD_default_policy net_fw_3) (map_of_ipassmt ipassmt)" by eval
  
  
  (*217.591s*)
  lemma "spoofing_protection (preprocess net_fw_3_FORWARD_default_policy net_fw_3) =
   [(''eth1.96'',   True),
    (''eth1.108'',  True),
    (''eth1.109'',  True),
    (''eth1.110'',  True), (*INET*)
    (''eth1.116'',  True),
    (''eth1.152'',  True),
    (''eth1.171'',  True),
    (''eth1.173'',  True),
    (''eth1.1010'', True),
    (''eth1.1011'', True),
    (''eth1.1012'', True),
    (''eth1.1014'', True),
    (''eth1.1016'', True),
    (''eth1.1017'', True),
    (''eth1.1111'', True),
    (''eth1.97'',   False), (*VLAN for internal testing, no spoofing protection*)
    (''eth1.1019'', True),
    (''eth1.1020'', True),
    (''eth1.1023'', True),
    (''eth1.1025'', True),
    (''eth1.1024'', True) (*transfer net*)
   ]" by eval
  
  text\<open>now we have spoofing protection!\<close>
  

end
