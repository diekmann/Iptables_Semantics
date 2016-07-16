theory SQRL_2015_nospoof
imports 
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: Implementing spoofing protection\<close>
  
  definition "everything_but_private_ips = all_but_those_ips [
    (ipv4addr_of_dotdecimal (192,168,0,0), 16),
    (ipv4addr_of_dotdecimal (172,16,0,0), 12),
    (ipv4addr_of_dotdecimal (10,0,0,0), 8)
    ]"
  
  definition "ipassmt = [(Iface ''ldit'', [(ipv4addr_of_dotdecimal (10,13,42,136), 29)]),
  (Iface ''lmd'', [(ipv4addr_of_dotdecimal (10,13,42,128), 29)]),
  (Iface ''loben'', [(ipv4addr_of_dotdecimal (10,13,42,144), 28)]),
  (Iface ''wg'', [(ipv4addr_of_dotdecimal (10,13,42,176), 28)]),
  (Iface ''wt'', [(ipv4addr_of_dotdecimal (10,13,42,160), 28)]),
  (Iface ''lup'', everything_but_private_ips), (*INET*)
  (*no protection fo the following interfaces*)
  (Iface ''lo'', [(0,0)]),
  (Iface ''vpriv'', [(0,0)]),
  (Iface ''vshit'', [(0,0)]),
  (Iface ''vocb'', [(0,0)]),
  (Iface ''lua'', [(0,0)])
  ]"
  
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt)" by eval

  lemma"ipassmt_sanity_complete ipassmt" by eval (* obviously with all these 0/0 ifaces*)
  
  
  definition "interfaces = (map (iface_sel \<circ> fst) ipassmt)"
  
  lemma "interfaces = [''ldit'', ''lmd'', ''loben'', ''wg'', ''wt'', ''lup'', ''lo'', ''vpriv'', ''vshit'', ''vocb'', ''lua'']" by eval
  
  definition "spoofing_protection fw \<equiv> map (\<lambda>ifce. (ifce, no_spoofing_iface (Iface ifce) (map_of_ipassmt ipassmt) fw)) interfaces"
  
  text\<open>We only consider packets which are @{const CT_New}. Packets which already belong to an established connection are okay be definition.
  A very interesting side aspect: In theory, this theory only supports the filter table.
  For efficiency, the firewall's administrator implemented the spoofing protection in the raw table's PREROUTING chain.
  Because the administrator only used actions which are supported by our semantics, we can apply our theory here.
\<close>
  definition "preprocess default_policy fw \<equiv> (upper_closure (ctstate_assume_new (unfold_ruleset_CHAIN ''PREROUTING'' default_policy (map_of_string_ipv4 fw))))"

  local_setup \<open>
    parse_iptables_save "raw" @{binding raw_fw1} ["2015_aug_iptables-save-spoofing-protection"]
   \<close>
  thm raw_fw1_def
  thm raw_fw1_PREROUTING_default_policy_def

  text\<open>sanity check that @{const ipassmt} is complete\<close>
  (*This actually caught a typo I made in the ipassmt!*)
  lemma "ipassmt_sanity_defined (preprocess raw_fw1_PREROUTING_default_policy raw_fw1) (map_of_ipassmt ipassmt)" by eval

  value[code] "debug_ipassmt_ipv4 ipassmt (preprocess raw_fw1_PREROUTING_default_policy raw_fw1)"

  text\<open>The administrator wanted to make sure that he will not lock himself out of the firewall.
  Hence, we must verify that ssh packets are still accepted by the firewall.
  Therefore, we also load the filter table.\<close>

  parse_iptables_save filter_fw1="2015_aug_iptables-save-spoofing-protection"
  thm filter_fw1_def

   (* To verify that we can still access the firewall via ssh, we assume that the ssh rate limiting rule will not drop us.
      Therefore, we change this --and only this-- rule:
     --A SSHLimit -m recent --update --seconds 60 --hitcount 2 --name SSHA --mask 255.255.255.255 --rsource -j DROP
     +-A SSHLimit -m recent --update --seconds 60 --hitcount 2 --name SSHA --mask 255.255.255.255 --rsource -j LOG
   *)


  value[code] "remdups (collect_ifaces (unfold_ruleset_INPUT filter_fw1_INPUT_default_policy (map_of_string_ipv4 filter_fw1)))"

  lemma "ipassmt_sanity_defined (unfold_ruleset_INPUT filter_fw1_INPUT_default_policy (map_of_string_ipv4 filter_fw1)) (map_of_ipassmt ipassmt)" by eval
  lemma "ipassmt_sanity_defined (unfold_ruleset_FORWARD filter_fw1_FORWARD_default_policy (map_of_string_ipv4 filter_fw1)) (map_of_ipassmt ipassmt)" by eval
  lemma "ipassmt_sanity_defined (unfold_ruleset_OUTPUT filter_fw1_OUTPUT_default_policy (map_of_string_ipv4 filter_fw1)) (map_of_ipassmt ipassmt)" by eval


  text\<open>the parsed firewall raw table:\<close>
  value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) raw_fw1"

  text\<open>Printing the simplified PREROUTING chain of the raw table:\<close>
  value[code] "let x = to_simple_firewall (upper_closure
                       (unfold_ruleset_CHAIN ''PREROUTING'' raw_fw1_PREROUTING_default_policy (map_of raw_fw1)))
               in map simple_rule_ipv4_toString x"


  text\<open>First, we check that NEW and ESTABLISHED ssh packets from the Internet are definitely allowed by the firewall:
    The packets must be allowed by both the PREROUTING and INPUT chain.
    We use @{const in_doubt_deny} to be absolutely sure that these packets will be accepted by the firewall.\<close>
  definition "ssh_packet_new = \<lparr>p_iiface = ''lup'', p_oiface = ''anything'',
     p_src = ipv4addr_of_dotdecimal (123,123,123,123), p_dst = ipv4addr_of_dotdecimal (131,159,14,9),
     p_proto = TCP, p_sport = 12345, p_dport = 22, p_tcp_flags = {TCP_SYN},
     p_payload='''', p_tag_ctstate = CT_New\<rparr>"

  definition "ssh_packet_established = ssh_packet_new\<lparr>p_tag_ctstate := CT_Established\<rparr>"

  text\<open>it is possible to reach the firewall over ssh\<close>
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny) ssh_packet_new
     (unfold_ruleset_CHAIN ''PREROUTING'' raw_fw1_PREROUTING_default_policy (map_of_string_ipv4 raw_fw1)) Undecided
     = Decision FinalAllow" by eval
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny) ssh_packet_established
     (unfold_ruleset_CHAIN ''PREROUTING'' raw_fw1_PREROUTING_default_policy (map_of_string_ipv4 raw_fw1)) Undecided
     = Decision FinalAllow" by eval

  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny) ssh_packet_new
     (unfold_ruleset_INPUT filter_fw1_INPUT_default_policy (map_of_string_ipv4 filter_fw1)) Undecided
     = Decision FinalAllow" by eval
  lemma "approximating_bigstep_fun (common_matcher, in_doubt_deny) ssh_packet_established
     (unfold_ruleset_INPUT filter_fw1_INPUT_default_policy (map_of_string_ipv4 filter_fw1)) Undecided
     = Decision FinalAllow" by eval

  
  text\<open>Finally, we show that the PREROUTING chain correctly implements spoofing protection.\<close>
  lemma "spoofing_protection (preprocess raw_fw1_PREROUTING_default_policy raw_fw1) =
       [(''ldit'', True),
        (''lmd'', True),
        (''loben'', True),
        (''wg'', True),
        (''wt'', True),
        (''lup'', True),
        (''lo'', True),
        (''vpriv'', True),
        (''vshit'', True),
        (''vocb'', True),
        (''lua'', True)]" by eval

end
