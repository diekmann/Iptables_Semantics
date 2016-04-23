theory TUM_Simple_FW
imports 
  "TUM_Spoofing_new3"
begin



section{*Printing various version of the simplified firewall*}
  text{*We got lucky that we do not need to abstract over the primitives whcih are not supported by the simple firewall*}
  value[code] "let x = to_simple_firewall (upper_closure
                      (packet_assume_new
                      (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))
               in map simple_rule_toString x" (*341.711s*)

  text{*Abstracting over the interfaces removes a lot of information*}
  value[code] "let x = to_simple_firewall (upper_closure
                      (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
                      (upper_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))
               in map simple_rule_toString x" (*352.424s*)


  text{*If we constrain the inbound interfaces to their assigned ip range, we assume that no spoofed packets arrive.
        This optimizes away the spoofing protection*}
  value[code] "let x = to_simple_firewall (upper_closure
                      (optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
                      (upper_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))
               in map simple_rule_toString x" (*411.281s*)



  text{*If we had spoofing protection in the firewall, then constrain the interfaces, then abstract over the interfaces,
        we get a pretty good ruleset which shows how the firewall partitions the ipv4 space*}
  value[code] "let x = to_simple_firewall (upper_closure
                      (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
                      (upper_closure
                      (optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
                      (upper_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))))
               in map simple_rule_toString x" (*395.192s*)


  text{*This was a whitelisting firewall. Unfortunately, if we build a stricter ruleset, abstracting over the interfaces forces most
        allow rules to be removed (because the packet could come from wron interface).*}
  value[code] "let x = to_simple_firewall (lower_closure
                      (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
                      (lower_closure
                      (optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
                      (lower_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))))
               in map simple_rule_toString x" (*290.862s*)
  text{*This problem is conquered by not constraining the interfaces but rewriting them. Literally, replacing an iiface with the corresponding src ip range.
        This is only possible if the ipassmt does not have zone-spanning interfaces.*}

  text{*If we ignore packets from some interfaces, we can get a better lower closure.
        This transformation is only valid for packets not from eth0, eth1.110, and eth1.1024.
        It is only valid for packets from @{term "(map fst disjoint_ipassmt)"}*}
  definition "disjoint_ipassmt = [(ifce,ips) \<leftarrow> (ipassmt_ignore_wildcard_list ipassmt). ifce \<noteq> Iface ''eth1.110'' \<and> ifce \<noteq> Iface ''eth1.1024'']"
  lemma "ipassmt_sanity_disjoint (map_of disjoint_ipassmt)" by eval
  lemma "set (map fst ipassmt) - {Iface ''eth1.110'', Iface ''eth1.1024''} = set (map fst disjoint_ipassmt)" by eval

  value[code] "let x = to_simple_firewall (lower_closure
                      (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
                      (lower_closure
                      (optimize_matches (iiface_rewrite (map_of_ipassmt disjoint_ipassmt))
                      (lower_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))))
               in map simple_rule_toString x" (*421.137s*)
  value[code] "let x = to_simple_firewall
                      (lower_closure
                      (optimize_matches (iiface_rewrite (map_of_ipassmt disjoint_ipassmt))
                      (lower_closure (packet_assume_new (unfold_ruleset_FORWARD net_fw_3_FORWARD_default_policy (map_of net_fw_3))))))
               in map simple_rule_toString x" (*308.791s*)


end
