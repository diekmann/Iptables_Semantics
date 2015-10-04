theory TEST
imports
  "../../Primitive_Matchers/Parser"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Primitive_Matchers/Interface_Replace"
begin


definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
              (closure
              (optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"


datatype ipt_chain = FWD | INP 

fun get_unfold where
  "get_unfold FWD = unfold_ruleset_FORWARD" |
  "get_unfold INP = unfold_ruleset_INPUT"

definition bench where
  "bench closure f ipassmt def fw_in \<equiv> let fw = preprocess (get_unfold f) closure ipassmt def fw_in in 
      (length ((get_unfold f) def (map_of fw_in)), length fw, length (getParts fw), length (buildParts ssh fw), length (buildParts http fw))"
definition view where
  "view closure f ipassmt def fw \<equiv> let fw = preprocess (get_unfold f) closure ipassmt def fw in 
      (''x'', map simple_rule_toString fw, map pretty_wordinterval (getParts fw), (build ssh fw), (build http fw))"





context begin
 private definition "everything_but_private_ips = all_but_those_ips [
    (ipv4addr_of_dotdecimal (192,168,0,0), 16),
    (ipv4addr_of_dotdecimal (172,16,0,0), 12),
    (ipv4addr_of_dotdecimal (10,0,0,0), 8)
    ]"
  
  private definition "ipassmt = [(Iface ''ldit'', [(ipv4addr_of_dotdecimal (10,13,42,136), 29)]),
  (Iface ''lmd'', [(ipv4addr_of_dotdecimal (10,13,42,128), 29)]),
  (Iface ''loben'', [(ipv4addr_of_dotdecimal (10,13,42,144), 28)]),
  (Iface ''wg'', [(ipv4addr_of_dotdecimal (10,13,42,176), 28)]),
  (Iface ''wt'', [(ipv4addr_of_dotdecimal (10,13,42,160), 28)]),
  (Iface ''lup'', everything_but_private_ips), (*INET*)
  (Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''vpriv'', [(0,0)]),
  (Iface ''vshit'', [(0,0)]),
  (Iface ''vocb'', [(0,0)]),
  (Iface ''lua'', [(0,0)])
  ]"
  

 private local_setup \<open>
    local_setup_parse_iptables_save "filter" @{binding fw1} ["configs_sqrl_shorewall", "2015_aug_iptables-save-spoofing-protection"]
   \<close>

  value[code] "bench upper_closure FWD ipassmt fw1_FORWARD_default_policy fw1"
  value[code] "view upper_closure FWD ipassmt fw1_FORWARD_default_policy fw1"

  value[code] "bench lower_closure FWD ipassmt fw1_FORWARD_default_policy fw1"
  value[code] "view lower_closure FWD ipassmt fw1_FORWARD_default_policy fw1"


  value[code] "bench upper_closure INP ipassmt fw1_INPUT_default_policy fw1"
  value[code] "view upper_closure INP ipassmt fw1_INPUT_default_policy fw1"

  value[code] "bench lower_closure INP ipassmt fw1_INPUT_default_policy fw1"
  value[code] "view lower_closure INP ipassmt fw1_INPUT_default_policy fw1"

 private local_setup \<open>
    local_setup_parse_iptables_save "filter" @{binding fw2} ["configs_sqrl_shorewall", "2014_sep_iptables-saveakachan"]
   \<close>
  value[code] "Semantics_Goto.rewrite_Goto fw2"


  value[code] "bench upper_closure FWD ipassmt fw2_FORWARD_default_policy (Semantics_Goto.rewrite_Goto fw2)"
  value[code] "view upper_closure FWD ipassmt fw2_FORWARD_default_policy (Semantics_Goto.rewrite_Goto fw2)"


  value[code] "bench lower_closure FWD ipassmt fw2_FORWARD_default_policy (Semantics_Goto.rewrite_Goto fw2)"
  value[code] "view lower_closure FWD ipassmt fw2_FORWARD_default_policy (Semantics_Goto.rewrite_Goto fw2)"
end

context
begin
  private definition "ipassmt2 = [(Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,1,0), 24)]),
  (Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)])
  ]"
 private local_setup \<open>
    local_setup_parse_iptables_save "filter" @{binding fw3} ["configs_synology_diskstation_ds414", "iptables-save_jun_2015_legacyifacerules"]
   \<close>

  value[code] "bench upper_closure INP ipassmt2 fw3_INPUT_default_policy fw3"
  value[code] "view upper_closure INP ipassmt2 fw3_INPUT_default_policy fw3"


  definition web8080 where "web8080 = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=8080, pc_tag_ctstate=CT_New\<rparr>"

  value[code] "let fw = preprocess (get_unfold INP) upper_closure ipassmt2 fw3_INPUT_default_policy fw3 in
               map pretty_wordinterval (buildParts web8080 fw)"

  value[code] "bench lower_closure INP ipassmt2 fw3_INPUT_default_policy fw3"
  value[code] "view lower_closure INP ipassmt2 fw3_INPUT_default_policy fw3"

end

definition "ipassmt_generic = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)])]"

context
begin
 private local_setup \<open>
    local_setup_parse_iptables_save "filter" @{binding fw4} ["gopherproxy.meulie.net", "iptables-save"]
   \<close>
 thm fw4_def

  value[code] "bench upper_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"
  value[code] "view upper_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"

  value[code] "bench lower_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"
  value[code] "view lower_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"

end

end
