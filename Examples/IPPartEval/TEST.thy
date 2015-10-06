theory TEST
imports
  "../../Primitive_Matchers/Parser"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Primitive_Matchers/Interface_Replace"
begin

definition "iface_try_rewrite ipassmt rs \<equiv> if ipassmt_sanity_disjoint (map_of ipassmt) \<and> ipassmt_sanity_defined rs (map_of ipassmt) then
  optimize_matches (iiface_rewrite (map_of_ipassmt ipassmt)) rs
  else
  optimize_matches (iiface_constrain (map_of_ipassmt ipassmt)) rs"

theorem iface_try_rewrite:
  assumes simplers: "simple_ruleset rs"
      and normalized: "\<forall> m \<in> get_match ` set rs. normalized_nnf_match m"
      and wf_ipassmt1: "ipassmt_sanity_nowildcards (map_of ipassmt)" and wf_ipassmt2: "distinct (map fst ipassmt)"
      and nospoofing: "\<exists>ips. (map_of ipassmt) (Iface (p_iiface p)) = Some ips \<and> p_src p \<in> ipv4cidr_union_set (set ips)"
  shows "(common_matcher, \<alpha>),p\<turnstile> \<langle>iface_try_rewrite ipassmt rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t \<longleftrightarrow> (common_matcher, \<alpha>),p\<turnstile> \<langle>rs, s\<rangle> \<Rightarrow>\<^sub>\<alpha> t"
  apply(simp add: iface_try_rewrite_def)
  apply(simp add: map_of_ipassmt_def wf_ipassmt1 wf_ipassmt2)
  apply(intro conjI impI)
   apply(elim conjE)
   using iiface_rewrite(1)[OF simplers normalized wf_ipassmt1 _ nospoofing] apply blast
  using iiface_constrain(1)[OF simplers normalized wf_ipassmt1] nospoofing apply force
  done

definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a))
              (closure
              (iface_try_rewrite ipassmt
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"


definition preprocess_keep_ifce where
  "preprocess_keep_ifce unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches abstract_for_simple_firewall
              (closure
              (optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"


datatype ipt_chain = FWD | INP 

fun get_unfold where
  "get_unfold FWD = unfold_ruleset_FORWARD" |
  "get_unfold INP = unfold_ruleset_INPUT"

fun ipt_chain_toSting where
  "ipt_chain_toSting FWD = ''FORWARD''" |
  "ipt_chain_toSting INPO = ''INPUT''"

definition bench where
  "bench closure f ipassmt def fw_in \<equiv> let fw = preprocess (get_unfold f) closure ipassmt def fw_in in 
      (length ((get_unfold f) def (map_of fw_in)), length (preprocess_keep_ifce (get_unfold f) closure ipassmt def fw_in), length fw, length (getParts fw), length (buildParts ssh fw), length (buildParts http fw))"
definition view where
  "view closure f ipassmt def fw_in \<equiv> let fw = preprocess (get_unfold f) closure ipassmt def fw_in in 
      (''x'',
       map (simple_rule_iptables_save_toString (ipt_chain_toSting f)) (preprocess_keep_ifce (get_unfold f) closure ipassmt def fw_in),
       map (simple_rule_iptables_save_toString (ipt_chain_toSting f)) fw,
       map pretty_wordinterval (getParts fw),
       (build ssh fw),
       (build http fw))"





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

(*
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
*)

(*
context
begin
 private local_setup \<open>
    local_setup_parse_iptables_save "filter" @{binding fw4} ["..", "..", "..", (*private*)]
   \<close>
 thm fw4_def

  value[code] "bench upper_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"
  value[code] "view upper_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"

  definition "mysql = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=3306, pc_tag_ctstate=CT_New\<rparr>"
  value[code] "let fw = preprocess (get_unfold INP) upper_closure ipassmt_generic fw4_INPUT_default_policy fw4 in
               map pretty_wordinterval (buildParts mysql fw)"

  value[code] "bench lower_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"
  value[code] "view lower_closure INP ipassmt_generic fw4_INPUT_default_policy fw4"
end
*)


context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw5} ["linux.gda.pl", "firewallp.txt"]
    \<close>
  thm fw5_def

  value[code] "bench upper_closure FWD ipassmt_generic fw5_FORWARD_default_policy fw5"
  value[code] "view upper_closure FWD ipassmt_generic fw5_FORWARD_default_policy fw5"

  value[code] "bench lower_closure FWD ipassmt_generic fw5_FORWARD_default_policy fw5"
  value[code] "view lower_closure FWD ipassmt_generic fw5_FORWARD_default_policy fw5"
end


context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw6} ["openvpn.eu", "iptables-save"]
    \<close>
  thm fw6_def

  private  definition "ipassmt6 = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,0,0),24)]),
  (Iface ''eth1'', [(ipv4addr_of_dotdecimal (192,168,2,0),24)])]"


  value[code] "bench upper_closure FWD ipassmt6 fw6_FORWARD_default_policy fw6"
  value[code] "view upper_closure FWD ipassmt6 fw6_FORWARD_default_policy fw6"

  value[code] "bench lower_closure FWD ipassmt6 fw6_FORWARD_default_policy fw6"
  value[code] "view lower_closure FWD ipassmt6 fw6_FORWARD_default_policy fw6"
end



context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw7} ["openwrt.org", "iptables-save-AA.txt_fixed_newline"]
    \<close>
  thm fw7_def

  private  definition "ipassmt7 = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,1,0),24)]),
  (*(Iface ''eth0.2'', [(ipv4addr_of_dotdecimal (192,168,2,0),24)]), cannot infer*)
  (Iface ''tun0'', [(ipv4addr_of_dotdecimal (10,8,0,0),24)]),
  (Iface ''br-lan'', [(ipv4addr_of_dotdecimal (192,168,1,0),24)])]"


  value[code] "bench upper_closure FWD ipassmt7 fw7_FORWARD_default_policy fw7"
  value[code] "view upper_closure FWD ipassmt7 fw7_FORWARD_default_policy fw7"

  value[code] "bench lower_closure FWD ipassmt7 fw7_FORWARD_default_policy fw7"
  value[code] "view lower_closure FWD ipassmt7 fw7_FORWARD_default_policy fw7"
end



context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw8} ["pastebin.com_bbWXHaTn", "iptables-save"]
    \<close>
  thm fw8_def

  value[code] "bench upper_closure FWD ipassmt_generic fw8_FORWARD_default_policy fw8"
  value[code] "view upper_closure FWD ipassmt_generic fw8_FORWARD_default_policy fw8"

  value[code] "bench lower_closure FWD ipassmt_generic fw8_FORWARD_default_policy fw8"
  value[code] "view lower_closure FWD ipassmt_generic fw8_FORWARD_default_policy fw8"
end



context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw9} ["rlworkman.net", "iptables-save"]
    \<close>
  thm fw9_def
 
  (*I loaded the script on my local machine*)
  private definition "ipassmt9 = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,13,0),24)]),
  (Iface ''ppp0'', all_but_those_ips [(ipv4addr_of_dotdecimal (192,168,13,0),24), (ipv4addr_of_dotdecimal (127,0,0,0),8)])]"

  value[code] "bench upper_closure FWD ipassmt9 fw9_FORWARD_default_policy fw9"
  value[code] "view upper_closure FWD ipassmt9 fw9_FORWARD_default_policy fw9"

  (*quite good results*)
  value[code] "bench lower_closure FWD ipassmt9 fw9_FORWARD_default_policy fw9"
  value[code] "view lower_closure FWD ipassmt9 fw9_FORWARD_default_policy fw9"


  value[code] "bench upper_closure INP ipassmt9 fw9_INPUT_default_policy fw9"
  value[code] "view upper_closure INP ipassmt9 fw9_INPUT_default_policy fw9"

  value[code] "bench lower_closure INP ipassmt9 fw9_INPUT_default_policy fw9"
  value[code] "view lower_closure INP ipassmt9 fw9_INPUT_default_policy fw9"
end



context
begin
  private local_setup \<open>
     local_setup_parse_iptables_save "filter" @{binding fw10} ["sargon", "iptables-save.txt"]
    \<close>
  thm fw10_def

  value[code] "bench upper_closure INP ipassmt_generic fw10_INPUT_default_policy fw10"
  value[code] "view upper_closure INP ipassmt_generic fw10_INPUT_default_policy fw10"

  value[code] "bench lower_closure INP ipassmt_generic fw10_INPUT_default_policy fw10"
  value[code] "view lower_closure INP ipassmt_generic fw10_INPUT_default_policy fw10"
end

end
