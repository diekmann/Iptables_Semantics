theory Analyze_topos_generated
imports 
  "../../Primitive_Matchers/Parser"
begin



parse_iptables_save factory_fw="imaginray_factory_network.iptables-save.by-linux-kernel"

thm factory_fw_def
thm factory_fw_FORWARD_default_policy_def

lemma "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) factory_fw =
 [(''FORWARD'',
   [''-s 10.8.2.2/32 -d 10.8.8.1/32 -i Bot2 -o Watchdog -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.8.2.1/32 -d 10.8.8.1/32 -i Bot1 -o Watchdog -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.8.1.1/32 -d 10.8.0.1/32 -i MissionControl1 -o AdminPc -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.8.1.2/32 -d 10.8.0.1/32 -i MissionControl2 -o AdminPc -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.8.2.2/32 -d 10.8.1.2/32 -i Bot2 -o MissionControl2 -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.8.2.1/32 -d 10.8.1.1/32 -i Bot1 -o MissionControl1 -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.0.0.1/32 -d 10.0.0.2/32 -i Statistics -o SensorSink -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.0.0.2/32 -d 10.0.1.2/32 -i SensorSink -o Webcam -m state --state ESTABLISHED -j ACCEPT'',
    ''-s 10.0.1.1/32 -d 10.0.0.2/32 -i PresenceSensor -o SensorSink -j ACCEPT'',
    ''-s 10.0.1.2/32 -d 10.0.0.2/32 -i Webcam -o SensorSink -j ACCEPT'',
    ''-s 10.0.1.3/32 -d 10.0.0.2/32 -i TempSensor -o SensorSink -j ACCEPT'',
    ''-s 10.0.1.4/32 -d 10.0.0.2/32 -i FireSensor -o SensorSink -j ACCEPT'',
    ''-s 10.0.0.2/32 -d 10.0.0.1/32 -i SensorSink -o Statistics -j ACCEPT'',
    ''-s 10.8.1.1/32 -d 10.8.2.1/32 -i MissionControl1 -o Bot1 -j ACCEPT'',
    ''-s 10.8.1.1/32 -d 10.8.2.2/32 -i MissionControl1 -o Bot2 -j ACCEPT'',
    ''-s 10.8.1.2/32 -d 10.8.2.2/32 -i MissionControl2 -o Bot2 -j ACCEPT'',
    ''-s 10.8.0.1/32 -d 10.8.1.2/32 -i AdminPc -o MissionControl2 -j ACCEPT'',
    ''-s 10.8.0.1/32 -d 10.8.1.1/32 -i AdminPc -o MissionControl1 -j ACCEPT'',
    ''-s 10.8.8.1/32 -d 10.8.2.1/32 -i Watchdog -o Bot1 -j ACCEPT'',
    ''-s 10.8.8.1/32 -d 10.8.2.2/32 -i Watchdog -o Bot2 -j ACCEPT'']),
  (''INPUT'', []),
  (''OUTPUT'', [])]" by eval

definition "unfolded_FORWARD = unfold_ruleset_FORWARD factory_fw_FORWARD_default_policy (map_of_string_ipv4 (factory_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_FORWARD)"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_FORWARD)"


value[code] "upper_closure (packet_assume_new unfolded_FORWARD)"

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall 
          (upper_closure (packet_assume_new unfolded_FORWARD))))" by eval

lemma "simple_fw_valid (to_simple_firewall (upper_closure
              (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"
by eval
lemma "simple_fw_valid (to_simple_firewall (lower_closure
              (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"
by eval


value[code] "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure
              (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"

value[code] "map simple_rule_ipv4_toString (to_simple_firewall (lower_closure
              (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"



(*Interfaces be gone! necessary for ip partition!*)
definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a
                                                                 | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (closure
              (iface_try_rewrite ipassmt None
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"

  (*incomplete, but we won't need it anyway*)
 definition ipassmt :: "(iface \<times> (32 word \<times> nat) list) list" where
 "ipassmt = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''Statistics'', [(ipv4addr_of_dotdecimal (10,0,0,1),32)])
  ]"
  lemma "distinct (map fst ipassmt)" by eval
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt)" by eval
  value[code] "map_of_ipassmt ipassmt"

value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt factory_fw_FORWARD_default_policy factory_fw)"

lemma "access_matrix_pretty_ipv4 parts_connection_http (
      preprocess unfold_ruleset_FORWARD upper_closure ipassmt factory_fw_FORWARD_default_policy factory_fw) =
([ (''10.8.8.1'', ''10.8.8.1''),
   (''10.8.2.2'', ''10.8.2.2''),
   (''10.8.2.1'', ''10.8.2.1''),
   (''10.8.1.2'', ''10.8.1.2''),
   (''10.8.1.1'', ''10.8.1.1''),
   (''10.8.0.1'', ''10.8.0.1''),
   (''10.0.1.1'', ''{10.0.1.1 .. 10.0.1.4}''),
   (''10.0.0.2'', ''10.0.0.2''),
   (''10.0.0.1'', ''10.0.0.1''),
   (''0.0.0.0'',  ''{0.0.0.0 .. 10.0.0.0} u {10.0.0.3 .. 10.0.1.0} u {10.0.1.5 .. 10.8.0.0} u ''@
                  ''{10.8.0.2 .. 10.8.1.0} u {10.8.1.3 .. 10.8.2.0} u {10.8.2.3 .. 10.8.8.0} u {10.8.8.2 .. 255.255.255.255}'')],
  [(''10.8.8.1'', ''10.8.2.2''),
   (''10.8.8.1'', ''10.8.2.1''),
   (''10.8.1.2'', ''10.8.2.2''),
   (''10.8.1.1'', ''10.8.2.2''),
   (''10.8.1.1'', ''10.8.2.1''),
   (''10.8.0.1'', ''10.8.1.2''),
   (''10.8.0.1'', ''10.8.1.1''),
   (''10.0.1.1'', ''10.0.0.2''),
   (''10.0.0.2'', ''10.0.0.1'')])" by eval

text\<open>@{const CT_Established}\<close>
lemma "access_matrix_pretty_ipv4 parts_connection_ssh 
    (to_simple_firewall (upper_closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a
                                                                 | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (upper_closure
              (iface_try_rewrite ipassmt None
              (upper_closure
              (optimize_matches (ctstate_assume_state CT_Established)
              (unfold_ruleset_FORWARD factory_fw_FORWARD_default_policy (map_of factory_fw))))))))) =
([(''10.8.8.1'', ''10.8.8.1''),
   (''10.8.2.2'', ''10.8.2.2''),
   (''10.8.2.1'', ''10.8.2.1''),
   (''10.8.1.2'', ''10.8.1.2''),
   (''10.8.1.1'', ''10.8.1.1''),
   (''10.8.0.1'', ''10.8.0.1''),
   (''10.0.1.1'', ''10.0.1.1 u {10.0.1.3 .. 10.0.1.4}''),
   (''10.0.0.1'', ''10.0.0.1 u 10.0.1.2''),
   (''10.0.0.2'', ''10.0.0.2''),
   (''0.0.0.0'',  ''{0.0.0.0 .. 10.0.0.0} u {10.0.0.3 .. 10.0.1.0} u {10.0.1.5 .. 10.8.0.0} u ''@
                  ''{10.8.0.2 .. 10.8.1.0} u {10.8.1.3 .. 10.8.2.0} u {10.8.2.3 .. 10.8.8.0} u {10.8.8.2 .. 255.255.255.255}'')],
  [(''10.8.8.1'', ''10.8.2.2''),
   (''10.8.8.1'', ''10.8.2.1''),
   (''10.8.2.2'', ''10.8.8.1''),
   (''10.8.2.2'', ''10.8.1.2''),
   (''10.8.2.1'', ''10.8.8.1''),
   (''10.8.2.1'', ''10.8.1.1''),
   (''10.8.1.2'', ''10.8.2.2''),
   (''10.8.1.2'', ''10.8.0.1''),
   (''10.8.1.1'', ''10.8.2.2''),
   (''10.8.1.1'', ''10.8.2.1''),
   (''10.8.1.1'', ''10.8.0.1''),
   (''10.8.0.1'', ''10.8.1.2''),
   (''10.8.0.1'', ''10.8.1.1''),
   (''10.0.1.1'', ''10.0.0.2''),
   (''10.0.0.1'', ''10.0.0.2''),
   (''10.0.0.2'', ''10.0.0.1'')])" by eval

end