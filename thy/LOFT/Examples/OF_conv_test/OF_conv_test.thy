theory OF_conv_test
imports 
  "../../../Iptables_Semantics/Primitive_Matchers/Parser"
  "../../../Simple_Firewall/SimpleFw_toString"
  "../../../Routing/IpRoute_Parser"
  "../../LinuxRouter_OpenFlow_Translation"
  "../../OpenFlow_Serialize"
begin

(*section\<open>Example: Simple Test for Translation to OpenFlow\<close>*)


parse_iptables_save SQRL_fw="iptables-save"

term SQRL_fw
thm SQRL_fw_def
thm SQRL_fw_FORWARD_default_policy_def

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) SQRL_fw"
definition "unfolded = unfold_ruleset_FORWARD SQRL_fw_FORWARD_default_policy (map_of_string_ipv4 SQRL_fw)"
lemma "map (quote_rewrite \<circ> common_primitive_rule_toString) unfolded =
  [''-p icmp -j ACCEPT'',
   ''-i s1-lan -p tcp -m tcp --spts [1024:65535] -m tcp --dpts [80] -j ACCEPT'',
   ''-i s1-wan -p tcp -m tcp --spts [80] -m tcp --dpts [1024:65535] -j ACCEPT'',
   '' -j DROP'']" by eval

lemma "length unfolded = 4" by eval


value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 4" by eval


value[code] "upper_closure (packet_assume_new unfolded)"

lemma "length (lower_closure unfolded) = 4" by eval

lemma "check_simple_fw_preconditions (upper_closure unfolded) = True" by eval
lemma "\<forall>m \<in> get_match`set (upper_closure (packet_assume_new unfolded)). normalized_nnf_match m" by eval
lemma "\<forall>m \<in> get_match`set (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))). normalized_nnf_match m" by eval
lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))))" by eval
lemma "length (to_simple_firewall (upper_closure (packet_assume_new unfolded))) = 4" by eval

lemma "(lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded)))) = lower_closure unfolded"
      "lower_closure unfolded = upper_closure unfolded"
      "(upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded)))) = upper_closure unfolded" by eval+

value[code] "(getParts (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded))))))"

definition "SQRL_fw_simple \<equiv> remdups_rev (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded)))))"
value[code] "SQRL_fw_simple"
lemma "simple_fw_valid SQRL_fw_simple" by eval

(*section\<open>Example: SQRL RTBL\<close>*)

parse_ip_route SQRL_rtbl_main = "ip-route"
value SQRL_rtbl_main
lemma "SQRL_rtbl_main = [\<lparr>routing_match = PrefixMatch 0xA000100 24, metric = 0, routing_action = \<lparr>output_iface = ''s1-lan'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0xA000200 24, metric = 0, routing_action = \<lparr>output_iface = ''s1-wan'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0 0, metric = 0, routing_action = \<lparr>output_iface = ''s1-wan'', next_hop = Some 0xA000201\<rparr>\<rparr>]" by eval
value "dotdecimal_of_ipv4addr 0xA0D2500"
lemma "SQRL_rtbl_main = [
	rr_ctor (10,0,1,0) 24 ''s1-lan'' None 0,
	rr_ctor (10,0,2,0) 24 ''s1-wan'' None 0,
	rr_ctor (0,0,0,0) 0 ''s1-wan'' (Some (10,0,2,1)) 0
	]" 
by eval

definition "SQRL_rtbl_main_sorted \<equiv> rev (sort_key (\<lambda>r. pfxm_length (routing_match r)) SQRL_rtbl_main)"
value SQRL_rtbl_main_sorted
definition "SQRL_ifs \<equiv> [
\<lparr>iface_name = ''s1-lan'', iface_mac = 0x10001\<rparr>,
\<lparr>iface_name = ''s1-wan'', iface_mac = 0x10002\<rparr>
]"
value SQRL_ifs

definition "SQRL_macs \<equiv> [
	(*(''s1-lan'', (ipv4addr_of_dotdecimal (10,0,1,1), 0x3)),*)
	(''s1-lan'', (ipv4addr_of_dotdecimal (10,0,1,2), 0x1)),
	(''s1-lan'', (ipv4addr_of_dotdecimal (10,0,1,3), 0x2)),
	(''s1-wan'', (ipv4addr_of_dotdecimal (10,0,2,1), 0x3))
	(*(''s1-wan'', (ipv4addr_of_dotdecimal (10,0,2,4), 0xeabad0152059))*)
]"

definition "SQRL_ports \<equiv> [
	(''s1-lan'', ''1''),
	(''s1-wan'', ''2'')
]"

(* preconditions (get checked by lr_of_tran, too) *)
lemma "let fw = SQRL_fw_simple in no_oif_match fw \<and> has_default_policy fw \<and> simple_fw_valid fw" by eval
lemma "let rt = SQRL_rtbl_main_sorted in valid_prefixes rt \<and> has_default_route rt" by eval
lemma "let ifs = (map iface_name SQRL_ifs) in distinct ifs" by eval

definition "ofi \<equiv> 
    case (lr_of_tran SQRL_rtbl_main_sorted SQRL_fw_simple (map iface_name SQRL_ifs))
    of (Inr openflow_rules) \<Rightarrow> map (serialize_of_entry (the \<circ> map_of SQRL_ports)) openflow_rules"
lemma "ofi =
[''priority=11,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,nw_dst=10.0.2.0/24,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=1024/0xfc00,tp_dst=80,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=2048/0xf800,tp_dst=80,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=4096/0xf000,tp_dst=80,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=8192/0xe000,tp_dst=80,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=16384/0xc000,tp_dst=80,action=output:2'',
  ''priority=10,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=32768/0x8000,tp_dst=80,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=1024/0xfc00,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=2048/0xf800,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=4096/0xf000,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=8192/0xe000,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=16384/0xc000,action=output:2'',
  ''priority=9,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=80,tp_dst=32768/0x8000,action=output:2'',
  ''priority=8,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=10.0.2.0/24,action=drop'',
  ''priority=7,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,nw_dst=10.0.1.0/24,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=1024/0xfc00,tp_dst=80,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=2048/0xf800,tp_dst=80,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=4096/0xf000,tp_dst=80,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=8192/0xe000,tp_dst=80,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=16384/0xc000,tp_dst=80,action=output:1'',
  ''priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=32768/0x8000,tp_dst=80,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=1024/0xfc00,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=2048/0xf800,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=4096/0xf000,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=8192/0xe000,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=16384/0xc000,action=output:1'',
  ''priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=32768/0x8000,action=output:1'',
  ''priority=4,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=10.0.1.0/24,action=drop'',
  ''priority=3,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=1024/0xfc00,tp_dst=80,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=2048/0xf800,tp_dst=80,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=4096/0xf000,tp_dst=80,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=8192/0xe000,tp_dst=80,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=16384/0xc000,tp_dst=80,action=output:2'',
  ''priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=32768/0x8000,tp_dst=80,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=1024/0xfc00,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=2048/0xf800,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=4096/0xf000,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=8192/0xe000,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=16384/0xc000,action=output:2'',
  ''priority=1,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,tp_src=80,tp_dst=32768/0x8000,action=output:2'',
  ''priority=0,hard_timeout=0,idle_timeout=0,dl_type=0x800,action=drop'']" by eval

value[code] "ofi"

(*ML\<open>
	val evterm = the (Code_Evaluation.dynamic_value @{context} @{term "intersperse (Char Nibble0 NibbleA) ofi"});
	val opstr = Syntax.string_of_term (Config.put show_markup false @{context}) evterm;
	File.write (Path.explode (File.platform_path(Resources.master_directory @{theory}) ^ "/pretty_str.txt")) opstr;
\<close>*)

end
