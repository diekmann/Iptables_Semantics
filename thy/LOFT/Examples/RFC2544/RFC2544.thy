theory RFC2544
imports 
  "../../../Iptables_Semantics/Primitive_Matchers/Parser"
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

lemma "length unfolded = 26" by eval

value[code] "unfolded"
value[code] "(upper_closure unfolded)"
value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded)"
lemma "length (upper_closure unfolded) = 26" by eval


value[code] "upper_closure (packet_assume_new unfolded)"

lemma "length (lower_closure unfolded) = 26" by eval

lemma "check_simple_fw_preconditions (upper_closure unfolded)" by eval
lemma "\<forall>m \<in> get_match`set (upper_closure (packet_assume_new unfolded)). normalized_nnf_match m" by eval
lemma "\<forall>m \<in> get_match`set (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))). normalized_nnf_match m" by eval
lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded))))" by eval
lemma "length (to_simple_firewall (upper_closure (packet_assume_new unfolded))) = 26" by eval

lemma "(lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded)))) = lower_closure unfolded"
      "lower_closure unfolded = upper_closure unfolded"
      "(upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded)))) = upper_closure unfolded" by eval+

value[code] "(getParts (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded))))))"

definition "SQRL_fw_simple \<equiv> remdups_rev (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded)))))"
value[code] "SQRL_fw_simple"
lemma "simple_fw_valid SQRL_fw_simple" by eval

parse_ip_route SQRL_rtbl_main = "ip-route"
value SQRL_rtbl_main
lemma "SQRL_rtbl_main = [\<lparr>routing_match = PrefixMatch 0xC6120100 24, metric = 0, routing_action = \<lparr>output_iface = ''ip1'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0xC6130100 24, metric = 0, routing_action = \<lparr>output_iface = ''op1'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0 0, metric = 0, routing_action = \<lparr>output_iface = ''op1'', next_hop = Some 0xC6130102\<rparr>\<rparr>]" by eval
lemma "SQRL_rtbl_main = [
	rr_ctor (198,18,1,0) 24 ''ip1'' None 0,
	rr_ctor (198,19,1,0) 24 ''op1'' None 0,
	rr_ctor (0,0,0,0) 0 ''op1'' (Some (198,19,1,2)) 0
	]" 
by eval

definition "SQRL_ports \<equiv> [
	(''ip1'', ''1''),
	(''op1'', ''2'')
]"

definition "ofi \<equiv> 
    case (lr_of_tran SQRL_rtbl_main SQRL_fw_simple (map fst SQRL_ports))
    of (Inr openflow_rules) \<Rightarrow> map (serialize_of_entry (the \<circ> map_of SQRL_ports)) openflow_rules"
lemma "ofi =
[''priority=27,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=198.18.1.0/24,action=drop'',
  ''priority=26,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=198.19.1.0/24,action=drop'',
  ''priority=25,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.1.1/32,nw_dst=192.18.101.1/32,action=drop'',
  ''priority=24,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.2.2/32,nw_dst=192.18.102.2/32,action=drop'',
  ''priority=23,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.3.3/32,nw_dst=192.18.103.3/32,action=drop'',
  ''priority=22,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.4.4/32,nw_dst=192.18.104.4/32,action=drop'',
  ''priority=21,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.5.5/32,nw_dst=192.18.105.5/32,action=drop'',
  ''priority=20,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.6.6/32,nw_dst=192.18.106.6/32,action=drop'',
  ''priority=19,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.7.7/32,nw_dst=192.18.107.7/32,action=drop'',
  ''priority=18,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.8.8/32,nw_dst=192.18.108.8/32,action=drop'',
  ''priority=17,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.9.9/32,nw_dst=192.18.109.9/32,action=drop'',
  ''priority=16,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.10.10/32,nw_dst=192.18.110.10/32,action=drop'',
  ''priority=15,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.11.11/32,nw_dst=192.18.111.11/32,action=drop'',
  ''priority=14,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.12.12/32,nw_dst=192.18.112.12/32,action=drop'',
  ''priority=13,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.19.1.2/32,nw_dst=192.19.65.1/32,action=output:2'',
  ''priority=12,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.13.13/32,nw_dst=192.18.113.13/32,action=drop'',
  ''priority=11,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.14.14/32,nw_dst=192.18.114.14/32,action=drop'',
  ''priority=10,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.15.15/32,nw_dst=192.18.115.15/32,action=drop'',
  ''priority=9,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.16.16/32,nw_dst=192.18.116.16/32,action=drop'',
  ''priority=8,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.17.17/32,nw_dst=192.18.117.17/32,action=drop'',
  ''priority=7,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.18.18/32,nw_dst=192.18.118.18/32,action=drop'',
  ''priority=6,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.19.19/32,nw_dst=192.18.119.19/32,action=drop'',
  ''priority=5,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.20.20/32,nw_dst=192.18.120.20/32,action=drop'',
  ''priority=4,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.21.21/32,nw_dst=192.18.121.21/32,action=drop'',
  ''priority=3,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.22.22/32,nw_dst=192.18.122.22/32,action=drop'',
  ''priority=2,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.23.23/32,nw_dst=192.18.123.23/32,action=drop'',
  ''priority=1,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_src=192.18.24.24/32,nw_dst=192.18.124.24/32,action=drop'',
  ''priority=0,hard_timeout=0,idle_timeout=0,dl_type=0x800,action=drop'']" by eval
value[code] "length ofi"

(* TODO: Well, that's something\<dots> I'd really like to have a proper file with newlines though\<dots> *)
(*ML\<open>
	val evterm = the (Code_Evaluation.dynamic_value @{context} @{term "intersperse (Char Nibble0 NibbleA) ofi"});
	val opstr = Syntax.string_of_term (Config.put show_markup false @{context}) evterm;
	File.write (Path.explode (File.platform_path(Resources.master_directory @{theory}) ^ "/pretty_str.txt")) opstr;
\<close>*)

end
