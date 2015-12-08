theory Analyze_TUM_Net_Firewall
imports "../../Primitive_Matchers/Code_Interface"
  "../../Semantics_Ternary/Packet_Set"
  "../../Simple_Firewall/SimpleFw_toString"
  "../../Primitive_Matchers/Parser"
begin


section{*Example: Chair for Network Architectures and Services (TUM) 2013*}


parse_iptables_save net_fw_2013="iptables_20.11.2013_cheating"
(*diff -u iptables_20.11.2013 iptables_20.11.2013_cheating
--- iptables_20.11.2013	2015-12-04 15:28:33.492307000 +0100
+++ iptables_20.11.2013_cheating	2015-12-08 18:44:36.579896349 +0100
@@ -104,9 +104,6 @@
 -A INPUT -s 127.0.0.0/8 -j LOG_DROP
 -A INPUT -i vlan110 -j NOTFROMHERE
 -A INPUT -i vlan110 -j filter_INPUT
--A FORWARD -m state --state RELATED,ESTABLISHED,UNTRACKED -j ACCEPT
--A FORWARD -m recent --update --seconds 60 --name DEFAULT --rsource -j LOG_RECENT_DROP
--A FORWARD -p tcp -m state --state NEW -m tcp --dport 22 --tcp-flags FIN,SYN,RST,ACK SYN -m recent --update --seconds 360 --hitcount 41 --name ratessh --rsource -j LOG_RECENT_DROP
 -A FORWARD -s 127.0.0.0/8 -j LOG_DROP
 -A FORWARD -s 131.159.14.206/32 -i vlan1011 -p tcp -m multiport --sports 389,636 -j ACCEPT
 -A FORWARD -s 131.159.14.208/32 -i vlan1011 -p tcp -m multiport --sports 389,636 -j ACCEPT*)

lemma "sanity_wf_ruleset net_fw_2013" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013)
                    in (length rules, length (upper_closure rules), length (lower_closure rules)) =
 (2373, 2381, 2838)" by eval

value[code] "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013)
                    in ()"
(*116.392s, compiled ML is less than one second*)

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013)
                    in (length (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                              (upper_closure (packet_assume_new rules))))),
                        length (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
                              (lower_closure (packet_assume_new rules)))))) 
 = (2381, 2836)" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013)
     in map simple_rule_toString (take 43 (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                              (upper_closure (packet_assume_new rules)))))) =
 [''DROP     all  --  127.0.0.0/8            0.0.0.0/0    '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     udp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     udp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     tcp  --  131.159.14.192/27            0.0.0.0/0 in: vlan1011  sports: 3260 '',
  ''ACCEPT     tcp  --  131.159.14.0/23            131.159.14.192/27  out: vlan1011  dports: 3260'',
  ''ACCEPT     tcp  --  131.159.20.0/24            131.159.14.192/27  out: vlan1011  dports: 3260'',
  ''ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0 in: vlan152   '',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 4569'',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 5000:65535'',
  ''ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32 in: vlan110 out: vlan152  '',
  ''ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32 in: vlan110 out: vlan152  '',
  ''DROP     all  --  0.0.0.0/1            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  128.0.0.0/7            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  130.0.0.0/8            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.0.0.0/9            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.128.0.0/12            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.144.0.0/13            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.152.0.0/14            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.156.0.0/15            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.158.0.0/16            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.0.0/21            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.8.0/22            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.12.0/23            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.14.128/25            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.15.0/24            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.16.0/20            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.32.0/19            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.64.0/18            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.128.0/17            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.160.0.0/11            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.192.0.0/10            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  132.0.0.0/6            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  136.0.0.0/5            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  144.0.0.0/4            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  160.0.0.0/3            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  192.0.0.0/2            0.0.0.0/0 in: vlan96   '',
  ''ACCEPT     tcp  --  0.0.0.0/0            131.159.14.36/32  out: vlan96  dports: 22'']" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013)
     in map simple_rule_toString (take 18 (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
                              (lower_closure (packet_assume_new rules)))))) = 
 [''DROP     all  --  127.0.0.0/8            0.0.0.0/0    '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     udp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     udp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     tcp  --  131.159.14.192/27            0.0.0.0/0 in: vlan1011  sports: 3260 '',
  ''ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0 in: vlan152   '',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 4569'',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 5000:65535'',
  ''ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32 in: vlan110 out: vlan152  '',
  ''ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32 in: vlan110 out: vlan152  '',
  ''DROP     all  --  131.159.14.92/32            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.14.65/32            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.14.44/32            0.0.0.0/0 in: vlan96   '']" by eval




parse_iptables_save net_fw_2013_2="iptables_20.11.2013_cheating_2"
(*diff -u iptables_20.11.2013 iptables_20.11.2013_cheating_2
--- iptables_20.11.2013	2015-12-04 15:28:33.492307000 +0100
+++ iptables_20.11.2013_cheating_2	2015-12-08 19:44:06.251743619 +0100
@@ -105,7 +105,6 @@
 -A INPUT -i vlan110 -j NOTFROMHERE
 -A INPUT -i vlan110 -j filter_INPUT
 -A FORWARD -m state --state RELATED,ESTABLISHED,UNTRACKED -j ACCEPT
--A FORWARD -m recent --update --seconds 60 --name DEFAULT --rsource -j LOG_RECENT_DROP
 -A FORWARD -p tcp -m state --state NEW -m tcp --dport 22 --tcp-flags FIN,SYN,RST,ACK SYN -m recent --update --seconds 360 --hitcount 41 --name ratessh --rsource -j LOG_RECENT_DROP
 -A FORWARD -s 127.0.0.0/8 -j LOG_DROP
 -A FORWARD -s 131.159.14.206/32 -i vlan1011 -p tcp -m multiport --sports 389,636 -j ACCEPT*)

lemma "sanity_wf_ruleset net_fw_2013_2" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_2_FORWARD_default_policy (map_of_string net_fw_2013_2)
                    in (length rules, length (upper_closure rules), length (lower_closure rules))
  = (2375, 2382, 2840)" by eval

value[code] "let rules = unfold_ruleset_FORWARD net_fw_2013_2_FORWARD_default_policy (map_of_string net_fw_2013_2)
                    in ()"
(*116.392s, compiled ML is less than one second*)

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_2_FORWARD_default_policy (map_of_string net_fw_2013_2)
                    in (length (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                              (upper_closure (packet_assume_new rules))))),
                        length (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
                              (lower_closure (packet_assume_new rules)))))) = 
 (2381, 2837)" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013_2)
     in map simple_rule_toString (take 43 (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                              (upper_closure (packet_assume_new rules)))))) =
 [''DROP     all  --  127.0.0.0/8            0.0.0.0/0    '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     udp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     udp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     tcp  --  131.159.14.192/27            0.0.0.0/0 in: vlan1011  sports: 3260 '',
  ''ACCEPT     tcp  --  131.159.14.0/23            131.159.14.192/27  out: vlan1011  dports: 3260'',
  ''ACCEPT     tcp  --  131.159.20.0/24            131.159.14.192/27  out: vlan1011  dports: 3260'',
  ''ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0 in: vlan152   '',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 4569'',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 5000:65535'',
  ''ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32 in: vlan110 out: vlan152  '',
  ''ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32 in: vlan110 out: vlan152  '',
  ''DROP     all  --  0.0.0.0/1            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  128.0.0.0/7            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  130.0.0.0/8            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.0.0.0/9            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.128.0.0/12            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.144.0.0/13            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.152.0.0/14            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.156.0.0/15            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.158.0.0/16            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.0.0/21            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.8.0/22            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.12.0/23            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.14.128/25            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.15.0/24            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.16.0/20            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.32.0/19            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.64.0/18            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.128.0/17            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.160.0.0/11            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.192.0.0/10            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  132.0.0.0/6            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  136.0.0.0/5            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  144.0.0.0/4            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  160.0.0.0/3            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  192.0.0.0/2            0.0.0.0/0 in: vlan96   '',
  ''ACCEPT     tcp  --  0.0.0.0/0            131.159.14.36/32  out: vlan96  dports: 22'']" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string net_fw_2013_2)
     in map simple_rule_toString (take 18 (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
                              (lower_closure (packet_assume_new rules)))))) =
 [''DROP     tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 22'',
  ''DROP     all  --  127.0.0.0/8            0.0.0.0/0    '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 389 '',
  ''ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 636 '',
  ''ACCEPT     udp  --  131.159.14.206/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     udp  --  131.159.14.208/32            0.0.0.0/0 in: vlan1011  sports: 88 '',
  ''ACCEPT     tcp  --  131.159.14.192/27            0.0.0.0/0 in: vlan1011  sports: 3260 '',
  ''ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0 in: vlan152   '',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 4569'',
  ''ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32  out: vlan152  dports: 5000:65535'',
  ''ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32 in: vlan110 out: vlan152  '',
  ''ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0 in: vlan152 out: vlan110  '',
  ''ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32 in: vlan110 out: vlan152  '',
  ''DROP     all  --  131.159.14.92/32            0.0.0.0/0 in: vlan96   '',
  ''DROP     all  --  131.159.14.65/32            0.0.0.0/0 in: vlan96   '']" by eval


(*we get better results than from the old dump for iptables_20.11.2013_cheating and iptables_20.11.2013_cheating_2
 reason: the parser understands more
 the results are longer
 we don't need to remove the RELATED,ESTABLISHED rule manually*)



text{*We analyze a dump from 2013. Unfortunately, we don't have an 
      @{text "iptables-save"} dump from that time and have to rely on the @{text "iptables -L -n"}
      dump. This dump was translated by our legacy python importer.*}

(*this is just for testing*)
definition deny_set :: "common_primitive rule list \<Rightarrow> common_primitive packet_set list" where
  "deny_set rs \<equiv> filter (\<lambda>a. a \<noteq> packet_set_UNIV) (map packet_set_opt (allow_set_not_inter rs))"

export_code unfold_ruleset_FORWARD map_of_string upper_closure lower_closure
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtoAny Proto TCP UDP
  Src Dst Prot Extra OIface IIface Src_Ports Dst_Ports
  Iface
  nat_of_integer integer_of_nat integer_to_16word
  dotdecimal_of_ipv4addr
  check_simple_fw_preconditions
  to_simple_firewall
  SimpleRule simple_action.Accept simple_action.Drop 
  iiface oiface src dst proto sports dports
  bitmask_to_strange_inverse_cisco_mask
  deny_set
  ipv4_cidr_toString protocol_toString simple_action_toString port_toString iface_toString ports_toString
  simple_rule_toString
  simple_rule_iptables_save_toString
  sanity_wf_ruleset
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"


ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(* ../../importer/main.py --type ml --module Test iptables_Ln_29.11.2013_cheating iptables_Ln_29.11.2013_cheating.ML *)
ML_file "iptables_Ln_29.11.2013_cheating.ML"



(*This is the diff for the _cheating rule set
 Chain FORWARD (policy ACCEPT)
 target     prot opt source               destination
-ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0            state RELATED,ESTABLISHED,UNTRACKED
-LOG_RECENT_DROP  all  --  0.0.0.0/0            0.0.0.0/0            recent: UPDATE seconds: 60 name: DEFAULT side: source
-LOG_RECENT_DROP  tcp  --  0.0.0.0/0            0.0.0.0/0            state NEW tcp dpt:22flags: 0x17/0x02 recent: UPDATE seconds: 360 hit_count: 41 name: ratessh side: source
 LOG_DROP   all  --  127.0.0.0/8          0.0.0.0/0
 ACCEPT     tcp  --  131.159.14.206       0.0.0.0/0            multiport sports 389,636
 ACCEPT     tcp  --  131.159.14.208       0.0.0.0/0            multiport sports 389,636
*)

ML{*
open Test; 
*}


ML_val{*
  sanity_wf_ruleset firewall_chains
*} (*true*)


declare[[ML_print_depth=50]]
ML{*
val rules = unfold_ruleset_FORWARD Accept (map_of_string firewall_chains)
*}
ML{*
length rules;
val upper = upper_closure rules;
val lower = lower_closure rules;
length upper;
length lower;*}
(*val it = 2401: ?.int
val upper ...
val it = 997: ?.int
val it = 574: ?.int*)


text{*How long does the unfolding take?*}
ML_val{*
val t0 = Time.now();
val _ = unfold_ruleset_FORWARD Accept (map_of_string firewall_chains);
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 1 second.*}



text{*Time required for calculating and normalizing closure*}
ML_val{*
val t0 = Time.now();
val _ = upper_closure rules;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 20 seconds.*}
text{*on my system, less than 25 seconds if we also included l4 ports.*}


ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*} (*true, true; also true if ports included*)

ML_val{*
length (to_simple_firewall upper);
length (to_simple_firewall lower);
*} (*997, 574*)


ML{*
fun dump_dotdecimal_ip (a,(b,(c,d))) = ""^ Int.toString (integer_of_nat a)^"."^ Int.toString (integer_of_nat b)^"."^ Int.toString (integer_of_nat c)^"."^ Int.toString (integer_of_nat d);

fun dump_ip (base, n) = (dump_dotdecimal_ip (dotdecimal_of_ipv4addr base))^"/"^ Int.toString (integer_of_nat n);

fun dump_prot ProtoAny = "all"
  | dump_prot (Proto TCP) = "tcp"
  | dump_prot (Proto UDP) = "udp";

fun dump_action (Accepta : simple_action) = "ACCEPT"
  | dump_action (Dropa   : simple_action) = "DROP";

fun dump_iface_name (descr: string) (Iface name) = (let val iface=String.implode name in (if iface = "" orelse iface = "+" then "" else descr^" "^iface) end)

(*fun dump_port p = Int.toString (integer_of_nat (port_to_nat p))*)

fun dump_ports descr (s,e) = (let val ports = "("^String.implode (port_toString s)^","^String.implode (port_toString e)^")" in (if ports = "(0,65535)" then "" else descr^" "^ports) end)

*}

ML{*
val putLn = writeln o String.implode o simple_rule_toString
*}

text{*iptables -L -n*}
ML_val{*
writeln "Chain INPUT (policy ACCEPT)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy ACCEPT)";
writeln "target     prot opt source               destination";
val _ = map putLn (to_simple_firewall upper);
writeln "Chain OUTPUT (policy ACCEPT)";
writeln "target     prot opt source               destination"
*}
(*
Chain FORWARD (policy ACCEPT) 
target     prot opt source               destination 
DROP     all  --  127.0.0.0/8            0.0.0.0/0     
ACCEPT     tcp  --  131.159.14.206/32            0.0.0.0/0     
ACCEPT     tcp  --  131.159.14.208/32            0.0.0.0/0     
ACCEPT     udp  --  131.159.14.206/32            0.0.0.0/0     
ACCEPT     udp  --  131.159.14.208/32            0.0.0.0/0     
ACCEPT     tcp  --  131.159.14.192/27            0.0.0.0/0     
ACCEPT     tcp  --  131.159.14.0/23            131.159.14.192/27     
ACCEPT     tcp  --  131.159.20.0/24            131.159.14.192/27     
ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0     
ACCEPT     udp  --  0.0.0.0/0            131.159.15.252/32     
ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0     
ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32     
ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0     
ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32     
DROP     all  --  0.0.0.0/1            0.0.0.0/0     
DROP     all  --  128.0.0.0/7            0.0.0.0/0     
DROP     all  --  130.0.0.0/8            0.0.0.0/0     
DROP     all  --  131.0.0.0/9            0.0.0.0/0     
DROP     all  --  131.128.0.0/12            0.0.0.0/0     
DROP     all  --  131.144.0.0/13            0.0.0.0/0     
DROP     all  --  131.152.0.0/14            0.0.0.0/0     
DROP     all  --  131.156.0.0/15            0.0.0.0/0     
DROP     all  --  131.158.0.0/16            0.0.0.0/0     
DROP     all  --  131.159.0.0/21            0.0.0.0/0     
DROP     all  --  131.159.8.0/22            0.0.0.0/0     
DROP     all  --  131.159.12.0/23            0.0.0.0/0     
DROP     all  --  131.159.14.128/25            0.0.0.0/0     
DROP     all  --  131.159.15.0/24            0.0.0.0/0     
DROP     all  --  131.159.16.0/20            0.0.0.0/0     
DROP     all  --  131.159.32.0/19            0.0.0.0/0     
DROP     all  --  131.159.64.0/18            0.0.0.0/0     
DROP     all  --  131.159.128.0/17            0.0.0.0/0     
DROP     all  --  131.160.0.0/11            0.0.0.0/0     
DROP     all  --  131.192.0.0/10            0.0.0.0/0     
DROP     all  --  132.0.0.0/6            0.0.0.0/0     
DROP     all  --  136.0.0.0/5            0.0.0.0/0     
DROP     all  --  144.0.0.0/4            0.0.0.0/0     
DROP     all  --  160.0.0.0/3            0.0.0.0/0     
DROP     all  --  192.0.0.0/2            0.0.0.0/0     
ACCEPT     tcp  --  0.0.0.0/0            131.159.14.36/32     
ACCEPT     tcp  --  0.0.0.0/0            131.159.14.9/32     
ACCEPT     tcp  --  0.0.0.0/0            131.159.14.91/32     
ACCEPT     tcp  --  0.0.0.0/0            131.159.14.24/32     
ACCEPT     tcp  --  131.159.15.224/28            131.159.14.47/32 
...*)


text{*iptables -L -n*}
ML_val{*
writeln "Chain INPUT (policy ACCEPT)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy ACCEPT)";
writeln "target     prot opt source               destination";
val _ = map putLn (to_simple_firewall lower);
writeln "Chain OUTPUT (policy ACCEPT)";
writeln "target     prot opt source               destination"
*}
(*Chain FORWARD (policy ACCEPT) 
target     prot opt source               destination 
DROP     all  --  127.0.0.0/8            0.0.0.0/0     
ACCEPT     udp  --  131.159.15.252/32            0.0.0.0/0     
ACCEPT     all  --  131.159.15.247/32            0.0.0.0/0     
ACCEPT     all  --  0.0.0.0/0            131.159.15.247/32     
ACCEPT     all  --  131.159.15.248/32            0.0.0.0/0     
ACCEPT     all  --  0.0.0.0/0            131.159.15.248/32     
DROP     all  --  131.159.14.92/32            0.0.0.0/0     
DROP     all  --  131.159.14.65/32            0.0.0.0/0     
DROP     all  --  131.159.14.44/32            0.0.0.0/0     
DROP     all  --  131.159.14.36/32            0.0.0.0/0     
DROP     all  --  131.159.14.119/32            0.0.0.0/0     
DROP     all  --  131.159.14.18/32            0.0.0.0/0     
DROP     all  --  131.159.14.54/32            0.0.0.0/0     
DROP     all  --  131.159.14.9/32            0.0.0.0/0     
DROP     all  --  131.159.14.85/32            0.0.0.0/0     
DROP     all  --  131.159.14.118/32            0.0.0.0/0     
DROP     all  --  131.159.14.17/32            0.0.0.0/0     
DROP     all  --  131.159.14.45/32            0.0.0.0/0     
DROP     all  --  131.159.14.91/32            0.0.0.0/0     
DROP     all  --  131.159.14.71/32            0.0.0.0/0     
DROP     all  --  131.159.14.34/32            0.0.0.0/0     
DROP     all  --  131.159.14.83/32            0.0.0.0/0     
DROP     all  --  131.159.14.82/32            0.0.0.0/0     
DROP     all  --  131.159.14.60/32            0.0.0.0/0     
DROP     all  --  131.159.14.24/32            0.0.0.0/0     
DROP     all  --  131.159.14.47/32            0.0.0.0/0     
DROP     all  --  131.159.14.33/32            0.0.0.0/0     
DROP     all  --  131.159.14.15/32            0.0.0.0/0     
DROP     all  --  131.159.14.74/32            0.0.0.0/0     
DROP     all  --  131.159.14.123/32            0.0.0.0/0     
DROP     all  --  131.159.14.73/32            0.0.0.0/0     
DROP     all  --  131.159.14.64/32            0.0.0.0/0     
DROP     all  --  131.159.14.20/32            0.0.0.0/0     
DROP     all  --  131.159.14.79/32            0.0.0.0/0     
DROP     all  --  131.159.14.51/32            0.0.0.0/0     
DROP     all  --  131.159.14.7/32            0.0.0.0/0     
DROP     all  --  131.159.14.48/32            0.0.0.0/0     
DROP     all  --  131.159.14.120/32            0.0.0.0/0     
DROP     all  --  131.159.14.121/32            0.0.0.0/0     
DROP     all  --  131.159.14.27/32            0.0.0.0/0     
DROP     all  --  131.159.14.105/32            0.0.0.0/0     
DROP     all  --  131.159.14.106/32            0.0.0.0/0     
DROP     all  --  131.159.14.103/32            0.0.0.0/0     
DROP     all  --  131.159.14.101/32            0.0.0.0/0     
DROP     all  --  131.159.14.102/32            0.0.0.0/0     
DROP     all  --  131.159.14.100/32            0.0.0.0/0     
DROP     all  --  131.159.14.95/32            0.0.0.0/0     
DROP     all  --  131.159.14.107/32            0.0.0.0/0     
DROP     all  --  131.159.14.108/32            0.0.0.0/0     
DROP     all  --  131.159.14.77/32            0.0.0.0/0     
DROP     all  --  131.159.14.52/32            0.0.0.0/0     
DROP     all  --  131.159.14.66/32            0.0.0.0/0     
DROP     all  --  131.159.14.90/32            0.0.0.0/0     
DROP     all  --  131.159.14.111/32            0.0.0.0/0     
DROP     all  --  131.159.14.96/32            0.0.0.0/0     
DROP     all  --  131.159.14.43/32            0.0.0.0/0     
DROP     all  --  131.159.14.109/32            0.0.0.0/0     
DROP     all  --  131.159.14.112/32            0.0.0.0/0     
DROP     all  --  131.159.14.113/32            0.0.0.0/0     
DROP     all  --  131.159.14.114/32            0.0.0.0/0     
DROP     all  --  131.159.14.115/32            0.0.0.0/0     
DROP     all  --  131.159.14.116/32            0.0.0.0/0     
DROP     all  --  131.159.14.117/32            0.0.0.0/0     
DROP     all  --  131.159.14.93/32            0.0.0.0/0     
DROP     all  --  131.159.14.99/32            0.0.0.0/0     
DROP     all  --  131.159.14.122/32            0.0.0.0/0     
DROP     all  --  131.159.14.28/32            0.0.0.0/0     
DROP     all  --  131.159.14.94/32            0.0.0.0/0     
DROP     all  --  131.159.14.75/32            0.0.0.0/0     
DROP     all  --  131.159.14.63/32            0.0.0.0/0     
DROP     all  --  131.159.14.89/32            0.0.0.0/0     
DROP     all  --  131.159.14.37/32            0.0.0.0/0     
DROP     all  --  131.159.14.81/32            0.0.0.0/0     
DROP     all  --  131.159.14.12/32            0.0.0.0/0     
DROP     all  --  131.159.14.58/32            0.0.0.0/0     
DROP     all  --  131.159.14.6/32            0.0.0.0/0     
DROP     all  --  131.159.14.78/32            0.0.0.0/0     
DROP     all  --  131.159.14.8/32            0.0.0.0/0     
DROP     all  --  131.159.14.98/32            0.0.0.0/0     
DROP     all  --  131.159.14.19/32            0.0.0.0/0     
DROP     all  --  131.159.14.10/32            0.0.0.0/0     
DROP     all  --  131.159.14.23/32            0.0.0.0/0     
DROP     all  --  131.159.14.57/32            0.0.0.0/0     
DROP     all  --  131.159.14.86/32            0.0.0.0/0     
DROP     all  --  131.159.14.11/32            0.0.0.0/0     
DROP     all  --  131.159.14.55/32            0.0.0.0/0     
DROP     all  --  131.159.14.46/32            0.0.0.0/0     
DROP     all  --  131.159.14.50/32            0.0.0.0/0     
DROP     all  --  131.159.14.70/32            0.0.0.0/0     
DROP     all  --  131.159.14.5/32            0.0.0.0/0     
DROP     all  --  131.159.14.53/32            0.0.0.0/0     
DROP     all  --  131.159.14.88/32            0.0.0.0/0     
DROP     all  --  131.159.14.14/32            0.0.0.0/0     
DROP     all  --  131.159.14.13/32            0.0.0.0/0     
DROP     all  --  131.159.14.84/32            0.0.0.0/0     
DROP     all  --  131.159.14.68/32            0.0.0.0/0     
DROP     all  --  131.159.14.42/32            0.0.0.0/0     
DROP     all  --  131.159.14.16/32            0.0.0.0/0     
DROP     all  --  131.159.14.30/32            0.0.0.0/0     
DROP     all  --  131.159.14.22/32            0.0.0.0/0     
DROP     all  --  131.159.14.87/32            0.0.0.0/0     
DROP     all  --  131.159.14.97/32            0.0.0.0/0     
DROP     all  --  131.159.14.29/32            0.0.0.0/0     
DROP     all  --  131.159.14.72/32            0.0.0.0/0     
DROP     all  --  131.159.14.21/32            0.0.0.0/0     
DROP     all  --  131.159.14.125/32            0.0.0.0/0     
DROP     all  --  131.159.14.67/32            0.0.0.0/0     
DROP     all  --  131.159.14.76/32            0.0.0.0/0     
DROP     all  --  0.0.0.0/1            0.0.0.0/0     
DROP     all  --  128.0.0.0/7            0.0.0.0/0     
DROP     all  --  130.0.0.0/8            0.0.0.0/0     
DROP     all  --  131.0.0.0/9            0.0.0.0/0     
DROP     all  --  131.128.0.0/12            0.0.0.0/0     
DROP     all  --  131.144.0.0/13            0.0.0.0/0     
DROP     all  --  131.152.0.0/14            0.0.0.0/0     
DROP     all  --  131.156.0.0/15            0.0.0.0/0     
DROP     all  --  131.158.0.0/16            0.0.0.0/0     
DROP     all  --  131.159.0.0/21            0.0.0.0/0     
DROP     all  --  131.159.8.0/22            0.0.0.0/0     
DROP     all  --  131.159.12.0/23            0.0.0.0/0     
DROP     all  --  131.159.14.128/25            0.0.0.0/0     
DROP     all  --  131.159.15.0/24            0.0.0.0/0     
DROP     all  --  131.159.16.0/20            0.0.0.0/0     
DROP     all  --  131.159.32.0/19            0.0.0.0/0     
DROP     all  --  131.159.64.0/18            0.0.0.0/0     
DROP     all  --  131.159.128.0/17            0.0.0.0/0     
DROP     all  --  131.160.0.0/11            0.0.0.0/0     
DROP     all  --  131.192.0.0/10            0.0.0.0/0     
DROP     all  --  132.0.0.0/6            0.0.0.0/0     
DROP     all  --  136.0.0.0/5            0.0.0.0/0     
DROP     all  --  144.0.0.0/4            0.0.0.0/0     
DROP     all  --  160.0.0.0/3            0.0.0.0/0     
DROP     all  --  192.0.0.0/2            0.0.0.0/0     
DROP     all  --  0.0.0.0/0            131.159.14.0/25     
DROP     all  --  0.0.0.0/0            224.0.0.0/4     
DROP     all  --  131.159.14.186/32            0.0.0.0/0     
DROP     all  --  131.159.14.153/32            0.0.0.0/0     
DROP     all  --  131.159.14.187/32            0.0.0.0/0     
DROP     all  --  131.159.14.158/32            0.0.0.0/0     
DROP     all  --  131.159.14.155/32            0.0.0.0/0     
DROP     all  --  131.159.14.169/32            0.0.0.0/0     
DROP     all  --  131.159.14.150/32            0.0.0.0/0     
DROP     all  --  131.159.14.163/32            0.0.0.0/0     
DROP     all  --  131.159.14.166/32            0.0.0.0/0     
DROP     all  --  131.159.14.170/32            0.0.0.0/0     
DROP     all  --  131.159.14.171/32            0.0.0.0/0     
DROP     all  --  131.159.14.176/32            0.0.0.0/0     
DROP     all  --  131.159.14.144/32            0.0.0.0/0     
DROP     all  --  131.159.14.181/32            0.0.0.0/0     
DROP     all  --  131.159.14.167/32            0.0.0.0/0     
DROP     all  --  131.159.14.175/32            0.0.0.0/0     
DROP     all  --  131.159.14.139/32            0.0.0.0/0     
DROP     all  --  131.159.14.178/32            0.0.0.0/0     
DROP     all  --  131.159.14.174/32            0.0.0.0/0     
DROP     all  --  131.159.14.157/32            0.0.0.0/0     
DROP     all  --  131.159.14.130/32            0.0.0.0/0     
DROP     all  --  131.159.14.149/32            0.0.0.0/0     
DROP     all  --  131.159.14.180/32            0.0.0.0/0     
DROP     all  --  131.159.14.148/32            0.0.0.0/0     
DROP     all  --  131.159.14.132/32            0.0.0.0/0     
DROP     all  --  131.159.14.137/32            0.0.0.0/0     
DROP     all  --  131.159.14.138/32            0.0.0.0/0     
DROP     all  --  131.159.14.164/32            0.0.0.0/0     
DROP     all  --  131.159.14.136/32            0.0.0.0/0     
DROP     all  --  131.159.14.140/32            0.0.0.0/0     
DROP     all  --  131.159.14.146/32            0.0.0.0/0     
DROP     all  --  131.159.14.165/32            0.0.0.0/0     
DROP     all  --  131.159.14.145/32            0.0.0.0/0     
DROP     all  --  131.159.14.156/32            0.0.0.0/0     
DROP     all  --  131.159.14.184/32            0.0.0.0/0     
DROP     all  --  131.159.14.168/32            0.0.0.0/0     
DROP     all  --  131.159.14.0/25            0.0.0.0/0     
DROP     all  --  131.159.14.192/26            0.0.0.0/0     
DROP     all  --  0.0.0.0/0            131.159.14.128/26     
DROP     all  --  131.159.20.126/32            0.0.0.0/0     
DROP     all  --  131.159.20.109/32            0.0.0.0/0     
DROP     all  --  131.159.20.180/32            0.0.0.0/0     
DROP     all  --  131.159.20.52/32            0.0.0.0/0     
DROP     all  --  131.159.20.146/32            0.0.0.0/0     
DROP     all  --  131.159.20.89/32            0.0.0.0/0     
DROP     all  --  131.159.20.142/32            0.0.0.0/0     
DROP     all  --  131.159.20.121/32            0.0.0.0/0     
DROP     all  --  131.159.20.5/32            0.0.0.0/0     
DROP     all  --  131.159.20.252/32            0.0.0.0/0     
DROP     all  --  131.159.20.62/32            0.0.0.0/0     
DROP     all  --  131.159.20.85/32            0.0.0.0/0     
DROP     all  --  131.159.20.172/32            0.0.0.0/0     
DROP     all  --  131.159.20.71/32            0.0.0.0/0     
DROP     all  --  131.159.20.79/32            0.0.0.0/0     
DROP     all  --  131.159.20.12/32            0.0.0.0/0     
DROP     all  --  131.159.20.37/32            0.0.0.0/0     
DROP     all  --  131.159.20.103/32            0.0.0.0/0     
DROP     all  --  131.159.20.150/32            0.0.0.0/0     
DROP     all  --  131.159.20.92/32            0.0.0.0/0     
DROP     all  --  131.159.20.128/32            0.0.0.0/0     
DROP     all  --  131.159.20.100/32            0.0.0.0/0     
DROP     all  --  131.159.20.131/32            0.0.0.0/0     
DROP     all  --  131.159.20.167/32            0.0.0.0/0     
DROP     all  --  131.159.20.133/32            0.0.0.0/0     
DROP     all  --  131.159.20.21/32            0.0.0.0/0     
DROP     all  --  131.159.20.183/32            0.0.0.0/0     
DROP     all  --  131.159.20.99/32            0.0.0.0/0     
DROP     all  --  131.159.20.132/32            0.0.0.0/0     
DROP     all  --  131.159.20.163/32            0.0.0.0/0     
DROP     all  --  131.159.20.94/32            0.0.0.0/0     
DROP     all  --  131.159.20.82/32            0.0.0.0/0     
DROP     all  --  131.159.20.145/32            0.0.0.0/0     
DROP     all  --  131.159.20.111/32            0.0.0.0/0     
DROP     all  --  131.159.20.53/32            0.0.0.0/0     
DROP     all  --  131.159.20.115/32            0.0.0.0/0     
DROP     all  --  131.159.20.161/32            0.0.0.0/0     
DROP     all  --  131.159.20.156/32            0.0.0.0/0     
DROP     all  --  131.159.20.122/32            0.0.0.0/0     
DROP     all  --  131.159.20.130/32            0.0.0.0/0     
DROP     all  --  131.159.20.91/32            0.0.0.0/0     
DROP     all  --  131.159.20.178/32            0.0.0.0/0     
DROP     all  --  131.159.20.237/32            0.0.0.0/0     
DROP     all  --  131.159.20.168/32            0.0.0.0/0    
...*)

subsection{*Different output formats*}

text{*iptables-save*}
ML_val{* 
local
  val date = Date.toString (Date.fromTimeLocal (Time.now ()));
  val export_file = Context.theory_name @{theory} ^ ".thy";
  val header ="# Generated by " ^ Distribution.version ^ " on " ^ date ^ " src: " ^ export_file;
in
  val _ = writeln header;
end;
writeln "*filter";
writeln ":INPUT ACCEPT [0:0]";
writeln ":FORWARD ACCEPT [0:0]";
writeln ":OUTPUT ACCEPT [0:0]";
val _ = map (fn r => writeln (String.implode (simple_rule_iptables_save_toString (String.explode "FORWARD") r))) (to_simple_firewall upper);
writeln "COMMIT";
writeln "# make sure no space is after COMMIT";
writeln "# Completed on Wed Sep  3 18:02:01 2014";
*}



text{*Cisco*}
text{*The following can be loaded by Margrave. It seems that Margrave does not support the `range' command for ports
      but if the protocol is TCP or UDP, it expects the `eq' keyword.
      Therefore, we set everything to ip*}
ML{*
fun dump_action_cisco Accepta = "permit"
  | dump_action_cisco Dropa = "deny"
;


fun dump_prot_cisco ProtoAny = "ip"
  | dump_prot_cisco (Proto TCP) = "tcp"
  | dump_prot_cisco (Proto UDP) = "udp";


local
  fun dump_ip_cisco_helper (ip, nm) = (dump_dotdecimal_ip (dotdecimal_of_ipv4addr ip))^" "^(dump_dotdecimal_ip (bitmask_to_strange_inverse_cisco_mask nm));
    (*dump_ip_cisco_helper (ip, (nat_of_integer 32)) = "host "^(dump_dotdecimal_ip ip)*)
in
  fun dump_ip_cisco ip = dump_ip_cisco_helper ip
end; (*TODO: add any for UNIV range*)


fun dump_cisco [] = ()
  | dump_cisco (SimpleRule (m, a) :: rs) =
      (writeln ("access-list 101 " ^ dump_action_cisco a ^ " " ^
                (*dump_prot_cisco (proto m)*)"ip" ^ " " ^ (*hack hack*)
               (dump_ip_cisco (src m))^" "^(dump_ip_cisco (dst m))^
               (if (dump_iface_name "in:" (iiface m))^(dump_iface_name "out:" (oiface m))^(dump_ports "srcports:" (sports m))^
                    (dump_ports "dstports:" (dports m)) <> "TODO: more fields to dump" then "" else "")
               (*^ if (proto m) = (Proto TCP) orelse (proto m) = (Proto UDP) then " range 0 65535" else "") (*hack hack*)*)
               ); dump_cisco rs);
*}

ML_val{*
writeln "interface fe0";
writeln "ip address 10.1.1.1 255.255.255.254";
writeln "ip access-group 101 in";
writeln "!";
dump_cisco (to_simple_firewall upper);
writeln "!";
writeln "! // need to give the end command";
writeln "end";
*}



text{*OpenVSwitch flow table entries *}
ML{*

fun dump_action_flowtable Accepta = "flood"
  | dump_action_flowtable Dropa = "drop"
;


fun dump_ip_flowtable (ip, nm) = (dump_dotdecimal_ip (dotdecimal_of_ipv4addr ip))^"/"^ Int.toString (integer_of_nat nm);


fun dump_flowtable [] = ()
  | dump_flowtable (SimpleRule (m, a) :: rs) =
      (writeln (dump_prot_cisco (proto m) ^ " " ^
                "nw_src="^(dump_ip_flowtable (src m))^" nw_dst="^(dump_ip_flowtable (dst m)) ^
                " priority="^Int.toString (List.length rs)^
                " action="^dump_action_flowtable a ^
                (if (dump_iface_name "in:" (iiface m))^(dump_iface_name "out:" (oiface m))^(dump_ports "srcports:" (sports m))^
                    (dump_ports "dstports:" (dports m)) <> "TODO: more fields to dump" then "" else "")
                ); dump_flowtable rs);
*}
ML_val{*
dump_flowtable (to_simple_firewall upper);
*}


text{*packet set (test)*}
ML{*
val t0 = Time.now();
val deny_set_set = deny_set upper;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}

(*
less than 3 seconds on my system.
It was a problem when packet_set_opt2_internal recursive
*)

ML_val{*
length deny_set_set;
*} (*330*)
ML_val{*
deny_set_set;
*}
(*test with rules*)

end
