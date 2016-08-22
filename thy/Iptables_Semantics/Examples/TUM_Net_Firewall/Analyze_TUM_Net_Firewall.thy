theory Analyze_TUM_Net_Firewall
imports "../../Primitive_Matchers/Code_Interface"
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: Chair for Network Architectures and Services (TUM) 2013\<close>


parse_iptables_save net_fw_2013="iptables_20.11.2013_cheating"
(*diff -u iptables_20.11.2013 iptables_20.11.2013_cheating
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

lemma "sanity_wf_ruleset net_fw_2013" by eval


(*
value[code] "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
                    in (map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure rules),
                        map (quote_rewrite \<circ> common_primitive_rule_toString) (lower_closure rules))"
*)
lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
                    in (length rules, length (upper_closure rules), length (lower_closure rules))
  = (2375, 2381, 2839)" by eval

value[code] "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
                    in ()"
(*116.392s, compiled ML is less than one second*)


lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
                    in (length (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
                              (upper_closure (packet_assume_new rules))))),
                        length (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
                              (lower_closure (packet_assume_new rules)))))) 
 = (2380, 2836)" by eval

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
     in map simple_rule_ipv4_toString (take 43 (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall
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

lemma "let rules = unfold_ruleset_FORWARD net_fw_2013_FORWARD_default_policy (map_of_string_ipv4 net_fw_2013)
     in map simple_rule_ipv4_toString (take 18 (to_simple_firewall (lower_closure (optimize_matches abstract_for_simple_firewall
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



end
