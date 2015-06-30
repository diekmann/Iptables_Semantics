theory TUM_Spoofing_new3
imports "../Code_Interface"
  "../Parser"
  "../../Primitive_Matchers/No_Spoof"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

(* My IP ranges. If a packet comes from there from the wrong interface, it is spoofed.
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
definition "everything_but_my_ips = ipv4range_split (ipv4range_invert (l2br (map ipv4cidr_to_interval [
  (ipv4addr_of_dotdecimal (131,159,14,0), 23),
  (ipv4addr_of_dotdecimal (131,159,20,0), 23),
  (ipv4addr_of_dotdecimal (192,168,212,0), 23),
  (ipv4addr_of_dotdecimal (188,95,233,0), 24),
  (ipv4addr_of_dotdecimal (188,95,232,192), 27),
  (ipv4addr_of_dotdecimal (188,95,234,0), 23),
  (ipv4addr_of_dotdecimal (192,48,107,0), 24),
  (ipv4addr_of_dotdecimal (188,95,236,0), 22),
  (ipv4addr_of_dotdecimal (185,86,232,0), 22)
  ])))"


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

lemma "ipassmt_sanity_haswildcards (map_of ipassmt)" by eval


text{*We check for all interfaces, except for @{term "Iface ''eth0''"}, which does not need spoofing protection.*}
definition "interfaces = tl (map (iface_sel \<circ> fst) ipassmt)"

lemma "interfaces = 
  [''eth1.96'', ''eth1.108'', ''eth1.109'', ''eth1.110'',
   ''eth1.116'', ''eth1.152'', ''eth1.171'', ''eth1.173'', ''eth1.1010'',
   ''eth1.1011'', ''eth1.1012'', ''eth1.1014'', ''eth1.1016'', ''eth1.1017'',
   ''eth1.1111'', ''eth1.97'', ''eth1.1019'', ''eth1.1020'', ''eth1.1023'',
   ''eth1.1025'', ''eth1.1024'']" by eval



definition "spoofing_protection fw \<equiv> map (\<lambda>ifce. (ifce, no_spoofing_iface (Iface ifce) (map_of ipassmt) fw)) interfaces"

definition "preprocess default_policy fw \<equiv> (upper_closure (unfold_ruleset_FORWARD default_policy (map_of_string fw)))"




(*test*)
parse_iptables_save net_fw="iptables-save-2015-05-15_15-23-41_cheating"
(* DIFF iptables-save

$ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_15-23-41 iptables-save-2015-05-15_15-23-41_cheating
--- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-save-2015-05-15_15-23-41	2015-05-15 15:24:23.180698000 +0200
+++ iptables-save-2015-05-15_15-23-41_cheating	2015-06-17 14:25:52.485704347 +0200
@@ -141,7 +141,6 @@
 -A INPUT -s 127.0.0.0/8 -j LOG_DROP
 -A INPUT -i eth1.110 -j filter_INPUT
 -A INPUT -i eth1.1024 -j filter_INPUT
--A FORWARD -m state --state RELATED,ESTABLISHED,UNTRACKED -j ACCEPT
 -A FORWARD -i eth1.110 -j NOTFROMHERE
 -A FORWARD -i eth1.1024 -j NOTFROMHERE
 -A FORWARD -m recent --update --seconds 60 --name DEFAULT --rsource -j LOG_RECENT_DROP2
@@ -150,7 +149,6 @@
 -A FORWARD -s 131.159.14.197/32 -i eth1.1011 -j ACCEPT
 -A FORWARD -s 131.159.14.221/32 -i eth1.1011 -j ACCEPT
 -A FORWARD -s 131.159.15.252/32 -i eth1.152 -p udp -j ACCEPT
--A FORWARD -d 131.159.15.252/32 -o eth1.152 -p udp -m multiport --dports 4569,5000:65535 -j ACCEPT
 -A FORWARD -s 131.159.15.247/32 -i eth1.152 -o eth1.110 -j ACCEPT
 -A FORWARD -d 131.159.15.247/32 -i eth1.110 -o eth1.152 -j ACCEPT
 -A FORWARD -s 131.159.15.248/32 -i eth1.152 -o eth1.110 -j ACCEPT
*)
(*DIFF iptables -L -n -v

$ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-Lnv-2015-05-15_15-23-41 iptables-Lnv-2015-05-15_15-23-41_cheating
--- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables-Lnv-2015-05-15_15-23-41	2015-05-15 15:24:23.224698000 +0200
+++ iptables-Lnv-2015-05-15_15-23-41_cheating	2015-05-27 11:08:10.122472029 +0200
@@ -13,7 +13,6 @@
 
 Chain FORWARD (policy ACCEPT 0 packets, 0 bytes)
  pkts bytes target     prot opt in     out     source               destination         
- 278K  265M ACCEPT     all  --  *      *       0.0.0.0/0            0.0.0.0/0            state RELATED,ESTABLISHED,UNTRACKED
  3151  206K NOTFROMHERE  all  --  eth1.110 *       0.0.0.0/0            0.0.0.0/0           
 12501  844K NOTFROMHERE  all  --  eth1.1024 *       0.0.0.0/0            0.0.0.0/0           
     0     0 LOG_RECENT_DROP2  all  --  *      *       0.0.0.0/0            0.0.0.0/0            recent: UPDATE seconds: 60 name: DEFAULT side: source
@@ -22,7 +21,6 @@
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.197       0.0.0.0/0           
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.221       0.0.0.0/0           
     0     0 ACCEPT     udp  --  eth1.152 *       131.159.15.252       0.0.0.0/0           
-    0     0 ACCEPT     udp  --  *      eth1.152  0.0.0.0/0            131.159.15.252       multiport dports 4569,5000:65535
     0     0 ACCEPT     all  --  eth1.152 eth1.110  131.159.15.247       0.0.0.0/0           
     1    40 ACCEPT     all  --  eth1.110 eth1.152  0.0.0.0/0            131.159.15.247      
     0     0 ACCEPT     all  --  eth1.152 eth1.110  131.159.15.248       0.0.0.0/0

*)

(*
The second rule we removed was for an asterisk server. This rule is probably an error because this rule prevents any spoofing protection.
It was a temprary rule and it should have been removed but was forgotten, we are investigating ...
*)

text{*the parsed firewall:*}
value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) net_fw"


(*
(*194.439s*)
value[code] "upper_closure (unfold_ruleset_FORWARD net_fw_FORWARD_default_policy (map_of_string net_fw))"

(*146.691s*)
value[code] "example_ipassignment_nospoof ''eth1.96'' (upper_closure (unfold_ruleset_FORWARD net_fw_FORWARD_default_policy (map_of_string net_fw)))"
*)

text{*sanity check that @{const ipassmt} is complete*}
(*192.886s*)
lemma "ipassmt_sanity_defined (preprocess net_fw_FORWARD_default_policy net_fw) (map_of ipassmt)" by eval


(*204.591s*)
lemma "spoofing_protection (preprocess net_fw_FORWARD_default_policy net_fw) =
 [(''eth1.96'', True),
  (''eth1.108'', True),
  (''eth1.109'', True),
  (''eth1.110'', True), (*INET*)
  (''eth1.116'', True),
  (''eth1.152'', True),
  (''eth1.171'', True),
  (''eth1.173'', True),
  (''eth1.1010'', True),
  (''eth1.1011'', True),
  (''eth1.1012'', True),
  (''eth1.1014'', True),
  (''eth1.1016'', True),
  (''eth1.1017'', True),
  (''eth1.1111'', True),
  (''eth1.97'', False), (*VLAN for internal testing, no spoofing protection*)
  (''eth1.1019'', True),
  (''eth1.1020'', True),
  (''eth1.1023'', True),
  (''eth1.1025'', True),
  (''eth1.1024'', True) (*transfer net*)
 ]" by eval



end
