theory TUM_Spoofing_new
imports "../Code_Interface"
  "../../Primitive_Matchers/No_Spoof"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

definition "ipassmt = [(Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,213,4), 24)]),
(Iface ''eth1.96'', [(ipv4addr_of_dotdecimal (131,159,14,3), 25)]),
(Iface ''eth1.108'', [(ipv4addr_of_dotdecimal (131,159,14,129), 26)]),
(Iface ''eth1.109'', [(ipv4addr_of_dotdecimal (131,159,20,11), 24)]),
(Iface ''eth1.110'', [(ipv4addr_of_dotdecimal (131,159,252,150), 30)]),
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
(Iface ''eth1.1024'', [(ipv4addr_of_dotdecimal (188,95,232,61), 29)])]"
(*TODO: not in this list: inet iface*)

lemma "ipassmt_sanity_haswildcards (map_of ipassmt)" by eval


definition "example_ipassignment_nospoof ifce = 
    no_spoofing_iface (Iface ifce) (map_of ipassmt:: ipassignment)"


definition "example_ipassmt_sanity_defined rs = ipassmt_sanity_defined rs (map_of ipassmt)"


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
  ipv4_cidr_toString protocol_toString simple_action_toString port_toString iface_toString ports_toString
  simple_rule_toString
  simple_rule_iptables_save_toString

  ifaceAny no_spoofing_iface example_ipassignment_nospoof
  map_of ipassmt example_ipassmt_sanity_defined
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"


ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(*../../importer/main.py --type ml --module Test  iptables_Lnv_test_iface iptables_Lnv_test_iface.ML*)


ML_file "iptables-Lnv-2015-05-13_10-53-20_cheating.ML"

(*
$ diff -u ~/git/net-network/iptables-Lnv-2015-05-13_10-53-20 iptables-Lnv-2015-05-13_10-53-20_cheating
--- /home/diekmann/git/net-network/iptables-Lnv-2015-05-13_10-53-20	2015-05-13 11:19:16.669193827 +0200
+++ iptables-Lnv-2015-05-13_10-53-20_cheating	2015-05-13 13:11:18.463582107 +0200
@@ -13,14 +13,12 @@
 
 Chain FORWARD (policy ACCEPT 0 packets, 0 bytes)
  pkts bytes target     prot opt in     out     source               destination         
-2633M 3879G ACCEPT     all  --  *      *       0.0.0.0/0            0.0.0.0/0            state RELATED,ESTABLISHED,UNTRACKED
     0     0 LOG_RECENT_DROP2  all  --  *      *       0.0.0.0/0            0.0.0.0/0            recent: UPDATE seconds: 60 name: DEFAULT side: source
  563K   26M LOG_RECENT_DROP  tcp  --  *      *       0.0.0.0/0            0.0.0.0/0            state NEW tcp dpt:22flags: 0x17/0x02 recent: UPDATE seconds: 360 hit_count: 41 name: ratessh side: source
     0     0 LOG_DROP   all  --  *      *       127.0.0.0/8          0.0.0.0/0           
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.197       0.0.0.0/0           
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.221       0.0.0.0/0           
     0     0 ACCEPT     udp  --  eth1.152 *       131.159.15.252       0.0.0.0/0           
-    0     0 ACCEPT     udp  --  *      eth1.152  0.0.0.0/0            131.159.15.252       multiport dports 4569,5000:65535
   209  9376 ACCEPT     all  --  eth1.152 eth1.110  131.159.15.247       0.0.0.0/0           
 11332  694K ACCEPT     all  --  eth1.110 eth1.152  0.0.0.0/0            131.159.15.247      
   173  6948 ACCEPT     all  --  eth1.152 eth1.110  131.159.15.248       0.0.0.0/0           
*)


(*
The second rule we removed was for an asterisk server. This rule is probably an error because this rule prevents any spoofing protection!
It was a temprary rule and it should have been removed but was forgotten, we are investigating ...
*)

ML{*
open Test; 
*}

declare[[ML_print_depth=50]]
ML{*
val rules = unfold_ruleset_FORWARD Accept (map_of_string firewall_chains)
*}
ML{*
length rules;
val upper = upper_closure rules;
length upper;*}

text{*How long does the unfolding take?*}
ML_val{*
val t0 = Time.now();
val _ = unfold_ruleset_FORWARD Accept (map_of_string firewall_chains);
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 1 second.*}


ML_val{*
check_simple_fw_preconditions upper;
*} (*true*)

ML_val{*
example_ipassmt_sanity_defined upper;
*} (*true*)

ML_val{*
length (to_simple_firewall upper);
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


ML_val{*
example_ipassignment_nospoof (String.explode "eth1.96") upper;
*} (*success*)


ML_val{*
example_ipassignment_nospoof (String.explode "eth1.108") upper;
*} (*fail. reason: filter_96 allows spoofed packets*)

text{*vlan 96 is protected, all other following are not!*}
(* rp filter still blocks most spoofing attempts. most! when we disable it, we can spoof (tested) *)
(* our firewall also has a MAC address filter, constructed analogously to the ip spoofing filter.
   the MAC address filter had the same problems, rp_filter could not prevent them. *)
(* rp filter for some cases not applicable*)
(* example where rp_filter will fail: 10./8 
  admin: will iber reverse path explizit als sich auf rp_filter zu verlassen. real life: router mit firewall der kein rp_filter aus haben kann
  (address range ueber mehrer interfaces)*)
(*an example where we need to disbale rp_filter:
  https://www.tolaris.com/2009/07/13/disabling-reverse-path-filtering-in-complex-networks/
  ``However, you can safely disable it [rp_filter] if you perform the same sanity checks in your iptables firewall (and you do, right?).''*)
(*
``Some setups, notably with asymmetric routing, may not be eligible to use RPF however.'' http://inai.de/documents/Perfect_Ruleset.pdf
or failover, or other stuff, ...
*)

end
