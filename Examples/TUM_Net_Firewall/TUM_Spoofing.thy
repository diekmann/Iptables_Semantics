theory TUM_Spoofing
imports "../Code_Interface"
  "../../Primitive_Matchers/No_Spoof"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

(*this is just for testing*)
definition "example_ipassignment_nospoof = 
    no_spoofing_iface (Iface ''eth1.1017'') ([Iface ''eth1.1017'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,240), 28)]]:: ipassignment)"



text{*
This will be a counter example that the spoofing protection fails.
The IPv4 src clearly is not for the range of the interface!
*}
definition "counter_example rs =
  approximating_bigstep_fun (common_matcher, in_doubt_allow)
    \<lparr>p_iiface = ''eth1.1017'', p_oiface = ''eth1.96'',
     p_src = 0, p_dst = ipv4addr_of_dotdecimal (131,159,14,9),
     p_proto = TCP, p_sport = 12345, p_dport = 22\<rparr> rs Undecided
    "

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
  counter_example
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"


ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(*../../importer/main.py --type ml --module Test  iptables_Lnv_test_iface iptables_Lnv_test_iface.ML*)
(*This is a CHEATING rule set. seee readme cheating.*)
(*
$ diff -u ~/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables_Lnv_25.07.2014 iptables_Lnv_test_iface
--- /home/diekmann/git/net-network/configs_chair_for_Network_Architectures_and_Services/iptables_Lnv_25.07.2014	2014-09-09 14:44:29.782417000 +0200
+++ iptables_Lnv_test_iface	2015-05-05 18:12:08.464302371 +0200
@@ -11,9 +11,6 @@
 
 Chain FORWARD (policy ACCEPT 0 packets, 0 bytes)
  pkts bytes target     prot opt in     out     source               destination
-1560M  352G ACCEPT     all  --  *      *       0.0.0.0/0            0.0.0.0/0            state RELATED,ESTABLISHED,UNTRACKED
-    0     0 LOG_RECENT_DROP2  all  --  *      *       0.0.0.0/0            0.0.0.0/0            recent: UPDATE seconds: 60 name: DEFAULT side: source
-80610 3815K LOG_RECENT_DROP  tcp  --  *      *       0.0.0.0/0            0.0.0.0/0            state NEW tcp dpt:22flags: 0x17/0x02 recent: UPDATE seconds: 360 hit_count: 41 name: ratessh side: source
     0     0 LOG_DROP   all  --  *      *       127.0.0.0/8          0.0.0.0/0
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.197       0.0.0.0/0
     0     0 ACCEPT     all  --  eth1.1011 *       131.159.14.221       0.0.0.0/0
*)
ML_file "iptables_Lnv_test_iface.ML"

ML{*
open Test; 
*}

declare[[ML_print_depth=50]]
ML{*
val rules = unfold_ruleset_FORWARD (map_of_string firewall_chains)
*}
ML{*
length rules;
val upper = upper_closure rules;
val lower = lower_closure rules;
length upper;
length lower;*}

text{*How long does the unfolding take?*}
ML_val{*
val t0 = Time.now();
val _ = unfold_ruleset_FORWARD (map_of_string firewall_chains);
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
text{*on my system, less than 30 seconds (with interfaces).*}


ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*}

ML_val{*
length (to_simple_firewall upper);
length (to_simple_firewall lower);
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
example_ipassignment_nospoof upper;
*}

ML_val{*
val t0 = Time.now();
val _ = example_ipassignment_nospoof upper;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*On my system: It took 0.489 seconds
And less than 5gb ram total (loading the firewall ML file still is the most expensive part) *}


text{*
The spoofing protection check fails.
Here is the counter example.
@{term "Decision FinalAllow"}
*}
ML_val{*
counter_example upper;
*}

end
