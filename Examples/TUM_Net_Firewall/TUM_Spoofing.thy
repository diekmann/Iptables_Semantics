theory TUM_Spoofing
imports "../Code_Interface"
  "../../Primitive_Matchers/No_Spoof"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

(*this is just for testing*)
definition "example_ipassignment_nospoof = 
    no_spoofing_iface (Iface ''eth1.1011'') ([Iface ''eth1.1011'' \<mapsto> [(ipv4addr_of_dotdecimal (131,159,14,0), 24)]]:: ipassignment)"

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
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"


ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(*../../importer/main.py --type ml --module Test  iptables_Lnv_test_iface iptables_Lnv_test_iface.ML*)
(*This is a CHEATING rule set. seee readme cheating.*)
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
text{*on my system, less than 25 seconds (with interfaces).*}


ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*} (*also true if ports included*)

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

ML_val{*
example_ipassignment_nospoof upper;*}

ML_val{*
val t0 = Time.now();
val _ = example_ipassignment_nospoof upper;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*On my system: It took 0.489 seconds
And less than 5gb ram total (loading the firewall ML file still is the most expensive part) *}

end
