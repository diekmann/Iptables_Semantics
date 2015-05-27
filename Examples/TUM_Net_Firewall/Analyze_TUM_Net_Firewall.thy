theory Analyze_TUM_Net_Firewall
imports "../Code_Interface"
  "../../Semantics_Ternary/Packet_Set"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

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
text{*on my system, less than 20 seconds.*}
text{*on my system, less than 25 seconds if we also included l4 ports.*}


ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*} (*also true if ports included*)

ML_val{*
length (to_simple_firewall upper);
length (to_simple_firewall lower);
*}


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
                (dump_prot_cisco (proto m)) ^ " " ^
               (dump_ip_cisco (src m))^" "^(dump_ip_cisco (dst m))^
               (if (dump_iface_name "in:" (iiface m))^(dump_iface_name "out:" (oiface m))^(dump_ports "srcports:" (sports m))^
                    (dump_ports "dstports:" (dports m)) <> "TODO: more fields to dump" then "" else "")
               ); dump_cisco rs);
*}

ML_val{*
writeln "interface fe0";
writeln "ip address 10.1.1.1 255.255.255.254";
writeln "ip access-group 101 in";
writeln "!";
dump_cisco (to_simple_firewall upper);
(*access-list 101 deny ip host 10.1.1.2 any
access-list 101 permit tcp any host 192.168.5.10 eq 80
access-list 101 permit tcp any host 192.168.5.11 eq 25
access-list 101 deny any*)
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
*}
ML_val{*
deny_set_set;
*}
(*test with rules*)

end
