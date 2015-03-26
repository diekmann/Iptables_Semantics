theory Analyze_SQRL_Shorewall
imports "../Code_Interface"
"../../Semantics_Ternary/Optimizing"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
begin


section{*Example: SQRL Shorewall*}

export_code unfold_ruleset_OUTPUT map_of_string upper_closure lower_closure
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtoAny Proto TCP UDP
  Src Dst Prot Extra OIface IIface Src_Ports Dst_Ports
  Iface
  nat_of_integer integer_of_nat
  port_to_nat
  dotdecimal_of_ipv4addr
  check_simple_fw_preconditions
  to_simple_firewall
  SimpleRule simple_action.Accept simple_action.Drop 
  iiface oiface src dst proto sports dports
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"

ML{*
open Test; (*put the exported code into current namespace such that the following firewall definition loads*)
*}

(*./main.py -t ml --module=Test  ../Examples/SQRL_Shorewall/akachan-iptables-Ln ../Examples/SQRL_Shorewall/akachan-iptables-Ln.ML
*)
ML_file "akachan-iptables-Ln.ML"

ML{*
open Test;
*}
declare[[ML_print_depth=50]]



ML{*
val rules = unfold_ruleset_OUTPUT (map_of_string firewall_chains)
*}
ML{*
length rules;
val upper = upper_closure rules;
val lower = lower_closure rules;
length upper;
length lower;*}


ML_val{*
check_simple_fw_preconditions upper;
check_simple_fw_preconditions lower;
*}

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

fun dump_port p = Int.toString (integer_of_nat (port_to_nat p))

fun dump_ports descr (s,e) = (let val ports = "("^dump_port s^","^dump_port e^")" in (if ports = "(0,65535)" then "" else descr^" "^ports) end)

fun dump_iptables [] = ()
  | dump_iptables (SimpleRule (m, a) :: rs) =
      (writeln (dump_action a ^ "     " ^
               (dump_prot (proto m)) ^ "  --  " ^
               (dump_ip (src m)) ^ "            " ^
               (dump_ip (dst m)) ^ " " ^
               (dump_iface_name "in:" (iiface m)) ^ " " ^
               (dump_iface_name "out:" (oiface m)) ^ " " ^
               (dump_ports "srcports:" (sports m)) ^ " " ^
               (dump_ports "dstports:" (dports m)) ); dump_iptables rs);

*}


text{*iptables -L -n*}
ML_val{*
writeln "Chain INPUT (policy ACCEPT)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy ACCEPT)";
writeln "target     prot opt source               destination";
dump_iptables (to_simple_firewall upper);
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
dump_iptables (to_simple_firewall lower);
writeln "Chain OUTPUT (policy ACCEPT)";
writeln "target     prot opt source               destination"
*}
end
