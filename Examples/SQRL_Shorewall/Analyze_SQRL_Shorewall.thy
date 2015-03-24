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

(*./main.py -t ml --module=test  ../Examples/SQRL_Shorewall/akachan-iptables-Ln ../Examples/SQRL_Shorewall/akachan-iptables-Ln.ML
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
length upper;*}
ML{*
val lower = lower_closure rules;
length lower;*}

ML{*
fun dump_ip (Ip4Addr (a,(b,(c,d)))) = ""^ Int.toString (integer_of_nat a)^"."^ Int.toString (integer_of_nat b)^"."^ Int.toString (integer_of_nat c)^"."^ Int.toString (integer_of_nat d)^"/32"
  | dump_ip (Ip4AddrNetmask ((a,(b,(c,d))), nm)) = 
      ""^ Int.toString (integer_of_nat a)^"."^ Int.toString (integer_of_nat b)^"."^ Int.toString (integer_of_nat c)^"."^ Int.toString (integer_of_nat d)^"/"^ Int.toString (integer_of_nat nm);

fun dump_prot ProtAll = "all"
  | dump_prot ProtTCP = "tcp"
  | dump_prot ProtUDP = "udp";

fun dump_prots [] = "all"
  | dump_prots [Pos p] = dump_prot p
  | dump_prots [Neg p] = "!"^dump_prot p;
  (*undefined otherwise*)

fun dump_extra [] = "";

fun dump_action Accept = "ACCEPT"
  | dump_action Drop = "DROP"
  | dump_action Log = "LOG"
  | dump_action Reject = "REJECT"
;

local
  fun dump_ip_list_hlp [] = ""
    | dump_ip_list_hlp ((Pos ip)::ips) = ((dump_ip ip) ^ dump_ip_list_hlp ips)
    | dump_ip_list_hlp ((Neg ip)::ips) = ("!" ^ (dump_ip ip) ^ dump_ip_list_hlp ips)
in
  fun dump_ip_list [] = "0.0.0.0/0"
    | dump_ip_list rs = dump_ip_list_hlp rs
end;
  

fun dump_iptables [] = ()
  | dump_iptables ((UncompressedFormattedMatch (src, dst, proto, extra), a) :: rs) =
      (writeln (dump_action a ^ "     " ^
                "" ^ dump_prots proto ^ "  --  "^ 
                "" ^ dump_ip_list src ^ "            " ^
                "" ^ dump_ip_list dst ^ "    " ^
                "" ^ dump_extra extra); dump_iptables rs);
*}

ML_val{*
length (format_Ln_rules_uncompressed upper);
(format_Ln_rules_uncompressed upper);
*}
ML_val{*
(compress_Ln_ips (format_Ln_rules_uncompressed upper));
*}
ML_val{*
length (does_I_has_compressed_rules (compress_Ln_ips (format_Ln_rules_uncompressed upper)));
does_I_has_compressed_rules (compress_Ln_ips (format_Ln_rules_uncompressed upper));
*}
ML_val{*
does_I_has_compressed_prots (compress_Ln_ips (format_Ln_rules_uncompressed upper));
*}
ML_val{*
dump_iptables (compress_Ln_ips (format_Ln_rules_uncompressed upper));
*}


ML_val{*
compress_Ln_ips (format_Ln_rules_uncompressed lower);
*}
ML_val{*
length (does_I_has_compressed_rules (compress_Ln_ips (format_Ln_rules_uncompressed lower)));
does_I_has_compressed_rules (compress_Ln_ips (format_Ln_rules_uncompressed lower));
*}
ML_val{*
does_I_has_compressed_prots (compress_Ln_ips (format_Ln_rules_uncompressed lower));
*}

end
