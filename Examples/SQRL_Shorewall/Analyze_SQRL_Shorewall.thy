theory Analyze_SQRL_Shorewall
imports Main "../../Output_Format/IPSpace_Format_Ln" "../../Call_Return_Unfolding" "../../Optimizing"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
begin


section{*Example: SQRL Shorewall*}

definition unfold_ruleset_FORWARD :: "iptrule_match ruleset \<Rightarrow> iptrule_match rule list" where
"unfold_ruleset_FORWARD rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call rs)^^20) [Rule MatchAny (Call ''FORWARD'')]))))"


definition unfold_ruleset_OUTPUT :: "iptrule_match ruleset \<Rightarrow> iptrule_match rule list" where
"unfold_ruleset_OUTPUT rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call rs)^^20) [Rule MatchAny (Call ''OUTPUT'')]))))"


definition map_of_string :: "(string \<times> iptrule_match rule list) list \<Rightarrow> string \<rightharpoonup> iptrule_match rule list" where
"map_of_string rs = map_of rs"



definition upper_closure :: "iptrule_match rule list \<Rightarrow> iptrule_match rule list" where
  "upper_closure rs == rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^2000) (optimize_matches_a upper_closure_matchexpr rs))"
definition lower_closure :: "iptrule_match rule list \<Rightarrow> iptrule_match rule list" where
  "lower_closure rs == rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^2000) (optimize_matches_a lower_closure_matchexpr rs))"

export_code unfold_ruleset_OUTPUT map_of_string upper_closure lower_closure format_Ln_rules_uncompressed compress_Ln_ips does_I_has_compressed_rules 
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtAll ProtTCP ProtUDP
  Src Dst Prot Extra
  nat_of_integer integer_of_nat
  UncompressedFormattedMatch Pos Neg
  does_I_has_compressed_prots
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"


(*../main.py -t ml --module Test akachan-iptables-Ln akachan-iptables-Ln.ML
File generated 1. Sept 2014
add "open Test" to second line
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
