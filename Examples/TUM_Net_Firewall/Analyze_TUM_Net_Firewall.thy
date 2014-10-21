theory Analyze_TUM_Net_Firewall
imports Main "../../Output_Format/IPSpace_Format_Ln" "../../Call_Return_Unfolding" "../../Optimizing"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Char"
  "../../Packet_Set"
begin


section{*Example: Chair for Network Architectures and Services (TUM)*}

definition unfold_ruleset_FORWARD :: "iptrule_match ruleset \<Rightarrow> iptrule_match rule list" where
"unfold_ruleset_FORWARD rs = ((optimize_matches opt_MatchAny_match_expr)^^10) 
  (optimize_matches opt_simple_matcher (rw_Reject (rm_LogEmpty (((process_call rs)^^5) [Rule MatchAny (Call ''FORWARD'')]))))"


definition map_of_string :: "(string \<times> iptrule_match rule list) list \<Rightarrow> string \<rightharpoonup> iptrule_match rule list" where
"map_of_string rs = map_of rs"


definition upper_closure :: "iptrule_match rule list \<Rightarrow> iptrule_match rule list" where
  "upper_closure rs == rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^2000) (optimize_matches_a opt_simple_matcher_in_doubt_allow_extra rs))"
definition lower_closure :: "iptrule_match rule list \<Rightarrow> iptrule_match rule list" where
  "lower_closure rs == rmMatchFalse (((optimize_matches opt_MatchAny_match_expr)^^2000) (optimize_matches_a opt_simple_matcher_in_doubt_deny_extra rs))"



definition deny_set :: "iptrule_match rule list \<Rightarrow> iptrule_match packet_set list" where
  "deny_set rs \<equiv> filter (\<lambda>a. a \<noteq> packet_set_UNIV) (map packet_set_opt (allow_set_not_inter rs))"
(*definition allow_set_debug :: "iptrule_match rule list \<Rightarrow> iptrule_match packet_set" where
  "allow_set_debug rs \<equiv> collect_allow_impl_debug rs packet_set_UNIV"*)


definition bitmask_to_strange_inverse_cisco_mask:: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
 "bitmask_to_strange_inverse_cisco_mask n \<equiv> dotteddecimal_of_ipv4addr ( (NOT (((mask n)::ipv4addr) << (32 - n))) )"
lemma "bitmask_to_strange_inverse_cisco_mask 16 = (0, 0, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 24 = (0, 0, 0, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 8 = (0, 255, 255, 255)" by eval
lemma "bitmask_to_strange_inverse_cisco_mask 32 = (0, 0, 0, 0)" by eval


export_code unfold_ruleset_FORWARD map_of_string upper_closure lower_closure format_Ln_rules_uncompressed compress_Ln_ips does_I_has_compressed_rules 
  Rule
  Accept Drop Log Reject Call Return Empty  Unknown
  Match MatchNot MatchAnd MatchAny
  Ip4Addr Ip4AddrNetmask
  ProtAll ProtTCP ProtUDP
  Src Dst Prot Extra
  nat_of_integer integer_of_nat
  UncompressedFormattedMatch Pos Neg
  does_I_has_compressed_prots
  bitmask_to_strange_inverse_cisco_mask
  deny_set
  in SML module_name "Test" file "unfold_code.ML"

ML_file "unfold_code.ML"

(*ML_file "iptables_Ln_29.11.2013_cheating.ML"*)

(*../main.py -t ml --module Test iptables_Ln_29.11.2013_cheating iptables_Ln_29.11.2013.ML
add "open Test" to second line
*)
ML_file "iptables_Ln_29.11.2013.ML"

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


(*iptables_Ln_29.11.2013 netnetwork*)

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
length upper;*}
ML{*
val lower = lower_closure rules;
length lower;*}

text{*How long does the unfolding take?*}
ML_val{*
val t0 = Time.now();
val _ = unfold_ruleset_FORWARD (map_of_string firewall_chains);
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than 1 second.*}

text{*Time required for calculating both closures*}
ML_val{*
val t0 = Time.now();
val _ = upper_closure rules;
val _ = lower_closure rules;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}
text{*on my system, less than five seconds.*}

ML{*
fun dump_dotteddecimal_ip (a,(b,(c,d))) = ""^ Int.toString (integer_of_nat a)^"."^ Int.toString (integer_of_nat b)^"."^ Int.toString (integer_of_nat c)^"."^ Int.toString (integer_of_nat d);

fun dump_ip (Ip4Addr ip) = (dump_dotteddecimal_ip ip)^"/32"
  | dump_ip (Ip4AddrNetmask (ip, nm)) = (dump_dotteddecimal_ip ip)^"/"^ Int.toString (integer_of_nat nm);

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

fun dump_iptables_save [] = ()
  | dump_iptables_save ((UncompressedFormattedMatch (src, dst, proto, []), a) :: rs) =
      (writeln ("-A FORWARD  " ^
                (if List.length src = 1 then "-s " ^ dump_ip_list src ^ " " else if List.length src > 1 then "ERROR" else "")^
                (if List.length dst = 1 then "-d " ^ dump_ip_list dst ^ " " else if List.length dst > 1 then "ERROR" else "")^
                (if List.length proto = 1 then "-p " ^ dump_prots proto ^ " " else if List.length proto > 1 then "ERROR" else "")^
                "" ^ " -j " ^ dump_action a); dump_iptables_save rs);
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

text{*iptables -L -n*}

ML_val{*
writeln "Chain INPUT (policy ACCEPT)";
writeln "target     prot opt source               destination";
writeln "";
writeln "Chain FORWARD (policy ACCEPT)";
writeln "target     prot opt source               destination";
dump_iptables (compress_Ln_ips (format_Ln_rules_uncompressed upper));

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
dump_iptables (compress_Ln_ips (format_Ln_rules_uncompressed lower));

writeln "Chain OUTPUT (policy ACCEPT)";
writeln "target     prot opt source               destination"
*}

text{*iptables-save*}
ML_val{*
writeln "# Generated by iptables-save v1.4.21 on Wed Sep  3 18:02:01 2014";
writeln "*filter";
writeln ":INPUT ACCEPT [0:0]";
writeln ":FORWARD ACCEPT [0:0]";
writeln ":OUTPUT ACCEPT [0:0]";
dump_iptables_save (compress_Ln_ips (format_Ln_rules_uncompressed upper));
writeln "COMMIT";
writeln "# Completed on Wed Sep  3 18:02:01 2014";
*}


text{*Cisco*}
ML{*
fun dump_action_cisco Accept = "permit"
  | dump_action_cisco Drop = "deny"
;


fun dump_prot_cisco [] = "ip"
  | dump_prot_cisco [Pos ProtAll] = "ip"
  | dump_prot_cisco [Pos ProtTCP] = "tcp"
  | dump_prot_cisco [Pos ProtUDP] = "udp";


local
  fun dump_ip_cisco (Ip4Addr ip) = "host "^(dump_dotteddecimal_ip ip)
    | dump_ip_cisco (Ip4AddrNetmask (ip, nm)) = (dump_dotteddecimal_ip ip)^" "^(dump_dotteddecimal_ip (bitmask_to_strange_inverse_cisco_mask nm));
in
  fun dump_ip_list_cisco [] = "any"
    | dump_ip_list_cisco [Pos ip] = dump_ip_cisco ip
    | dump_ip_list_cisco [Neg ip] = "TODO"^dump_ip_cisco ip
end;


fun dump_cisco [] = ()
  | dump_cisco ((UncompressedFormattedMatch (src, dst, proto, []), a) :: rs) =
      (writeln ("access-list 101 " ^ dump_action_cisco a ^ 
                (if List.length proto <= 1 then " " ^ dump_prot_cisco proto ^ " " else "ERROR")^
                (dump_ip_list_cisco src)^" "^(dump_ip_list_cisco dst)); dump_cisco rs);
*}

ML_val{*
writeln "interface fe0";
writeln "ip address 10.1.1.1 255.255.255.254";
writeln "ip access-group 101 in";
writeln "!";
dump_cisco (compress_Ln_ips (format_Ln_rules_uncompressed upper));
(*access-list 101 deny ip host 10.1.1.2 any
access-list 101 permit tcp any host 192.168.5.10 eq 80
access-list 101 permit tcp any host 192.168.5.11 eq 25
access-list 101 deny any*)
writeln "!";
writeln "! // need to give the end command";
writeln "end";

*}

(* openvswitch flow table entries *)
ML{*

fun dump_action_flowtable Accept = "flood"
  | dump_action_flowtable Drop = "drop"
;

local
  fun dump_ip_flowtable (Ip4Addr ip) = (dump_dotteddecimal_ip ip)
    | dump_ip_flowtable (Ip4AddrNetmask (ip, nm)) = (dump_dotteddecimal_ip ip)^"/"^ Int.toString (integer_of_nat nm);
in
  fun dump_ip_list_flowtable [] = "*"
    | dump_ip_list_flowtable [Pos ip] = dump_ip_flowtable ip
    | dump_ip_list_flowtable [Neg ip] = "TODO"^dump_ip_flowtable ip
end;

fun dump_flowtable [] = ()
  | dump_flowtable ((UncompressedFormattedMatch (src, dst, proto, []), a) :: rs) =
      (writeln ((if List.length proto <= 1 then "" ^ dump_prot_cisco proto ^ " " else "ERROR")^
                "nw_src="^(dump_ip_list_flowtable src)^" nw_dst="^(dump_ip_list_flowtable dst) ^
                " priority="^Int.toString (List.length rs)^
                " action="^dump_action_flowtable a
                ); dump_flowtable rs);
*}
ML_val{*
(*ip nw_src=10.0.0.1/32 nw_dst=* priority=30000 action=flood*)

dump_flowtable (compress_Ln_ips (format_Ln_rules_uncompressed upper));
*}


text{*packet set (test)*}
ML{*
val t0 = Time.now();
val deny_set_set = deny_set upper;
val t1= Time.now();
writeln(String.concat ["It took ", Time.toString(Time.-(t1,t0)), " seconds"])
*}

(*result when packet_set_opt2_internal was not recursive within 2 minutes: 95.949 seconds 
no results for recursive packet_set_opt2_internal now
  ("packet_set_opt2_internal (as#ps) = (as#((filter (\<lambda>ass. \<not> set as \<subseteq> set ass) (packet_set_opt2_internal ps))))"

first filter than recursive call  943.219seconds (15 min) *)

ML_val{*
length deny_set_set;
*}
ML_val{*
deny_set_set;
*}
(*test with rules*)

end
