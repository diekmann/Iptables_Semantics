theory Analyze_Ringofsaturn_com
imports
  "../../Primitive_Matchers/Parser"
begin


section\<open>Example: ringofsaturn.com\<close>

(* Based on <http://networking.ringofsaturn.com/Unix/iptables.php> *)
(* Archived at <https://archive.today/3c309> *)

parse_iptables_save saturn_fw="iptables-save"

thm saturn_fw_def

text\<open>The Firewall\<close>

text\<open>Infix pretty-printing for @{const MatchAnd} and @{const MatchNot}.\<close>
abbreviation MatchAndInfix :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" (infixr "MATCHAND" 65) where
  "MatchAndInfix m1 m2 \<equiv> MatchAnd m1 m2"
abbreviation MatchNotPrefix :: "'a match_expr \<Rightarrow> 'a match_expr" ("\<not> \<langle>_\<rangle>" 66) where
  "MatchNotPrefix m \<equiv> MatchNot m"
(*This syntax can be pretty confusing when mixing it with other theories. Do not use outside this example!*)

value[code] "unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw)"
lemma "unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw) =
 [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept,
  Rule (Match (CT_State {CT_New})) action.Accept,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop,
  Rule (Match (IIface (Iface ''lo''))) action.Accept,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (160, 86, 0, 0)) 16)) MATCHAND Match (IIface (Iface ''eth1''))) action.Accept,
  Rule (Match (IIface (Iface ''eth1''))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 3'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 11'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 0'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8'')) action.Accept,
  Rule (Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x6F, 0x6F)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x71, 0x71)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(4, 4)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x14, 0x14)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x15, 0x15)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x14, 0x14)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x15, 0x15)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x16, 0x16)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x16, 0x16)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x50, 0x50)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x50, 0x50)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x1BB, 0x1BB)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x1BB, 0x1BB)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x208, 0x208)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x89, 0x8B)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x89, 0x8B)]))) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop,
  Rule MatchAny action.Accept]" by eval

lemma "good_ruleset (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))" by eval
lemma "simple_ruleset (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))" by eval

text\<open>Basically, it accepts everything\<close>
lemma "take 2 (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw)) =
    [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept, Rule (Match (CT_State {CT_New})) action.Accept]" by eval


text\<open>The upper closure\<close>
value[code] "upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))"
lemma upper: "upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw)) =
 [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept,
  Rule (Match (CT_State {CT_New})) action.Accept,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop
  ]"
 by eval



text\<open>The firewall accepts all NEW packets\<close>
lemma "cut_off_after_match_any (rmMatchFalse (ctstate_assume_new
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))))
        = [Rule MatchAny action.Accept]"
by eval

text\<open>The firewall also accepts all ESTABLISHED packets. Essentially, it accepts all packets!\<close>
lemma "cut_off_after_match_any (rmMatchFalse (optimize_matches (ctstate_assume_state CT_Established)
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))))
        = [Rule MatchAny action.Accept]"
by eval



lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
        \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'',
         p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tcp_flags = {TCP_SYN},
         p_payload='''', p_tag_ctstate = CT_New\<rparr>
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw))
         Undecided
        = Decision FinalAllow" by eval


text\<open>We are removing the first call to the @{term "''STATEFUL''"} chain.\<close>

definition "saturn_fw_2 = map (\<lambda> (decl, rs). if decl = ''INPUT'' then (decl, remove1 (Rule MatchAny (Call ''STATEFUL'')) rs) else (decl, rs)) saturn_fw"

lemma "tl (the ((map_of_string_ipv4 saturn_fw) ''INPUT'')) = the ((map_of_string_ipv4 saturn_fw_2) ''INPUT'')" by eval


text\<open>in doubt allow closure\<close>
definition "upper = upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw_2))"

text\<open>Now the upper closure looks as expected\<close>
lemma "upper =
 [Rule (Match (IIface (Iface ''lo''))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask 0 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 8))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (10, 0, 0, 0)) 8))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (169, 254, 0, 0)) 16))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (172, 16, 0, 0)) 12))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (224, 0, 0, 0)) 3))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8)))
   action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (240, 0, 0, 0)) 8))) action.Drop,
  Rule (Match (IIface (Iface ''eth1'')) MATCHAND Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (160, 86, 0, 0)) 16))) action.Accept,
  Rule (Match (IIface (Iface ''eth1''))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP))) action.Accept,
  Rule (Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x6F, 0x6F)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x71, 0x71)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(4, 4)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x14, 0x14)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x15, 0x15)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))MATCHAND Match (Dst_Ports (L4Ports UDP [(0x14, 0x14)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x15, 0x15)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x16, 0x16)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x16, 0x16)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x50, 0x50)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x50, 0x50)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x1BB, 0x1BB)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x1BB, 0x1BB)]))) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x208, 0x208)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports (L4Ports TCP [(0x89, 0x8B)]))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports (L4Ports UDP [(0x89, 0x8B)]))) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop
  ]" by eval


value[code] "zip (upto 0 (int (length upper))) upper"
lemma "good_ruleset upper" by eval
lemma "simple_ruleset upper" by eval

lemma "check_simple_fw_preconditions upper \<and> simple_fw_valid (to_simple_firewall upper)" by eval
value "map simple_rule_ipv4_toString (to_simple_firewall upper)"


text\<open>in doubt deny closure\<close>
value[code] "lower_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw_2))"

lemma "simple_fw_valid (to_simple_firewall upper)" by eval
lemma "simple_fw_valid (to_simple_firewall (lower_closure 
	(unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string_ipv4 saturn_fw_2))))" by eval

end
