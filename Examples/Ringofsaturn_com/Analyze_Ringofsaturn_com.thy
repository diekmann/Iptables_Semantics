theory Analyze_Ringofsaturn_com
imports
 "../Code_Interface"
 "../../Semantics_Ternary/Optimizing"
 "../Parser"
begin

section{*Example: ringofsaturn.com*}

(* Based on <http://networking.ringofsaturn.com/Unix/iptables.php> *)
(* Archived at <https://archive.today/3c309> *)

parse_iptables_save saturn_fw="iptables-save"

thm saturn_fw_def

text{*The Firewall*}

text{*Infix pretty-printing for @{const MatchAnd} and @{const MatchNot}.*}
abbreviation MatchAndInfix :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" (infixr "MATCHAND" 65) where
  "MatchAndInfix m1 m2 \<equiv> MatchAnd m1 m2"
abbreviation MatchNotPrefix :: "'a match_expr \<Rightarrow> 'a match_expr" ("\<not> \<langle>_\<rangle>" 66) where
  "MatchNotPrefix m \<equiv> MatchNot m"
(*This syntax can be pretty confusing when mixing it with other theories. Do not use outside this example!*)

value[code] "unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw)"
lemma "unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw) =
 [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept,
  Rule (Match (CT_State {CT_New})) action.Accept,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop,
  Rule (Match (IIface (Iface ''lo''))) action.Accept,
  Rule ((Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule ((Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (160, 86, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth1''))) action.Accept,
  Rule (Match (IIface (Iface ''eth1''))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 3'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 11'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 0'')) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP)) MATCHAND Match (Extra ''-m icmp --icmp-type 8'')) action.Accept,
  Rule (Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x6F, 0x6F)])) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x71, 0x71)])) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(4, 4)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x14, 0x14)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x15, 0x15)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x14, 0x14)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x15, 0x15)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x16, 0x16)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x16, 0x16)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x50, 0x50)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x50, 0x50)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x1BB, 0x1BB)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x1BB, 0x1BB)])) action.Accept,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x208, 0x208)])) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)) MATCHAND Match (Dst_Ports [(0x89, 0x8B)])) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)) MATCHAND Match (Dst_Ports [(0x89, 0x8B)])) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop,
  Rule MatchAny action.Accept]" by eval

lemma "good_ruleset (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))" by eval
lemma "simple_ruleset (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))" by eval

text{*Basically, it accepts everything*}
lemma "take 2 (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw)) =
    [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept, Rule (Match (CT_State {CT_New})) action.Accept]" by eval

(*TODO: all the CT states are essentially the universe*)

text{*The upper closure*}
(*value[code] "upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))"*)
lemma upper: "upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw)) =
 [Rule (Match (CT_State {CT_Related, CT_Established})) action.Accept,
  Rule (Match (CT_State {CT_New})) action.Accept,
  Rule (Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Drop,
  Rule (Match (IIface (Iface ''lo''))) action.Accept,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (160, 86, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth1''))) action.Accept,
  Rule (Match (IIface (Iface ''eth1''))) action.Drop, Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP))) action.Accept,
  Rule (Match (Dst_Ports [(0x6F, 0x6F)]) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(0x71, 0x71)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(4, 4)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x14, 0x14)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x15, 0x15)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x14, 0x14)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x15, 0x15)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x16, 0x16)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x16, 0x16)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x50, 0x50)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x50, 0x50)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x1BB, 0x1BB)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x1BB, 0x1BB)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x208, 0x208)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Dst_Ports [(0x89, 0x8B)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(0x89, 0x8B)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule MatchAny action.Accept]"
 by eval



text{*The firewall accepts all NEW packets*}
lemma "cutt_off_after_default (rmMatchFalse (ctstate_assume_new
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))))
        = [Rule MatchAny action.Accept]"
by eval

text{*The firewall also accepts all ESTABLISHED packets. Essentially, it accepts all packets!*}
lemma "cutt_off_after_default (rmMatchFalse (optimize_matches (ctstate_assume_state CT_Established)
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))))
        = [Rule MatchAny action.Accept]"
by eval



lemma "approximating_bigstep_fun (common_matcher, in_doubt_allow)
        \<lparr>p_iiface = ''eth0'', p_oiface = ''eth1'', p_src = ipv4addr_of_dotdecimal (192,168,2,45), p_dst= ipv4addr_of_dotdecimal (173,194,112,111),
         p_proto=TCP, p_sport=2065, p_dport=80, p_tag_ctstate = CT_New\<rparr>
          (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw))
         Undecided
        = Decision FinalAllow" by eval


text{*We are removing the first call to the @{term "''STATEFUL''"} chain.*}

definition "saturn_fw_2 = map (\<lambda> (decl, rs). if decl = ''INPUT'' then (decl, remove1 (Rule MatchAny (Call ''STATEFUL'')) rs) else (decl, rs)) saturn_fw"

lemma "tl (the ((map_of_string saturn_fw) ''INPUT'')) = the ((map_of_string saturn_fw_2) ''INPUT'')" by eval


text{*in doubt allow closure*}
definition "upper = upper_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw_2))"

text{*Now the upper closure looks as expected*}
lemma "upper =
 [Rule (Match (IIface (Iface ''lo''))) action.Accept,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (0, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (10, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (127, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (169, 254, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (172, 16, 0, 0) 12)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (224, 0, 0, 0) 3)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP)))
   action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (240, 0, 0, 0) 8)) MATCHAND Match (IIface (Iface ''eth0''))) action.Drop,
  Rule (Match (Src (Ip4AddrNetmask (160, 86, 0, 0) 16)) MATCHAND Match (IIface (Iface ''eth1''))) action.Accept,
  Rule (Match (IIface (Iface ''eth1''))) action.Drop,
  Rule (Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto ICMP))) action.Accept,
  Rule (Match (Dst_Ports [(0x6F, 0x6F)]) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(0x71, 0x71)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(4, 4)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x14, 0x14)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x15, 0x15)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x14, 0x14)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x15, 0x15)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x16, 0x16)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x16, 0x16)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x50, 0x50)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x50, 0x50)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x1BB, 0x1BB)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Accept,
  Rule (Match (Dst_Ports [(0x1BB, 0x1BB)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Accept,
  Rule (Match (Dst_Ports [(0x208, 0x208)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Dst_Ports [(0x89, 0x8B)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto TCP))) action.Drop,
  Rule (Match (Dst_Ports [(0x89, 0x8B)]) MATCHAND Match (IIface (Iface ''eth0'')) MATCHAND Match (Prot (Proto UDP))) action.Drop,
  Rule (Match (Prot (Proto TCP))) action.Drop, Rule (Match (Prot (Proto UDP))) action.Drop, Rule MatchAny action.Drop,
  Rule MatchAny action.Accept]" by eval


value[code] "zip (upto 0 (int (length upper))) upper"
lemma "good_ruleset upper" by eval
lemma "simple_ruleset upper" by eval

lemma "check_simple_fw_preconditions upper" by eval
value "map simple_rule_toString (to_simple_firewall upper)"


text{*in doubt deny closure*}
value[code] "lower_closure (unfold_ruleset_INPUT saturn_fw_INPUT_default_policy (map_of_string saturn_fw_2))"


end
