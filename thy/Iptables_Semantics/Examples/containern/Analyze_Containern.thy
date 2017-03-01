theory Analyze_Containern
imports 
  "../../Primitive_Matchers/Parser"
begin



parse_iptables_save docker_fw="iptables-save.topos4.1.established"

thm docker_fw_def
thm docker_fw_FORWARD_default_policy_def


definition "unfolded_FORWARD = unfold_ruleset_FORWARD docker_fw_FORWARD_default_policy (map_of_string_ipv4 (docker_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_FORWARD)"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_FORWARD)"


value[code] "upper_closure (packet_assume_new unfolded_FORWARD)"

lemma "check_simple_fw_preconditions (upper_closure (optimize_matches abstract_for_simple_firewall 
          (upper_closure (packet_assume_new unfolded_FORWARD))))" by eval

lemma "simple_fw_valid (to_simple_firewall (upper_closure
              (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"
by eval
lemma "simple_fw_valid (to_simple_firewall (lower_closure
              (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"
by eval


value[code] "map simple_rule_ipv4_toString (to_simple_firewall (upper_closure
              (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"

value[code] "map simple_rule_ipv4_toString (to_simple_firewall (lower_closure
              (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"



(*Interfaces be gone! necessary for ip partition!*)
definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a
                                                                 | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (closure
              (iface_try_rewrite ipassmt None
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"

definition preprocess_ESTABLISHED where
  "preprocess_ESTABLISHED unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a
                                                                 | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (closure
              (iface_try_rewrite ipassmt None
              (closure
              (optimize_matches (ctstate_assume_state CT_Established)
              (unfold def (map_of fw))))))))"
  
  (*incomplete, but we won't need it anyway*)
 definition ipassmt :: "(iface \<times> (32 word \<times> nat) list) list" where
 "ipassmt = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''br-b74b417b331f'', [(ipv4addr_of_dotdecimal (10,0,0,0),8)])
  ]"
  lemma "distinct (map fst ipassmt)" by eval
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt)" by eval
  value[code] "map_of_ipassmt ipassmt"

value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt docker_fw_FORWARD_default_policy docker_fw)"

value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt docker_fw_FORWARD_default_policy docker_fw)"


value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt docker_fw_FORWARD_default_policy docker_fw)"

value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt docker_fw_FORWARD_default_policy docker_fw)"


parse_iptables_save docker_fw2="iptables-save.topos4.1"

thm docker_fw2_def
thm docker_fw2_FORWARD_default_policy_def


value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2)"

value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2)"


value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2)"

value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2)"

text{*Only one of the flows additionally allows answers for ESTABLISHED connections*}
lemma "let new = access_matrix_pretty_ipv4 parts_connection_http 
                    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2);
                 est = access_matrix_pretty_ipv4 parts_connection_http 
                    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt docker_fw2_FORWARD_default_policy docker_fw2)
    in  fst est = fst new \<and>
        set (snd est) - set (snd new) = {(''0.0.0.0'', ''10.0.0.4'')}" by eval


  
  
  
parse_iptables_save docker_fw_initial="iptables-save.topos1"

thm docker_fw_initial_def
thm docker_fw_initial_FORWARD_default_policy_def

(*The original docker0 bridge is still in this dump. We need some information about it.*)
definition ipassmt_initial :: "(iface \<times> (32 word \<times> nat) list) list" where
 "ipassmt_initial = (Iface ''docker0'', [(ipv4addr_of_dotdecimal (172,17,0,1),16)])#ipassmt"
  lemma "distinct (map fst ipassmt_initial)" by eval
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt_initial)" by eval


value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt_initial docker_fw_initial_FORWARD_default_policy docker_fw_initial)"

value[code] "access_matrix_pretty_ipv4 parts_connection_ssh 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt_initial docker_fw_initial_FORWARD_default_policy docker_fw_initial)"

value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt_initial docker_fw_initial_FORWARD_default_policy docker_fw_initial)"

value[code] "access_matrix_pretty_ipv4 parts_connection_http 
    (preprocess_ESTABLISHED unfold_ruleset_FORWARD upper_closure ipassmt_initial docker_fw_initial_FORWARD_default_policy docker_fw_initial)"

end