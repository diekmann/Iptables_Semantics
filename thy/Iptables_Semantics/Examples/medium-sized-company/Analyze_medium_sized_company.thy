theory Analyze_medium_sized_company
imports 
  "../../Primitive_Matchers/Parser"
begin



parse_iptables_save company_fw="iptables-save"

thm company_fw_def
thm company_fw_INPUT_default_policy_def

value[code] "map (\<lambda>(c,rs). (c, map (quote_rewrite \<circ> common_primitive_rule_toString) rs)) company_fw"

definition "unfolded_INPUT = unfold_ruleset_INPUT company_fw_INPUT_default_policy (map_of_string_ipv4 (company_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_INPUT)"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_INPUT)"


value[code] "upper_closure (packet_assume_new unfolded_INPUT)"

lemma "check_simple_fw_preconditions 
    (upper_closure (optimize_matches abstract_for_simple_firewall
      (upper_closure (packet_assume_new unfolded_INPUT))))" by eval


value[code] "map simple_rule_ipv4_toString (to_simple_firewall
    (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_INPUT)))))"

value[code] "map simple_rule_ipv4_toString (to_simple_firewall
    (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_INPUT)))))"









definition "unfolded_FORWARD = unfold_ruleset_FORWARD company_fw_FORWARD_default_policy (map_of_string_ipv4 (company_fw))"

value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (unfolded_FORWARD)"


value[code] "map (quote_rewrite \<circ> common_primitive_rule_toString) (upper_closure unfolded_FORWARD)"


value[code] "upper_closure (packet_assume_new unfolded_FORWARD)"

lemma "check_simple_fw_preconditions
    (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD))))" by eval


value[code] "map simple_rule_ipv4_toString (to_simple_firewall
    (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"

value[code] "map simple_rule_ipv4_toString (to_simple_firewall
    (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"

lemma "simple_fw_valid (to_simple_firewall
    (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"
  by eval

lemma "simple_fw_valid (to_simple_firewall
    (lower_closure (optimize_matches abstract_for_simple_firewall (lower_closure (packet_assume_new unfolded_FORWARD)))))"
  by eval
(*
text{*If we call the IP address spcae partitioning incorrectly (not prepocessed, still has interfaces), we get an error*}
value[code] " parts_connection_ssh 
  (to_simple_firewall (upper_closure (optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new unfolded_FORWARD)))))"
*)


(*Interfaces be gone! necessary for ip partition!*)
definition preprocess where
  "preprocess unfold closure ipassmt def fw \<equiv> to_simple_firewall (closure
              (optimize_matches (abstract_primitive (\<lambda>r. case r of Pos a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_L4_Flags a | Neg a \<Rightarrow> is_Iiface a \<or> is_Oiface a \<or> is_Prot a \<or> is_L4_Flags a))
              (closure
              (iface_try_rewrite ipassmt
              (closure
              (packet_assume_new
              (unfold def (map_of fw))))))))"

 definition "ipassmt = [(Iface ''lo'', [(ipv4addr_of_dotdecimal (127,0,0,0),8)]),
  (Iface ''eth0'', [(ipv4addr_of_dotdecimal (172,16,2,0),24)])
  ]"

lemma "access_matrix_pretty_ipv4 parts_connection_ssh
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt company_fw_FORWARD_default_policy company_fw) =
 ([(''46.4.115.113'',
    ''46.4.115.113 u {46.20.32.74 .. 46.20.32.75} u 54.68.106.202 u 62.141.33.131 u ''@
    ''63.245.217.112 u 74.119.117.71 u 80.190.166.25 u 80.237.184.24 u 80.252.91.41 u ''@
    ''82.196.187.209 u 82.199.80.141 u 83.133.189.139 u 83.169.54.252 u 83.169.59.64 u ''@
    ''85.25.248.94 u 85.90.254.45 u 85.195.127.21 u 88.198.208.110 u 91.215.101.185 u ''@
    ''93.184.220.20 u 93.184.221.133 u 94.198.59.132 u 94.198.59.134 u 95.131.121.65 u ''@
    ''95.131.121.199 u 95.172.69.42 u 144.76.67.119 u 151.80.102.139 u 176.9.103.51 u ''@
    ''178.63.153.114 u 178.250.0.101 u 178.250.2.73 u 178.250.2.77 u 178.250.2.98 u ''@
    ''178.250.2.102 u 184.168.47.225 u 188.65.74.70 u 194.97.151.143 u 194.97.153.231 u ''@
    ''194.126.239.34 u 195.20.250.231 u 206.191.168.170 u 212.45.104.69 u 212.227.67.37 u ''@
    ''213.9.42.248 u 213.203.221.32 u 213.203.221.43 u 216.38.172.131 u 217.72.250.66 u 217.72.250.84 u 217.72.250.89''),
   (''192.168.255.0'',
    ''{192.168.255.0 .. 192.168.255.255}''),
   (''172.16.2.0'',
    ''{172.16.2.0 .. 172.16.2.15} u 172.16.2.34 u 172.16.2.230 u {172.16.2.247 .. 172.16.2.255}''),
   (''172.16.2.16'',
    ''{172.16.2.16 .. 172.16.2.33} u {172.16.2.35 .. 172.16.2.229} u {172.16.2.231 .. 172.16.2.246}''),
   (''0.0.0.0'',
    ''{0.0.0.0 .. 46.4.115.112} u {46.4.115.114 .. 46.20.32.73} u {46.20.32.76 .. 54.68.106.201} u ''@
    ''{54.68.106.203 .. 62.141.33.130} u {62.141.33.132 .. 63.245.217.111} u ''@
    ''{63.245.217.113 .. 74.119.117.70} u {74.119.117.72 .. 80.190.166.24} u ''@
    ''{80.190.166.26 .. 80.237.184.23} u {80.237.184.25 .. 80.252.91.40} u ''@
    ''{80.252.91.42 .. 82.196.187.208} u {82.196.187.210 .. 82.199.80.140} u ''@
    ''{82.199.80.142 .. 83.133.189.138} u {83.133.189.140 .. 83.169.54.251} u ''@
    ''{83.169.54.253 .. 83.169.59.63} u {83.169.59.65 .. 85.25.248.93} u ''@
    ''{85.25.248.95 .. 85.90.254.44} u {85.90.254.46 .. 85.195.127.20} u ''@
    ''{85.195.127.22 .. 88.198.208.109} u {88.198.208.111 .. 91.215.101.184} u ''@
    ''{91.215.101.186 .. 93.184.220.19} u {93.184.220.21 .. 93.184.221.132} u ''@
    ''{93.184.221.134 .. 94.198.59.131} u 94.198.59.133 u {94.198.59.135 .. 95.131.121.64} u ''@
    ''{95.131.121.66 .. 95.131.121.198} u {95.131.121.200 .. 95.172.69.41} u ''@
    ''{95.172.69.43 .. 144.76.67.118} u {144.76.67.120 .. 151.80.102.138} u ''@
    ''{151.80.102.140 .. 172.16.1.255} u {172.16.3.0 .. 176.9.103.50} u ''@
    ''{176.9.103.52 .. 178.63.153.113} u {178.63.153.115 .. 178.250.0.100} u ''@
    ''{178.250.0.102 .. 178.250.2.72} u {178.250.2.74 .. 178.250.2.76} u ''@
    ''{178.250.2.78 .. 178.250.2.97} u {178.250.2.99 .. 178.250.2.101} u ''@
    ''{178.250.2.103 .. 184.168.47.224} u {184.168.47.226 .. 188.65.74.69} u ''@
    ''{188.65.74.71 .. 192.168.254.255} u {192.169.0.0 .. 194.97.151.142} u ''@
    ''{194.97.151.144 .. 194.97.153.230} u {194.97.153.232 .. 194.126.239.33} u ''@
    ''{194.126.239.35 .. 195.20.250.230} u {195.20.250.232 .. 206.191.168.169} u ''@
    ''{206.191.168.171 .. 212.45.104.68} u {212.45.104.70 .. 212.227.67.36} u ''@
    ''{212.227.67.38 .. 213.9.42.247} u {213.9.42.249 .. 213.203.221.31} u ''@
    ''{213.203.221.33 .. 213.203.221.42} u {213.203.221.44 .. 216.38.172.130} u ''@
    ''{216.38.172.132 .. 217.72.250.65} u {217.72.250.67 .. 217.72.250.83} u ''@
    ''{217.72.250.85 .. 217.72.250.88} u {217.72.250.90 .. 255.255.255.255}'')],
  [(''192.168.255.0'', ''172.16.2.0''),
   (''192.168.255.0'', ''172.16.2.16''),
   (''172.16.2.0'', ''192.168.255.0''),
   (''172.16.2.0'', ''172.16.2.0''),
   (''172.16.2.0'', ''172.16.2.16''),
   (''172.16.2.0'', ''0.0.0.0''),
   (''172.16.2.16'', ''192.168.255.0'')])" by eval (*the string @ takes quite some time*)

lemma "access_matrix_pretty_ipv4 parts_connection_http
    (preprocess unfold_ruleset_FORWARD upper_closure ipassmt company_fw_FORWARD_default_policy company_fw) =
 ([(''46.4.115.113'',
    ''46.4.115.113 u {46.20.32.74 .. 46.20.32.75} u 54.68.106.202 u 62.141.33.131 u 63.245.217.112 u 74.119.117.71 u 80.190.166.25 u 80.237.184.24 u 80.252.91.41 u 82.196.187.209 u 82.199.80.141 u 83.133.189.139 u 83.169.54.252 u 83.169.59.64 u 85.25.248.94 u 85.90.254.45 u 85.195.127.21 u 88.198.208.110 u 91.215.101.185 u 93.184.220.20 u 93.184.221.133 u 94.198.59.132 u 94.198.59.134 u 95.131.121.65 u 95.131.121.199 u 95.172.69.42 u 144.76.67.119 u 151.80.102.139 u 176.9.103.51 u 178.63.153.114 u 178.250.0.101 u 178.250.2.73 u 178.250.2.77 u 178.250.2.98 u 178.250.2.102 u 184.168.47.225 u 188.65.74.70 u 194.97.151.143 u 194.97.153.231 u 194.126.239.34 u 195.20.250.231 u 206.191.168.170 u 212.45.104.69 u 212.227.67.37 u 213.9.42.248 u 213.203.221.32 u 213.203.221.43 u 216.38.172.131 u 217.72.250.66 u 217.72.250.84 u 217.72.250.89''),
   (''192.168.255.0'',
    ''{192.168.255.0 .. 192.168.255.255}''),
   (''172.16.2.0'', ''{172.16.2.0 .. 172.16.2.255}''),
   (''0.0.0.0'',
    ''{0.0.0.0 .. 46.4.115.112} u {46.4.115.114 .. 46.20.32.73} u {46.20.32.76 .. 54.68.106.201} u {54.68.106.203 .. 62.141.33.130} u {62.141.33.132 .. 63.245.217.111} u {63.245.217.113 .. 74.119.117.70} u {74.119.117.72 .. 80.190.166.24} u {80.190.166.26 .. 80.237.184.23} u {80.237.184.25 .. 80.252.91.40} u {80.252.91.42 .. 82.196.187.208} u {82.196.187.210 .. 82.199.80.140} u {82.199.80.142 .. 83.133.189.138} u {83.133.189.140 .. 83.169.54.251} u {83.169.54.253 .. 83.169.59.63} u {83.169.59.65 .. 85.25.248.93} u {85.25.248.95 .. 85.90.254.44} u {85.90.254.46 .. 85.195.127.20} u {85.195.127.22 .. 88.198.208.109} u {88.198.208.111 .. 91.215.101.184} u {91.215.101.186 .. 93.184.220.19} u {93.184.220.21 .. 93.184.221.132} u {93.184.221.134 .. 94.198.59.131} u 94.198.59.133 u {94.198.59.135 .. 95.131.121.64} u {95.131.121.66 .. 95.131.121.198} u {95.131.121.200 .. 95.172.69.41} u {95.172.69.43 .. 144.76.67.118} u {144.76.67.120 .. 151.80.102.138} u {151.80.102.140 .. 172.16.1.255} u {172.16.3.0 .. 176.9.103.50} u {176.9.103.52 .. 178.63.153.113} u {178.63.153.115 .. 178.250.0.100} u {178.250.0.102 .. 178.250.2.72} u {178.250.2.74 .. 178.250.2.76} u {178.250.2.78 .. 178.250.2.97} u {178.250.2.99 .. 178.250.2.101} u {178.250.2.103 .. 184.168.47.224} u {184.168.47.226 .. 188.65.74.69} u {188.65.74.71 .. 192.168.254.255} u {192.169.0.0 .. 194.97.151.142} u {194.97.151.144 .. 194.97.153.230} u {194.97.153.232 .. 194.126.239.33} u {194.126.239.35 .. 195.20.250.230} u {195.20.250.232 .. 206.191.168.169} u {206.191.168.171 .. 212.45.104.68} u {212.45.104.70 .. 212.227.67.36} u {212.227.67.38 .. 213.9.42.247} u {213.9.42.249 .. 213.203.221.31} u {213.203.221.33 .. 213.203.221.42} u {213.203.221.44 .. 216.38.172.130} u {216.38.172.132 .. 217.72.250.65} u {217.72.250.67 .. 217.72.250.83} u {217.72.250.85 .. 217.72.250.88} u {217.72.250.90 .. 255.255.255.255}'')],
  [(''192.168.255.0'', ''172.16.2.0''),
   (''172.16.2.0'', ''192.168.255.0''),
   (''172.16.2.0'', ''172.16.2.0''),
   (''172.16.2.0'', ''0.0.0.0'')])" by eval

end
