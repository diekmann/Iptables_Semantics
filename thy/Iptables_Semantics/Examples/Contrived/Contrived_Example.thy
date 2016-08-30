section\<open>Contrived Example\<close>
theory Contrived_Example
imports 
  "../../Primitive_Matchers/Parser"
begin

(*
  internal network: 131.159.21.0/24
  DMZ: 131.159.15.240/28
  DMZ must not connect to internal
*)

parse_iptables_save example_fw="iptables-save"

thm example_fw_def
thm example_fw_FORWARD_default_policy_def


lemma "map common_primitive_rule_toString
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD example_fw_FORWARD_default_policy
                      (map_of_string_ipv4 example_fw)))) =
[''-i lo -j ACCEPT'',
 ''! -i lo -s 127.0.0.0/8 -j DROP'',
 ''-i inteneral -s 131.159.21.0/24 -j ACCEPT'',
 ''-d 131.159.21.0/24 -s 131.159.15.240/28 -j DROP'',
 ''-p tcp -d 131.159.15.240/28 -j ACCEPT'',
 ''-i dmz -p tcp -s 131.159.15.240/28 -j ACCEPT'',
 '' -j DROP'']" by eval


lemma "map simple_rule_ipv4_toString
              (to_simple_firewall (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD example_fw_FORWARD_default_policy
                      (map_of_string_ipv4 example_fw))))))) =
[''ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0 in: lo   '',
  ''ACCEPT     all  --  131.159.21.0/24            0.0.0.0/0 in: inteneral   '',
  ''DROP     all  --  131.159.15.240/28            131.159.21.0/24    '',
  ''ACCEPT     tcp  --  0.0.0.0/0            131.159.15.240/28    '',
  ''ACCEPT     tcp  --  131.159.15.240/28            0.0.0.0/0 in: dmz   '',
  ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval


lemma "map simple_rule_ipv4_toString
              (to_simple_firewall_without_interfaces ipassmt_generic_ipv4 None (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD example_fw_FORWARD_default_policy
                      (map_of_string_ipv4 example_fw))))))) =
[''ACCEPT     all  --  127.0.0.0/8            0.0.0.0/0    '',
  ''ACCEPT     all  --  131.159.21.0/24            0.0.0.0/0    '',
  ''DROP     all  --  131.159.15.240/28            131.159.21.0/24    '',
  ''ACCEPT     tcp  --  0.0.0.0/0            131.159.15.240/28    '',
  ''ACCEPT     tcp  --  131.159.15.240/28            0.0.0.0/0    '',
  ''DROP     all  --  0.0.0.0/0            0.0.0.0/0    '']" by eval



lemma "access_matrix_pretty_ipv4 parts_connection_ssh
              (to_simple_firewall_without_interfaces ipassmt_generic_ipv4 None (upper_closure
                (optimize_matches abstract_for_simple_firewall
                  (upper_closure (packet_assume_new
                    (unfold_ruleset_FORWARD example_fw_FORWARD_default_policy
                      (map_of_string_ipv4 example_fw))))))) =
([(''131.159.21.0'', ''{131.159.21.0 .. 131.159.21.255}''),
   (''131.159.15.240'', ''{131.159.15.240 .. 131.159.15.255}''),
   (''127.0.0.0'', ''{127.0.0.0 .. 127.255.255.255}''),
   (''0.0.0.0'', ''{0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 131.159.15.239} u {131.159.16.0 .. 131.159.20.255} u {131.159.22.0 .. 255.255.255.255}'')],

  [(''131.159.21.0'', ''131.159.21.0''), (''131.159.21.0'', ''131.159.15.240''),
   (''131.159.21.0'', ''127.0.0.0''), (''131.159.21.0'', ''0.0.0.0''),
   (''131.159.15.240'', ''131.159.15.240''), (''131.159.15.240'', ''127.0.0.0''),
   (''131.159.15.240'', ''0.0.0.0''), (''127.0.0.0'', ''131.159.21.0''), (''127.0.0.0'', ''131.159.15.240''),
   (''127.0.0.0'', ''127.0.0.0''), (''127.0.0.0'', ''0.0.0.0''), (''0.0.0.0'', ''131.159.15.240'')])"
by eval

(*
a |-> {131.159.21.0 .. 131.159.21.255}
b |-> {131.159.15.240 .. 131.159.15.255}
c |-> {127.0.0.0 .. 127.255.255.255}
d |-> {0.0.0.0 .. 126.255.255.255} \<union> {128.0.0.0 .. 131.159.15.239} \<union> {131.159.16.0 .. 131.159.20.255} \<union> {131.159.22.0 .. 255.255.255.255}

(a,a)
(a,b)
(a,c)
(a,d)
(b,b)
(b,c)
(b,d)
(c,a)
(c,b)
(c,c)
(c,d)
(d,b)

*)

end
