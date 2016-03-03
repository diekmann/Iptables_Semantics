theory IpRoute_Parser
imports Main "../Primitive_Matchers/IpAddresses" "../Routing/Routing"
keywords "parse_ip_route" :: thy_decl
begin

definition "empty_rr_hlp pm = routing_rule.make pm (Port '''') None default_metric"
lemma empty_rr_hlp_alt: "empty_rr_hlp pm = \<lparr> routing_match = pm, output_iface = Port '''', next_hop = None, metric = 0 \<rparr>"
unfolding empty_rr_hlp_def routing_rule.defs default_metric_def ..
definition "update_nh h pk = next_hop_update (const $ Some h) (pk::routing_rule)" 

(* Hide all the ugly ml in a file with the right extension *)
ML_file "IpRoute_Parser.ml"
                  
ML\<open>
  Outer_Syntax.local_theory @{command_keyword parse_ip_route}
  "Load a file generated by ip route and make the routing table definition available as isabelle term"
  (Parse.binding --| @{keyword "="} -- Parse.string >> register_ip_route)
\<close>

parse_ip_route "rtbl_parser_test1" = "ip-route-ex"  value rtbl_parser_test1


end