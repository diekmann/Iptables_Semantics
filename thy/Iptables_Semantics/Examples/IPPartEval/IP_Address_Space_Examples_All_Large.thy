theory IP_Address_Space_Examples_All_Large
imports 
  "IP_Address_Space_Examples_All_Small"
begin


  definition "everything_but_my_ips = all_but_those_ips [
    (ipv4addr_of_dotdecimal (131,159,14,0), 23),
    (ipv4addr_of_dotdecimal (131,159,20,0), 23),
    (ipv4addr_of_dotdecimal (192,168,212,0), 23),
    (ipv4addr_of_dotdecimal (188,95,233,0), 24),
    (ipv4addr_of_dotdecimal (188,95,232,192), 27),
    (ipv4addr_of_dotdecimal (188,95,234,0), 23),
    (ipv4addr_of_dotdecimal (192,48,107,0), 24),
    (ipv4addr_of_dotdecimal (188,95,236,0), 22),
    (ipv4addr_of_dotdecimal (185,86,232,0), 22)
    ]"
  
  
  definition "ipassmt = [(Iface ''eth0'', [(ipv4addr_of_dotdecimal (192,168,213,4), 24)]),
  (Iface ''eth1.96'', [(ipv4addr_of_dotdecimal (131,159,14,3), 25)]),
  (Iface ''eth1.108'', [(ipv4addr_of_dotdecimal (131,159,14,129), 26)]),
  (Iface ''eth1.109'', [(ipv4addr_of_dotdecimal (131,159,20,11), 24)]),
  (Iface ''eth1.110'', everything_but_my_ips), (*INET*)
  (Iface ''eth1.116'', [(ipv4addr_of_dotdecimal (131,159,15,131), 26)]),
  (Iface ''eth1.152'', [(ipv4addr_of_dotdecimal (131,159,15,252), 28)]),
  (Iface ''eth1.171'', [(ipv4addr_of_dotdecimal (131,159,15,2), 26)]),
  (Iface ''eth1.173'', [(ipv4addr_of_dotdecimal (131,159,21,252), 24)]),
  (Iface ''eth1.1010'', [(ipv4addr_of_dotdecimal (131,159,15,227), 28)]),
  (Iface ''eth1.1011'', [(ipv4addr_of_dotdecimal (131,159,14,194), 27)]),
  (Iface ''eth1.1012'', [(ipv4addr_of_dotdecimal (131,159,14,238), 28)]),
  (Iface ''eth1.1014'', [(ipv4addr_of_dotdecimal (131,159,15,217), 27)]),
  (Iface ''eth1.1016'', [(ipv4addr_of_dotdecimal (131,159,15,66), 26)]),
  (Iface ''eth1.1017'', [(ipv4addr_of_dotdecimal (131,159,14,242), 28)]),
  (Iface ''eth1.1111'', [(ipv4addr_of_dotdecimal (192,168,212,4), 24)]),
  (Iface ''eth1.97'', [(ipv4addr_of_dotdecimal (188,95,233,2), 24)]),
  (Iface ''eth1.1019'', [(ipv4addr_of_dotdecimal (188,95,234,2), 23)]),
  (Iface ''eth1.1020'', [(ipv4addr_of_dotdecimal (192,48,107,2), 24)]),
  (Iface ''eth1.1023'', [(ipv4addr_of_dotdecimal (188,95,236,2), 22)]),
  (Iface ''eth1.1025'', [(ipv4addr_of_dotdecimal (185,86,232,2), 22)]),
  (Iface ''eth1.1024'', everything_but_my_ips) (*transfer net*)]"
  
  lemma "ipassmt_sanity_nowildcards (map_of ipassmt)" by eval

  
  text\<open>We check for all interfaces, except for @{term "Iface ''eth0''"}, which does not need spoofing protection.\<close>
  definition "interfaces = tl (map (iface_sel \<circ> fst) ipassmt)"
  
  lemma "interfaces = 
    [''eth1.96'', ''eth1.108'', ''eth1.109'', ''eth1.110'',
     ''eth1.116'', ''eth1.152'', ''eth1.171'', ''eth1.173'', ''eth1.1010'',
     ''eth1.1011'', ''eth1.1012'', ''eth1.1014'', ''eth1.1016'', ''eth1.1017'',
     ''eth1.1111'', ''eth1.97'', ''eth1.1019'', ''eth1.1020'', ''eth1.1023'',
     ''eth1.1025'', ''eth1.1024'']" by eval



value[code] "debug_ipassmt_ipv4 ipassmt []"

definition netbios where "netbios = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=UDP,
                               pc_sport=10000, pc_dport=137\<rparr>"
definition kerberos_adm_tcp where "kerberos_adm_tcp = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=749\<rparr>"
definition kerberos_adm_udp where "kerberos_adm_udp = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=UDP,
                               pc_sport=10000, pc_dport=749\<rparr>"

definition ldap_tcp where "ldap_tcp = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=389\<rparr>"
definition ldap_udp where "ldap_udp = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=UDP,
                               pc_sport=10000, pc_dport=389\<rparr>"
definition ldaps_tcp where "ldaps_tcp = \<lparr>pc_iiface=''1'', pc_oiface=''1'', pc_proto=TCP,
                               pc_sport=10000, pc_dport=636\<rparr>"

context
begin


  private parse_iptables_save net_fw = "TUM_Net" "iptables-save-2015-05-15_15-23-41"

  value[code] "bench upper_closure FWD ipassmt net_fw_FORWARD_default_policy net_fw"
  value[code] "view upper_closure FWD ipassmt net_fw_FORWARD_default_policy net_fw"

  value[code] "bench lower_closure FWD ipassmt net_fw_FORWARD_default_policy net_fw"
  value[code] "view lower_closure FWD ipassmt net_fw_FORWARD_default_policy net_fw"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
          (build_ip_partition netbios fw)"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
     (access_matrix_pretty_ipv4 parts_connection_ssh fw)"
  
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
     (access_matrix_pretty_ipv4 parts_connection_http fw)"
  

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
     (access_matrix_pretty_ipv4 netbios fw)"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
    (access_matrix_pretty_ipv4 kerberos_adm_tcp fw)"
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
    (access_matrix_pretty_ipv4 kerberos_adm_udp fw)"


  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
    (access_matrix_pretty_ipv4 ldap_tcp fw)"
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
    (access_matrix_pretty_ipv4 ldap_udp fw)"


  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw_FORWARD_default_policy net_fw in
    (access_matrix_pretty_ipv4 ldaps_tcp fw)"
end


context
begin
 private parse_iptables_save net_fw2 = "TUM_Net" "iptables-save-2015-09-03_15-56-50"

  value[code] "bench upper_closure FWD ipassmt net_fw2_FORWARD_default_policy net_fw2"
  value[code] "view upper_closure FWD ipassmt net_fw2_FORWARD_default_policy net_fw2"

  value[code] "bench lower_closure FWD ipassmt net_fw2_FORWARD_default_policy net_fw2"
  value[code] "view lower_closure FWD ipassmt net_fw2_FORWARD_default_policy net_fw2"  


  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2_FORWARD_default_policy net_fw2 in
     (access_matrix_pretty_ipv4 netbios fw)"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2_FORWARD_default_policy net_fw2 in
    (access_matrix_pretty_ipv4 kerberos_adm_tcp fw)"
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2_FORWARD_default_policy net_fw2 in
    (access_matrix_pretty_ipv4 kerberos_adm_udp fw)"
end

context
begin
 private parse_iptables_save net_fw2013 = "TUM_Net" "iptables_20.10.2013"

  value[code] "bench upper_closure FWD ipassmt net_fw2013_FORWARD_default_policy net_fw2013"
  value[code] "view upper_closure FWD ipassmt net_fw2013_FORWARD_default_policy net_fw2013"

  value[code] "bench lower_closure FWD ipassmt net_fw2013_FORWARD_default_policy net_fw2013"
  value[code] "view lower_closure FWD ipassmt net_fw2013_FORWARD_default_policy net_fw2013"  

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2013_FORWARD_default_policy net_fw2013 in
     (access_matrix_pretty_ipv4 netbios fw)"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2013_FORWARD_default_policy net_fw2013 in
    (access_matrix_pretty_ipv4 kerberos_adm_tcp fw)"
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2013_FORWARD_default_policy net_fw2013 in
    (access_matrix_pretty_ipv4 kerberos_adm_udp fw)"
end



context
begin
 private parse_iptables_save net_fw2014 = "TUM_Net" "iptables_25.07.2014"

  value[code] "bench upper_closure FWD ipassmt net_fw2014_FORWARD_default_policy net_fw2014"
  value[code] "view upper_closure FWD ipassmt net_fw2014_FORWARD_default_policy net_fw2014"

  value[code] "bench lower_closure FWD ipassmt net_fw2014_FORWARD_default_policy net_fw2014"
  value[code] "view lower_closure FWD ipassmt net_fw2014_FORWARD_default_policy net_fw2014"  

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2014_FORWARD_default_policy net_fw2014 in
     (access_matrix_pretty_ipv4 netbios fw)"

  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2014_FORWARD_default_policy net_fw2014 in
    (access_matrix_pretty_ipv4 kerberos_adm_tcp fw)"
  value[code] "let fw = preprocess (get_unfold FWD) upper_closure ipassmt net_fw2014_FORWARD_default_policy net_fw2014 in
    (access_matrix_pretty_ipv4 kerberos_adm_udp fw)"
end


end
