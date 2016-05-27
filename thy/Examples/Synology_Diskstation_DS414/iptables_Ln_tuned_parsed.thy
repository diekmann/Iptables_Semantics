theory iptables_Ln_tuned_parsed
imports "../../Primitive_Matchers/Code_Interface"
begin
definition "firewall_chains = [''DOS_PROTECT'' \<mapsto> [Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (action.Return),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (action.Drop)],
''INPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (Call (''DOS_PROTECT'')),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (Call (''DOS_PROTECT'')),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (ProtoAny))) (Match (Extra (''state RELATED,ESTABLISHED'')))))) (action.Accept),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''tcp dpt:22'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto TCP))) (Match (Extra (''multiport dports 21,873,5005,5006,80,548,111,2049,892'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (Proto UDP))) (Match (Extra (''multiport dports 123,111,2049,892,5353'')))))) (action.Drop),
Rule (MatchAnd (Match (Src (IpAddrNetmask (ipv4addr_of_dotdecimal (192,168,0,0)) (16)))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (action.Accept),
Rule (MatchAnd (Match (Src (IpAddrNetmask 0 0))) (MatchAnd (Match (Dst (IpAddrNetmask 0 0))) (MatchAnd (Match (Prot (ProtoAny))) (MatchAny)))) (action.Drop),
Rule (MatchAny) (action.Accept)],
''FORWARD'' \<mapsto> [Rule (MatchAny) (action.Accept)],
''OUTPUT'' \<mapsto> [Rule (MatchAny) (action.Accept)]]"
end
