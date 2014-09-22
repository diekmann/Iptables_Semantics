(*<*)
theory iptables_Ln_tuned_parsed
imports "../../Firewall_Common" "../../Primitive_Matchers/IPSpace_Syntax"
begin
definition "firewall_chains = [''DOS_PROTECT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Extra (''Prot icmp''))) (Match (Extra (''icmptype 8'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04 limit: avg 1/sec burst 5'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x04'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02 limit: avg 10000/sec burst 100'')))))) (Return),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp flags:0x17/0x02'')))))) (Drop)],
''INPUT'' \<mapsto> [Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Call (''DOS_PROTECT'')),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Call (''DOS_PROTECT'')),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (Match (Extra (''state RELATED,ESTABLISHED'')))))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''tcp dpt:22'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtTCP))) (Match (Extra (''multiport dports 21,873,5005,5006,80,548,111,2049,892'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtUDP))) (Match (Extra (''multiport dports 123,111,2049,892,5353'')))))) (Drop),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((192,168,0,0)) (16)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Accept),
Rule (MatchAnd (Match (Src (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Dst (Ip4AddrNetmask ((0,0,0,0)) (0)))) (MatchAnd (Match (Prot (ProtAll))) (MatchAny)))) (Drop),
Rule (MatchAny) (Accept)],
''FORWARD'' \<mapsto> [Rule (MatchAny) (Accept)],
''OUTPUT'' \<mapsto> [Rule (MatchAny) (Accept)]]"
end
(*>*)
