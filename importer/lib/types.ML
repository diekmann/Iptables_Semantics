datatype action = Accept | Drop | Log | Reject | Call of string | Return | Empty | Unknown
datatype 'a match_expr = Match of 'a | MatchNot of 'a match_expr | MatchAnd of 'a match_expr * 'a match_expr | MatchAny
datatype 'a rule = Rule of 'a match_expr * action

datatype ipt_ipv4range = Ip4Addr of int * int * int * int
                       | Ip4AddrNetmask of (int * int * int * int) * int

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP

datatype iptrule_match = Src of ipt_ipv4range | Dst of ipt_ipv4range | Prot of ipt_protocol | Extra of string
