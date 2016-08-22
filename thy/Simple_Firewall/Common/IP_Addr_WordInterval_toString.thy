section\<open>Helper: Pretty Printing Word Intervals which correspond to IP address Ranges\<close>
theory IP_Addr_WordInterval_toString
imports "../../IP_Addresses/IP_Address_toString"
begin

(*The "u" stands for union. I guess you may want to customize this pretty printing syntax :D*)

fun ipv4addr_wordinterval_toString :: "32 wordinterval \<Rightarrow> string" where
  "ipv4addr_wordinterval_toString (WordInterval s e) =
    (if s = e then ipv4addr_toString s else ''{''@ipv4addr_toString s@'' .. ''@ipv4addr_toString e@''}'')" |
  "ipv4addr_wordinterval_toString (RangeUnion a b) =
    ipv4addr_wordinterval_toString a @ '' u ''@ipv4addr_wordinterval_toString b"

fun ipv6addr_wordinterval_toString :: "128 wordinterval \<Rightarrow> string" where
  "ipv6addr_wordinterval_toString (WordInterval s e) =
    (if s = e then ipv6addr_toString s else ''{''@ipv6addr_toString s@'' .. ''@ipv6addr_toString e@''}'')" |
  "ipv6addr_wordinterval_toString (RangeUnion a b) =
    ipv6addr_wordinterval_toString a @ '' u ''@ipv6addr_wordinterval_toString b"

end