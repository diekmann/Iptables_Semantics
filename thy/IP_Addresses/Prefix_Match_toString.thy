theory Prefix_Match_toString
imports IP_Address_toString Prefix_Match
begin

definition prefix_match_32_toString :: "32 prefix_match \<Rightarrow> string" where
  "prefix_match_32_toString pfx = (case pfx of PrefixMatch p l \<Rightarrow> ipv4addr_toString p @ (if l \<noteq> 32 then ''/'' @ string_of_nat l else []))"
definition prefix_match_128_toString :: "128 prefix_match \<Rightarrow> string" where
  "prefix_match_128_toString pfx = (case pfx of PrefixMatch p l \<Rightarrow> ipv6addr_toString p @ (if l \<noteq> 128 then ''/'' @ string_of_nat l else []))"

end