theory IpAddresses
imports "../Bitmagic/IPv4Addr"
begin


section{*IPv4 Addresses*}

(*src dst ipv4*)
datatype ipt_ipv4range = Ip4Addr "nat \<times> nat \<times> nat \<times> nat"
                      | Ip4AddrNetmask "nat \<times> nat \<times> nat \<times> nat" nat -- "addr/xx"



fun ipv4s_to_set :: "ipt_ipv4range \<Rightarrow> ipv4addr set" where
  "ipv4s_to_set (Ip4AddrNetmask base m) = ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal base) m" |
  "ipv4s_to_set (Ip4Addr ip) = { ipv4addr_of_dotdecimal ip }"

text{*@{term ipv4s_to_set} cannot represent an empty set.*}
lemma ipv4s_to_set_nonempty: "ipv4s_to_set ip \<noteq> {}"
  apply(cases ip)
   apply(simp)
  apply(simp add: ipv4range_set_from_bitmask_alt)
  apply(simp add: bitmagic_zeroLast_leq_or1Last)
  done

text{*maybe this is necessary as code equation?*}
lemma element_ipv4s_to_set[code_unfold]: "addr \<in> ipv4s_to_set X = (
  case X of (Ip4AddrNetmask pre len) \<Rightarrow> ((ipv4addr_of_dotdecimal pre) AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> (ipv4addr_of_dotdecimal pre) OR (mask (32 - len))
  | Ip4Addr ip \<Rightarrow> (addr = (ipv4addr_of_dotdecimal ip)) )"
apply(cases X)
 apply(simp)
apply(simp add: ipv4range_set_from_bitmask_alt)
done


--"Misc"
(*we dont't have an empty ip space, but a space which only contains the 0 address. We will use the option type to denote the empty space in some functions.*)
lemma "ipv4range_set_from_bitmask (ipv4addr_of_dotdecimal (0, 0, 0, 0)) 33 = {0}"
apply(simp add: ipv4addr_of_dotdecimal.simps ipv4addr_of_nat_def)
apply(simp add: ipv4range_set_from_bitmask_def)
apply(simp add: ipv4range_set_from_netmask_def)
done



(*We need a separate ipv4addr syntax thy*)
  fun ipv4cidr_to_intervall :: "(ipv4addr \<times> nat) \<Rightarrow> (ipv4addr \<times> ipv4addr)" where
    "ipv4cidr_to_intervall (pre, len) = (
      let netmask = (mask len) << (32 - len);
          network_prefix = (pre AND netmask)
      in (network_prefix, network_prefix OR (NOT netmask))
     )"
  lemma ipv4cidr_to_intervall: "ipv4cidr_to_intervall (base, len) = (s,e) \<Longrightarrow> ipv4range_set_from_bitmask base len = {s .. e}"
    apply(simp add: Let_def)
    apply(subst ipv4range_set_from_bitmask_alt)
    apply(subst(asm) NOT_mask_len32)
    by (metis NOT_mask_len32 ipv4range_set_from_bitmask_alt ipv4range_set_from_bitmask_alt1 ipv4range_set_from_netmask_def)
  




  fun ipt_ipv4range_to_intervall :: "ipt_ipv4range \<Rightarrow> (ipv4addr \<times> ipv4addr)" where
    "ipt_ipv4range_to_intervall (Ip4Addr addr) = (ipv4addr_of_dotdecimal addr, ipv4addr_of_dotdecimal addr)" |
    "ipt_ipv4range_to_intervall (Ip4AddrNetmask pre len) = ipv4cidr_to_intervall ((ipv4addr_of_dotdecimal pre), len)" 
  
  lemma ipt_ipv4range_to_intervall: "ipt_ipv4range_to_intervall ip = (s,e) \<Longrightarrow> {s .. e} = ipv4s_to_set ip"
    apply(cases ip)
    apply(auto simp add: ipv4cidr_to_intervall)
    done

end
