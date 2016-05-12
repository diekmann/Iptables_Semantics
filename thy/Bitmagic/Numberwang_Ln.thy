theory Numberwang_Ln
imports PrefixMatch IPAddr
begin

(*TODO: move to IpAddresses or somewhere*)
lemma ip_cidr_intersect: " \<not> ipset_from_cidr b2 m2 \<subseteq> ipset_from_cidr b1 m1 \<Longrightarrow>
       \<not> ipset_from_cidr b1 m1 \<subseteq> ipset_from_cidr b2 m2 \<Longrightarrow>
       ipset_from_cidr b1 m1 \<inter> ipset_from_cidr b2 m2 = {}"
apply(simp add: ipv4set_from_cidr_eq_ip_cidr_set)
using ip_cidr_set_notsubset_empty_inter by blast


(*
lemma help1: "word_of_int (uint a mod 256) = a mod (256::ipv4addr)"
by(simp add: word_mod_def)
lemma help2: "nat_of_ipv4addr ((ip::ipv4addr) AND mask 8) = (nat_of_ipv4addr ip) mod 256"
  apply(simp add: nat_of_ipv4addr_def)
  apply(simp add: and_mask_mod_2p)
  apply(simp add: help1)
  apply(simp add: unat_mod)
  done
lemma help3: "(nat_of_ipv4addr ip mod 256) = (nat_of_ipv4addr (ip mod 256))"
  by(simp add: nat_of_ipv4addr_def unat_mod)

lemma ip_shiftr_div_consts: "(ip::ipv4addr) >> 24 = ip div (2^24)"
      "(ip::ipv4addr) >> 16 = ip div (2^16)"
      "(ip::ipv4addr) >> 8 = ip div (2^8)"
by(subst Word.word_uint_eq_iff, simp add: shiftr_div_2n uint_div)+
*)






end
