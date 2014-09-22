theory Numberwang_Ln
imports NumberWangCebewee
begin

lemma ipv4range_bitmask_intersect: " \<not> ipv4range_set_from_bitmask b2 m2 \<subseteq> ipv4range_set_from_bitmask b1 m1 \<Longrightarrow>
       \<not> ipv4range_set_from_bitmask b1 m1 \<subseteq> ipv4range_set_from_bitmask b2 m2 \<Longrightarrow>
       ipv4range_set_from_bitmask b1 m1 \<inter> ipv4range_set_from_bitmask b2 m2 = {}"
apply(simp add: ipv4range_set_from_bitmask_eq_ip_set)
using ip_set_notsubset_empty_inter 
by presburger



end
