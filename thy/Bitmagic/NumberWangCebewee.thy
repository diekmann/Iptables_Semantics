theory NumberWangCebewee
imports
  "./l4v/lib/WordLemmaBucket"
  IPAddr
  (*formerly: NumberWangCaesar*)
begin

(*contributed by Lars Noschinski*)

(*TODO: move this whole thing to IPAddr?*)

lemma and_not_mask_twice:
  "(w && ~~ mask n) && ~~ mask m = w && ~~ mask (max m n)"
apply (simp add: and_not_mask)
apply (case_tac "n<m")
 apply (simp_all add: shiftl_shiftr2 shiftl_shiftr1 not_less max_def
                      shiftr_shiftr shiftl_shiftl)
 apply (cut_tac and_mask_shiftr_comm
                [where w=w and m="size w" and n=m, simplified,symmetric])
 apply (simp add: word_size mask_def)
apply (cut_tac and_mask_shiftr_comm
               [where w=w and m="size w" and n=n, simplified,symmetric])
apply (simp add: word_size mask_def)
done


lemma X: "j \<in> ip_cidr_set i r \<Longrightarrow> ip_cidr_set j r = ip_cidr_set i r"
  by (auto simp: ip_cidr_set_def)

lemma Z:
  fixes i :: "('a :: len) word"
  assumes "r2 \<le> r1" "i && ~~ mask r2 = x && ~~ mask r2"
  shows "i && ~~ mask r1 = x && ~~ mask r1"
proof -
  have "i AND NOT mask r1 = (i && ~~ mask r2) && ~~ mask r1" (is "_ = ?w && _")
    using \<open>r2 \<le> r1\<close> by (simp add: and_not_mask_twice max_def)
  also have "?w = x && ~~ mask r2" by fact
  also have "\<dots> && ~~ mask r1 = x && ~~ mask r1"
    using \<open>r2 \<le> r1\<close> by (simp add: and_not_mask_twice max_def)
  finally show ?thesis .
qed

(*TODO: rename*)
lemma Y:
  fixes i :: "'i::len word"
  shows "r1 \<le> r2 \<Longrightarrow> ip_cidr_set i r2 \<subseteq> ip_cidr_set i r1"
  unfolding ip_cidr_set_def
  apply auto
  apply (rule Z[where ?r2.0="len_of TYPE('i) - r2"])
  apply auto
  done


lemma ip_cidr_set_intersect_subset_helper:
  fixes i1 r1 i2 r2
  assumes disj: "ip_cidr_set i1 r1 \<inter> ip_cidr_set i2 r2 \<noteq> {}" and  "r1 \<le> r2"
  shows "ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1"
  proof -
  from disj obtain j where "j \<in> ip_cidr_set i1 r1" "j \<in> ip_cidr_set i2 r2" by auto
  with `r1 \<le> r2` have "j \<in> ip_cidr_set j r1" "j \<in> ip_cidr_set j r1" using X Y by blast+

  show "ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1"
  proof
    fix i assume "i \<in> ip_cidr_set i2 r2"
    with \<open>j \<in> ip_cidr_set i2 r2\<close> have "i \<in> ip_cidr_set j r2" using X by auto
    also have "ip_cidr_set j r2 \<subseteq> ip_cidr_set j r1" using \<open>r1 \<le> r2\<close> Y by blast
    also have "\<dots> = ip_cidr_set i1 r1" using \<open>j \<in> ip_cidr_set i1 r1\<close> X by blast
    finally show "i \<in> ip_cidr_set i1 r1" .
  qed
qed

lemma ip_cidr_set_notsubset_empty_inter: "\<not> ip_cidr_set i1 r1 \<subseteq> ip_cidr_set i2 r2 \<Longrightarrow> \<not> ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1 \<Longrightarrow> ip_cidr_set i1 r1 \<inter> ip_cidr_set i2 r2 = {}"
  apply(cases "r1 \<le> r2")
  using ip_cidr_set_intersect_subset_helper apply blast
  apply(cases "r2 \<le> r1")
  using ip_cidr_set_intersect_subset_helper apply blast
  apply(simp)
  done


end
