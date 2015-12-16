theory RoutingRange
imports RoutingSet
begin

type_synonym ipv4range = "32 wordinterval"

fun range_destination :: "prefix_routing \<Rightarrow> ipv4range \<Rightarrow> (ipv4range \<times> port list) list" where
"range_destination [] rg = (if ipv4range_empty rg then [] else [(rg, [])])" |
"range_destination (r # rs) rg = (
  let rpm = range_prefix_match (routing_match r) rg in (let m = fst rpm in (let nm = snd rpm in (
    (if ipv4range_empty m  then [] else [ (m, routing_action r) ]) @ 
    (if ipv4range_empty nm then [] else range_destination rs nm)
))))"

lemma range_destination_eq: 
  "{ (ipv4range_to_set r, ports)|r ports. (r, ports) \<in> set (range_destination rtbl rg)} = ipset_destination rtbl (ipv4range_to_set rg)"
  apply(induction rtbl arbitrary: rg)
   apply(simp)
  apply(simp only: Let_def range_destination.simps ipset_destination.simps)
  apply(case_tac "fst (ipset_prefix_match (routing_match a) (ipv4range_to_set rg)) = {}")
   apply(case_tac[!] "snd (ipset_prefix_match (routing_match a) (ipv4range_to_set rg)) = {}")
     apply(simp_all only: refl if_True if_False range_prefix_match_sm[symmetric] range_prefix_match_snm[symmetric] ipv4range_empty_set_eq Un_empty_left Un_empty_right)
     apply(simp_all)[3]
  apply(simp only: set_append set_simps)
  apply blast
done

definition "rr_to_sr r \<equiv> set (map (\<lambda>(x,y). (ipv4range_to_set x, y)) r)"

lemma range_destination_eq2:
  "ipv4range_to_set rg = rS \<Longrightarrow>
   ipset_destination rtbl rS = rr_to_sr (range_destination rtbl rg)"
  apply(unfold rr_to_sr_def)
  apply(induction rtbl arbitrary: rg rS)
   apply(simp)
  apply(simp only: Let_def range_destination.simps ipset_destination.simps)
  apply(case_tac "fst (ipset_prefix_match (routing_match a) (ipv4range_to_set rg)) = {}")
   apply(case_tac[!] "snd (ipset_prefix_match (routing_match a) (ipv4range_to_set rg)) = {}")
     apply(simp_all only: refl if_True if_False range_prefix_match_sm[symmetric] range_prefix_match_snm[symmetric] ipv4range_empty_set_eq Un_empty_left Un_empty_right)
     apply(simp_all)[3]
  proof -
    case goal1
    let ?maf = "(\<lambda>(x, y). (ipv4range_to_set x, y))"
    have ne: "ipv4range_to_set (fst (range_prefix_match (routing_match a) rg)) \<noteq> {}"
             "ipv4range_to_set (snd (range_prefix_match (routing_match a) rg)) \<noteq> {}"
      using goal1(3) goal1(4) goal1(2) by simp_all
    have *: "snd (ipset_prefix_match (routing_match a) rS) = ipv4range_to_set (snd (range_prefix_match (routing_match a) rg))"
      using goal1(2) by simp
    have ***: "(fst (ipset_prefix_match (routing_match a) rS), routing_action a) =
      ?maf (fst (range_prefix_match (routing_match a) rg), routing_action a)" by(simp add: goal1(2))
    moreover
    have **: "ipset_destination rtbl (snd (ipset_prefix_match (routing_match a) rS)) =
      set (map ?maf (range_destination rtbl (snd (range_prefix_match (routing_match a) rg))))"
    using goal1(1)[OF *[symmetric]] by simp
    show ?case unfolding ** ***
     by(simp only: set_map set_append set_simps if_False image_Un ne image_empty image_insert)
  qed

definition "range_rel r = {(ip,port)|ip port rg. (rg,port) \<in> set r \<and> ip \<in> ipv4range_to_set rg}"
lemma in_range_rel: "in_rel (range_rel r) x y = (\<exists>rg. ipv4range_element x rg \<and> (rg,y) \<in> set r)"
  unfolding ipv4range_element_set_eq in_rel_def range_rel_def by auto
lemma range_rel_to_sr: "range_rel = ipset_rel \<circ> rr_to_sr"
  unfolding comp_def rr_to_sr_def
  unfolding fun_eq_iff
  unfolding range_rel_def ipset_rel_def
  by auto

lemma range_destination_correct:
  assumes v_pfx: "valid_prefixes rtbl"
  shows "(packet_routing_table_semantics rtbl packet = ports) \<longleftrightarrow> in_rel (range_rel (range_destination rtbl ipv4range_UNIV)) (dst_addr packet) ports"
  unfolding packet_routing_table_semantics_def ipset_destination_correct[OF v_pfx UNIV_I] ipv4range_UNIV_set_eq[symmetric] range_destination_eq[symmetric] range_rel_def ipset_rel_def
  by simp blast

fun map_of_ranges where
"map_of_ranges [] = (\<lambda>x. undefined)" |
"map_of_ranges ((a,b)#rs) = (\<lambda>x. if ipv4range_element x a then b else map_of_ranges rs x)"

(*lemma "(map_of_ranges r a = b) = in_rel (range_rel r) a b"
unfolding in_rel_def range_rel_def
apply(induction r)
prefer 2
apply(clarify)
apply(unfold map_of_ranges.simps(2))
apply(case_tac "\<not>ipv4range_element a aa")
apply(unfold ipv4range_element_set_eq)
apply auto[1]
apply clarsimp
apply(rule)+
apply simp
apply simp
proof -
  fix aa ba
  assume "(map_of_ranges r a = b) = (\<exists>rg. (rg, b) \<in> set r \<and> a \<in> ipv4range_to_set rg)"
  assume "a \<in> ipv4range_to_set aa"
  assume " \<exists>rg. (rg = aa \<and> b = ba \<or> (rg, b) \<in> set r) \<and> a \<in> ipv4range_to_set rg"
  show "ba = b"*)

lemma range_left_side_nonempty: "x \<in> set (map fst (range_destination rtbl rg)) \<Longrightarrow> \<not> ipv4range_empty x"
proof -
  case goal1
  have "\<exists>S. S = ipv4range_to_set rg" by simp then guess S ..
  note * = range_destination_eq2[OF this[symmetric], unfolded rr_to_sr_def]
  show ?case
    unfolding ipv4range_empty_set_eq 
    using ipset_left_side_nonempty[where rg = S] unfolding * 
    using goal1 unfolding set_map
    by force
qed

subsection{*Reduction*}

(*
definition "range_left_reduce \<equiv> list_left_reduce list_to_ipv4range"
lemmas range_left_reduce_set_eq = list_left_reduce_set_eq[OF list_to_ipv4range_set_eq rr_to_sr_def, 
                                    unfolded range_left_reduce_def[symmetric]]

lemma "range_rel r = range_rel (range_left_reduce r)"
  unfolding range_rel_to_sr
  unfolding comp_def
  unfolding range_left_reduce_set_eq
  using left_reduce_ipset_rel_stable .

definition "reduced_range_destination tbl r = range_left_reduce (range_destination tbl r)"
lemma reduced_range_destination_eq:
  assumes "ipv4range_to_set rg = rS"
  shows "reduced_ipset_destination rtbl rS = rr_to_sr (reduced_range_destination rtbl rg)"
  unfolding reduced_ipset_destination_def reduced_range_destination_def
  unfolding range_left_reduce_set_eq
  using arg_cong[OF range_destination_eq2[OF assms]]
  . (* goes by . and .. — weird *)

lemma reduced_range_destination_eq1: (* equality that was first proven. *)
  "{ (ipv4range_to_set r, ports)|r ports. (r, ports) \<in> set (reduced_range_destination rtbl rg)} = reduced_ipset_destination rtbl (ipv4range_to_set rg)"
  unfolding reduced_ipset_destination_def
  unfolding range_destination_eq[symmetric]
  unfolding reduced_range_destination_def
  using range_left_reduce_set_eq[unfolded rr_to_sr_def set_map, of "range_destination rtbl rg"]
  unfolding image_set_comprehension by simp
*)

end
