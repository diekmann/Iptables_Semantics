section\<open>Routing and IP Assignments\<close>
theory Routing_IpAssmt
imports Ipassmt
        "../../Routing/Routing_Table"
begin
context
begin

subsection\<open>Routing IP Assignment\<close>
text\<open>Up to now, the definitions were all still on word intervals because those are much more convenient to work with.\<close>

definition "routing_ipassmt rt = (map (apfst Iface \<circ> apsnd cidr_split) (routing_ipassmt_wi rt))"

private lemma ipcidr_union_cidr_split[simp]: "ipcidr_union_set (set (cidr_split x)) = wordinterval_to_set x" 
  apply(subst cidr_split_prefix[symmetric])
  apply(fact ipcidr_union_set_uncurry)
done

lemma "valid_prefixes (rt::('i::len) prefix_routing) \<Longrightarrow> ipassmt_sanity_disjoint (map_of (routing_ipassmt rt))"
unfolding ipassmt_sanity_disjoint_def routing_ipassmt_def comp_def
  apply(clarsimp)
  apply(drule map_of_SomeD)+
  apply(clarsimp split: iface.splits)
using routing_ipassmt_wi_disjoint[where 'i = 'i] by meson

(* TODO: move all of these*)
subsection\<open>IP Assignment difference\<close>
text\<open>Compare two ipassmts. Returns a list of tuples
  First entry of the tuple: things which are in the left ipassmt but not in the right.
  Second entry of the tupls: things which are in the right ipassmt but not in the left.\<close>
definition ipassmt_diff
  :: "(iface \<times> ('i::len word \<times> nat) list) list \<Rightarrow> (iface \<times> ('i::len word \<times> nat) list) list
      \<Rightarrow> (iface \<times> ('i word \<times> nat) list \<times> ('i word \<times> nat) list) list"
where
"ipassmt_diff a b \<equiv> let
    t = \<lambda>s. (case s of None \<Rightarrow> Empty_WordInterval
                     | Some s \<Rightarrow> wordinterval_Union (map ipcidr_tuple_to_wordinterval s));
    k = \<lambda>x y d. cidr_split (wordinterval_setminus (t (map_of x d)) (t (map_of y d)))
  in
    [(d, (k a b d, k b a d)). d \<leftarrow> remdups (map fst (a @ b))]"


text\<open>If an interface is defined in both ipassignments and there is no difference
     then the two ipassignements describe the same IP range for this interface.\<close>
lemma ipassmt_diff_ifce_equal: "(ifce, [], []) \<in> set (ipassmt_diff ipassmt1 ipassmt2)  \<Longrightarrow>
       ifce \<in> dom (map_of ipassmt1) \<Longrightarrow> ifce \<in> dom (map_of ipassmt2) \<Longrightarrow>
         ipcidr_union_set (set (the ((map_of ipassmt1) ifce))) =
         ipcidr_union_set (set (the ((map_of ipassmt2) ifce)))"
  proof -
  have cidr_empty: "[] = cidr_split r \<Longrightarrow> wordinterval_to_set r = {}" for r :: "'a wordinterval"
    apply(subst cidr_split_prefix[symmetric])
    by(simp)
  show "(ifce, [], []) \<in> set (ipassmt_diff ipassmt1 ipassmt2)  \<Longrightarrow>
       ifce \<in> dom (map_of ipassmt1) \<Longrightarrow> ifce \<in> dom (map_of ipassmt2) \<Longrightarrow>
         ipcidr_union_set (set (the ((map_of ipassmt1) ifce))) =
         ipcidr_union_set (set (the ((map_of ipassmt2) ifce)))"
  apply(simp add: ipassmt_diff_def Let_def ipcidr_union_set_uncurry)
  apply(simp add: Set.image_iff)
  apply(elim conjE)
  apply(drule cidr_empty)+
  apply(simp )
  apply(simp add: domIff)
  apply(elim exE)
  apply(simp add: wordinterval_Union wordinterval_to_set_ipcidr_tuple_to_wordinterval_uncurry)
  done
qed
end

text\<open>Explanation for interface a: 
        Left ipassmt: The IP range 4/30 contains the addresses 4,5,6,7
        Diff: right ipassmt contains 6/32, so 4,5,7 is only in the left ipassmt.
        IP addresses 4,5 correspond to subnet 4/30.\<close>
lemma "ipassmt_diff (ipassmt_generic_ipv4 @ [(Iface ''a'', [(4,30)])])
                     (ipassmt_generic_ipv4 @ [(Iface ''a'', [(6,32), (0,30)]), (Iface ''b'', [(42,32)])]) =
  [(Iface ''lo'', [], []),
   (Iface ''a'', [(4::32 word, 31::nat),
                  (7::32 word, 32::nat)],
                 [(0::32 word, 30::nat)]
   ),
   (Iface ''b'', [], [(42, 32)])]" by eval

end
