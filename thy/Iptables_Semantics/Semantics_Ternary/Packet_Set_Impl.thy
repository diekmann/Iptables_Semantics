theory Packet_Set_Impl
imports Normalized_Matches Negation_Type_Matching "../Datatype_Selectors"
begin


section\<open>Util: listprod\<close>
    definition listprod :: "nat list \<Rightarrow> nat" where "listprod as \<equiv> foldr (op *) as 1"
    (*better: "'a::comm_semiring_1 list \<Rightarrow> 'a"*)
    lemma listprod_append[simp]: "listprod (as @ bs) =  listprod as * listprod bs"
     apply(induction as arbitrary: bs)
      apply(simp_all add: listprod_def)
     done
    lemma listprod_simps [simp]:
      "listprod [] = 1"
      "listprod (x # xs) = x * listprod xs"
      by (simp_all add: listprod_def)
    lemma "distinct as \<Longrightarrow> listprod as = \<Prod>(set as)"
      by(induction as) simp_all





section\<open>Executable Packet Set Representation\<close>

(* Not really used because it is not awesome :-( *)

text\<open>Recall: @{const alist_and} transforms @{typ "'a negation_type list \<Rightarrow> 'a match_expr"} and uses conjunction as connective.\<close>

text\<open>Symbolic (executable) representation. inner is @{text \<and>}, outer is @{text \<or>}\<close>
(*we remember the action which might be necessary for applying \<alpha>*)
(*the @{typ "'a"} negation type tells whether to negate the match expression*)
(*test: the action negation tells whether to negate the result of the match*)
(*due to unknowns, this may make a huge difference!*)
datatype 'a packet_set = PacketSet (packet_set_repr: "(('a negation_type \<times> action negation_type) list) list")

text\<open>Essentially, the @{typ "'a list list"} structure represents a DNF. See @{file "../Common/Negation_Type_DNF.thy"} for a pure Boolean version (without matching).\<close>

definition to_packet_set :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set" where
 "to_packet_set a m = PacketSet (map (map (\<lambda>m'. (m',Pos a)) o to_negation_type_nnf) (normalize_match m))"

fun get_action :: "action negation_type \<Rightarrow> action" where
  "get_action (Pos a) = a" |
  "get_action (Neg a) = a"

fun get_action_sign :: "action negation_type \<Rightarrow> (bool \<Rightarrow> bool)" where
  "get_action_sign (Pos _) = id" |
  "get_action_sign (Neg _) = (\<lambda>m. \<not> m)"

text\<open>
We collect all entries of the outer list.
For the inner list, we request that a packet matches all the entries.
A negated action means that the expression must not match.
Recall: @{term "matches \<gamma> (MatchNot m) a p \<noteq> (\<not> matches \<gamma> m a p)"}, due to @{const TernaryUnknown}
\<close>
definition packet_set_to_set :: "('a, 'packet) match_tac \<Rightarrow> 'a packet_set \<Rightarrow> 'packet set" where
  "packet_set_to_set \<gamma> ps \<equiv> \<Union> ms \<in> set (packet_set_repr ps).  {p. \<forall> (m, a) \<in> set ms. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)}"

lemma packet_set_to_set_alt:  "packet_set_to_set \<gamma> ps = (\<Union> ms \<in> set (packet_set_repr ps).  
  {p. \<forall> m a. (m, a) \<in> set ms \<longrightarrow> get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)})"
unfolding packet_set_to_set_def
by fast


text\<open>We really have a disjunctive normal form\<close>
lemma packet_set_to_set_alt2:  "packet_set_to_set \<gamma> ps = (\<Union> ms \<in> set (packet_set_repr ps).  
  (\<Inter>(m, a) \<in> set ms. {p. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)}))"
unfolding packet_set_to_set_alt
by blast

lemma to_packet_set_correct: "p \<in> packet_set_to_set \<gamma> (to_packet_set a m) \<longleftrightarrow> matches \<gamma> m a p"
apply(simp add: to_packet_set_def packet_set_to_set_def)
apply(rule iffI)
 apply(clarify)
 apply(induction m rule: normalize_match.induct)
       apply(simp_all add: bunch_of_lemmata_about_matches negation_type_to_match_expr_simps)
   apply force
apply (metis matches_DeMorgan)
apply(induction m rule: normalize_match.induct)
      apply(simp_all add: bunch_of_lemmata_about_matches negation_type_to_match_expr_simps)
 apply (metis Un_iff)
apply (metis Un_iff matches_DeMorgan)
done

lemma to_packet_set_set: "packet_set_to_set \<gamma> (to_packet_set a m) = {p. matches \<gamma> m a p}"
using to_packet_set_correct by fast

definition packet_set_UNIV :: "'a packet_set" where
  "packet_set_UNIV \<equiv> PacketSet [[]]"
lemma packet_set_UNIV: "packet_set_to_set \<gamma> packet_set_UNIV = UNIV"
by(simp add: packet_set_UNIV_def packet_set_to_set_def)

definition packet_set_Empty :: "'a packet_set" where
  "packet_set_Empty \<equiv> PacketSet []"
lemma packet_set_Empty: "packet_set_to_set \<gamma> packet_set_Empty = {}"
by(simp add: packet_set_Empty_def packet_set_to_set_def)

text\<open>If the matching agrees for two actions, then the packet sets are also equal\<close>
lemma "\<forall>p. matches \<gamma> m a1 p \<longleftrightarrow> matches \<gamma> m a2 p \<Longrightarrow> packet_set_to_set \<gamma> (to_packet_set a1 m) = packet_set_to_set \<gamma> (to_packet_set a2 m)"
apply(subst(asm) to_packet_set_correct[symmetric])+
apply safe
apply simp_all
done

subsubsection\<open>Basic Set Operations\<close>
  
  text\<open>@{text \<inter>}\<close>
    fun packet_set_intersect :: "'a packet_set \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_intersect (PacketSet olist1) (PacketSet olist2) = PacketSet [andlist1 @ andlist2. andlist1 <- olist1, andlist2 <- olist2]"
    
    lemma "packet_set_intersect (PacketSet [[a,b], [c,d]]) (PacketSet [[v,w], [x,y]]) = PacketSet [[a, b, v, w], [a, b, x, y], [c, d, v, w], [c, d, x, y]]" by simp
    
    declare packet_set_intersect.simps[simp del]
    
    
    lemma packet_set_intersect_intersect: "packet_set_to_set \<gamma> (packet_set_intersect P1 P2) = packet_set_to_set \<gamma> P1 \<inter> packet_set_to_set \<gamma> P2"
    unfolding packet_set_to_set_def
     apply(cases P1)
     apply(cases P2)
     apply(simp add: packet_set_intersect.simps)
     apply blast
    done
    
    
    lemma packet_set_intersect_correct: "packet_set_to_set \<gamma> (packet_set_intersect (to_packet_set a m1) (to_packet_set a m2)) = packet_set_to_set \<gamma> (to_packet_set a (MatchAnd m1 m2))"
     apply(simp add: to_packet_set_def packet_set_intersect.simps packet_set_to_set_alt)
     (*by fast very slow!*)
     apply safe
      apply simp_all
      apply blast+
     done
     
    lemma packet_set_intersect_correct': "p \<in> packet_set_to_set \<gamma> (packet_set_intersect (to_packet_set a m1) (to_packet_set a m2)) \<longleftrightarrow> matches \<gamma> (MatchAnd m1 m2) a p"
    apply(simp add: to_packet_set_correct[symmetric])
    using packet_set_intersect_correct by fast
  
    text\<open>The length of the result is the product of the input lengths\<close>
    lemma packet_set_intersetc_length: "length (packet_set_repr (packet_set_intersect (PacketSet ass) (PacketSet bss))) = length ass * length bss"
      by(induction ass) (simp_all add: packet_set_intersect.simps)
      

  
  text\<open>@{text \<union>}\<close>
    fun packet_set_union :: "'a packet_set \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_union (PacketSet olist1) (PacketSet olist2) = PacketSet (olist1 @ olist2)"
    declare packet_set_union.simps[simp del]
    
    lemma packet_set_union_correct: "packet_set_to_set \<gamma> (packet_set_union P1 P2) = packet_set_to_set \<gamma> P1 \<union> packet_set_to_set \<gamma> P2"
    unfolding packet_set_to_set_def
     apply(cases P1)
     apply(cases P2)
     apply(simp add: packet_set_union.simps)
    done
  
    lemma packet_set_append:
      "packet_set_to_set \<gamma> (PacketSet (p1 @ p2)) = packet_set_to_set \<gamma> (PacketSet p1) \<union> packet_set_to_set \<gamma> (PacketSet p2)"
      by(simp add: packet_set_to_set_def)
    lemma packet_set_cons: "packet_set_to_set \<gamma> (PacketSet (a # p3)) =  packet_set_to_set \<gamma> (PacketSet [a]) \<union> packet_set_to_set \<gamma> (PacketSet p3)"
      by(simp add: packet_set_to_set_def)
  
  

  text\<open>@{text -}\<close>
    fun listprepend :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
      "listprepend [] ns = []" |
      "listprepend (a#as) ns = (map (\<lambda>xs. a#xs) ns) @ (listprepend as ns)"
    
    text\<open>The returned result of @{const listprepend} can get long.\<close>
    lemma listprepend_length: "length (listprepend as bss) = length as * length bss"
      by(induction as) (simp_all)
    
    lemma packet_set_map_a_and: "packet_set_to_set \<gamma> (PacketSet (map (op # a) ds)) = packet_set_to_set \<gamma> (PacketSet [[a]]) \<inter> packet_set_to_set \<gamma> (PacketSet ds)"
      apply(induction ds)
       apply(simp_all add: packet_set_to_set_def)
      apply(case_tac a)
      apply(simp)
      apply blast
      done
    lemma listprepend_correct: "packet_set_to_set \<gamma> (PacketSet (listprepend as ds)) = packet_set_to_set \<gamma> (PacketSet (map (\<lambda>a. [a]) as)) \<inter> packet_set_to_set \<gamma> (PacketSet ds)"
      apply(induction as arbitrary: )
       apply(simp add: packet_set_to_set_alt)
      apply(simp)
      apply(rename_tac a as)
      apply(simp add: packet_set_map_a_and packet_set_append)
      (*using packet_set_cons by fast*)
      apply(subst(2) packet_set_cons)
      by blast
    
    lemma packet_set_to_set_map_singleton: "packet_set_to_set \<gamma> (PacketSet (map (\<lambda>a. [a]) as)) = (\<Union> a \<in> set as. packet_set_to_set \<gamma> (PacketSet [[a]]))"
    by(simp add: packet_set_to_set_alt)
    
    fun invertt :: "('a negation_type \<times> action negation_type) \<Rightarrow> ('a negation_type \<times> action negation_type)" where
      "invertt (n, a) = (n, invert a)"
    
    lemma singleton_invertt: "packet_set_to_set \<gamma> (PacketSet [[invertt n]]) =  - packet_set_to_set \<gamma> (PacketSet [[n]])"
     apply(simp add: to_packet_set_def packet_set_intersect.simps packet_set_to_set_alt)
     apply(case_tac n, rename_tac m a)
     apply(simp)
     apply(case_tac a)
      apply(simp_all)
      apply safe
     done
    
    lemma packet_set_to_set_map_singleton_invertt: 
      "packet_set_to_set \<gamma> (PacketSet (map ((\<lambda>a. [a]) \<circ> invertt) d)) = - (\<Inter> a \<in> set d. packet_set_to_set \<gamma> (PacketSet [[a]]))"
    apply(induction d)
     apply(simp)
     apply(simp add: packet_set_to_set_alt; fail)
    apply(simp)
    apply(subst(1) packet_set_cons)
    apply(simp)
    apply(simp add: packet_set_to_set_map_singleton singleton_invertt)
    done
    
    fun packet_set_not_internal :: " ('a negation_type \<times> action negation_type) list list \<Rightarrow>  ('a negation_type \<times> action  negation_type) list list" where
      "packet_set_not_internal [] = [[]]" |
      "packet_set_not_internal (ns#nss) = listprepend (map invertt ns) (packet_set_not_internal nss)"

    lemma packet_set_not_internal_length: "length (packet_set_not_internal ass) = listprod ([length n. n <- ass])"
      by(induction ass) (simp_all add: listprepend_length)
    
    lemma packet_set_not_internal_correct: "packet_set_to_set \<gamma> (PacketSet (packet_set_not_internal d)) = - packet_set_to_set \<gamma> (PacketSet d)"
      apply(induction d)
       apply(simp add: packet_set_to_set_alt)
      apply(rename_tac d ds)
      apply(simp add: )
      apply(simp add: listprepend_correct)
      apply(simp add: packet_set_to_set_map_singleton_invertt)
      apply(simp add: packet_set_to_set_alt)
      by blast
    
    fun packet_set_not :: "'a packet_set \<Rightarrow> 'a packet_set" where
      "packet_set_not (PacketSet ps) = PacketSet (packet_set_not_internal ps)"
    declare packet_set_not.simps[simp del]

    text\<open>The length of the result of @{const packet_set_not} is the multiplication over the length of all the inner sets.
      Warning: gets huge!
      See @{thm packet_set_not_internal_length}
\<close>
    
    lemma packet_set_not_correct: "packet_set_to_set \<gamma> (packet_set_not P) = - packet_set_to_set \<gamma> P"
    apply(cases P)
    apply(simp)
    apply(simp add: packet_set_not.simps)
    apply(simp add: packet_set_not_internal_correct)
    done

    

subsubsection\<open>Derived Operations\<close>
  definition packet_set_constrain :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_constrain a m ns = packet_set_intersect ns (to_packet_set a m)"
  
  theorem packet_set_constrain_correct: "packet_set_to_set \<gamma> (packet_set_constrain a m P) = {p \<in> packet_set_to_set \<gamma> P. matches \<gamma> m a p}"
  unfolding packet_set_constrain_def
  unfolding packet_set_intersect_intersect
  unfolding to_packet_set_set
  by blast
  
  text\<open>Warning: result gets huge\<close>
  definition packet_set_constrain_not :: "action \<Rightarrow> 'a match_expr \<Rightarrow> 'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_constrain_not a m ns = packet_set_intersect ns (packet_set_not (to_packet_set a m))"
  
  theorem packet_set_constrain_not_correct: "packet_set_to_set \<gamma> (packet_set_constrain_not a m P) = {p \<in> packet_set_to_set \<gamma> P. \<not> matches \<gamma> m a p}"
  unfolding packet_set_constrain_not_def
  unfolding packet_set_intersect_intersect
  unfolding packet_set_not_correct
  unfolding to_packet_set_set
  by blast


subsubsection\<open>Optimizing\<close>
  fun packet_set_opt1 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt1 (PacketSet ps) = PacketSet (map remdups (remdups ps))"
  declare packet_set_opt1.simps[simp del]
  
  lemma packet_set_opt1_correct: "packet_set_to_set \<gamma> (packet_set_opt1 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_to_set_alt packet_set_opt1.simps)


  fun packet_set_opt2_internal :: "(('a negation_type \<times> action negation_type) list) list \<Rightarrow> (('a negation_type \<times> action negation_type) list) list" where
    "packet_set_opt2_internal [] = []" |

    "packet_set_opt2_internal ([]#ps) = [[]]" | (*If UNIV is included, the whole expression is UNIV*)

    (*"packet_set_opt2_internal ([a]#ps) = ([a]#(filter (\<lambda>as. a \<notin> set as) ps))" |*)

    (*
    (*call recursively! we did not do this because it is really slow!*)
    (*if a more permissive expression is encountered, we can drop all less-permissive ones*)
    "packet_set_opt2_internal (as#ps) = (as#(*packet_set_opt2_internal*) ((filter (\<lambda>ass. \<not> set as \<subseteq> set ass) ps)))" (*this might be horribly inefficient ...*)
    *)

    (*this might be horribly inefficient, so we only test subsets for \<le> 5 entries*)
    "packet_set_opt2_internal (as#ps) = as# (if length as \<le> 5 then packet_set_opt2_internal ((filter (\<lambda>ass. \<not> set as \<subseteq> set ass) ps)) else packet_set_opt2_internal ps)" 

  lemma packet_set_opt2_internal_correct: "packet_set_to_set \<gamma> (PacketSet (packet_set_opt2_internal ps)) = packet_set_to_set \<gamma> (PacketSet ps)"
    apply(induction ps rule:packet_set_opt2_internal.induct)
    apply(simp_all add: packet_set_UNIV)
    apply(simp add: packet_set_to_set_alt)
    apply(simp add: packet_set_to_set_alt)
    apply(safe)[1]
    apply(simp_all)
    apply blast+
    (*apply(simp add: packet_set_to_set_alt)
    apply(safe)[1]
    apply(simp_all)
    apply blast+*)
    done
    
  export_code packet_set_opt2_internal checking SML

  fun packet_set_opt2 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt2 (PacketSet ps) = PacketSet (packet_set_opt2_internal ps)" 
  declare packet_set_opt2.simps[simp del]

  lemma packet_set_opt2_correct: "packet_set_to_set \<gamma> (packet_set_opt2 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_opt2.simps packet_set_opt2_internal_correct)


  text\<open>If we sort by length, we will hopefully get better results when applying @{const packet_set_opt2}.\<close>
  fun packet_set_opt3 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt3 (PacketSet ps) = PacketSet (sort_key (\<lambda>p. length p) ps)" (*quadratic runtime of sort?*)
  declare packet_set_opt3.simps[simp del]
  lemma packet_set_opt3_correct: "packet_set_to_set \<gamma> (packet_set_opt3 ps) = packet_set_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_opt3.simps packet_set_to_set_alt)
  
  fun packet_set_opt4_internal_internal :: "(('a negation_type \<times> action negation_type) list) \<Rightarrow> bool" where
    "packet_set_opt4_internal_internal cs = (\<forall> (m, a) \<in> set cs. (m, invert a) \<notin> set cs)"
  fun packet_set_opt4 :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt4 (PacketSet ps) = PacketSet (filter packet_set_opt4_internal_internal ps)"
  declare packet_set_opt4.simps[simp del]
  lemma packet_set_opt4_internal_internal_helper: assumes
      "\<forall>m a. (m, a) \<in> set xb \<longrightarrow> get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) xa)"
   shows "\<forall>(m, a)\<in>set xb. (m, invert a) \<notin> set xb"
   proof(clarify)
    fix a b
    assume a1: "(a, b) \<in> set xb" and a2: "(a, invert b) \<in> set xb"
    from assms a1 have 1: "get_action_sign b (matches \<gamma> (negation_type_to_match_expr a) (get_action b) xa)" by simp
    from assms a2 have 2: "get_action_sign (invert b) (matches \<gamma> (negation_type_to_match_expr a) (get_action (invert b)) xa)" by simp
    from 1 2 show "False"
      by(cases b) (simp_all)
   qed
  lemma packet_set_opt4_correct: "packet_set_to_set \<gamma> (packet_set_opt4 ps) = packet_set_to_set \<gamma> ps"
    apply(cases ps, clarify)
    apply(simp add: packet_set_opt4.simps packet_set_to_set_alt)
    apply(rule)
     apply blast
    apply(clarify)
    apply(simp)
    apply(rule_tac x=xb in exI)
    apply(simp)
    using packet_set_opt4_internal_internal_helper by fast


  definition packet_set_opt :: "'a packet_set \<Rightarrow> 'a packet_set" where
    "packet_set_opt ps = packet_set_opt1 (packet_set_opt2 (packet_set_opt3 (packet_set_opt4 ps)))" 

  lemma packet_set_opt_correct: "packet_set_to_set \<gamma> (packet_set_opt ps) = packet_set_to_set \<gamma> ps"
    using packet_set_opt_def packet_set_opt2_correct packet_set_opt3_correct packet_set_opt4_correct packet_set_opt1_correct by metis


subsection\<open>Conjunction Normal Form Packet Set\<close>
datatype 'a packet_set_cnf = PacketSetCNF (packet_set_repr_cnf: "(('a negation_type \<times> action negation_type) list) list")


lemma "\<not> ((a \<and> b) \<or> (c \<and> d)) \<longleftrightarrow> (\<not>a \<or> \<not>b) \<and> (\<not>c \<or> \<not> d)" by blast
lemma "\<not> ((a \<or> b) \<and> (c \<or> d)) \<longleftrightarrow> (\<not>a \<and> \<not>b) \<or> (\<not>c \<and> \<not> d)" by blast

definition packet_set_cnf_to_set :: "('a, 'packet) match_tac \<Rightarrow> 'a packet_set_cnf \<Rightarrow> 'packet set" where
  "packet_set_cnf_to_set \<gamma> ps \<equiv>  (\<Inter> ms \<in> set (packet_set_repr_cnf ps).  
  (\<Union>(m, a) \<in> set ms. {p. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (get_action a) p)}))"


  text\<open>Inverting a @{typ "'a packet_set"} and returning @{typ "'a packet_set_cnf"} is very efficient!\<close>
  fun packet_set_not_to_cnf :: "'a packet_set \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_not_to_cnf (PacketSet ps) = PacketSetCNF (map (\<lambda>a. map invertt a) ps)"
  declare packet_set_not_to_cnf.simps[simp del]

  lemma helper: "(case invertt x of (m, a) \<Rightarrow> {p. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (Packet_Set_Impl.get_action a) p)}) =
         (- (case x of (m, a) \<Rightarrow> {p. get_action_sign a (matches \<gamma> (negation_type_to_match_expr m) (Packet_Set_Impl.get_action a) p)}))"
    apply(case_tac x)
    apply(simp)
    apply(case_tac b)
    apply(simp_all)
    apply safe
    done
  lemma packet_set_not_to_cnf_correct: "packet_set_cnf_to_set \<gamma> (packet_set_not_to_cnf P) = - packet_set_to_set \<gamma> P"
  apply(cases P)
  apply(simp add: packet_set_not_to_cnf.simps packet_set_cnf_to_set_def packet_set_to_set_alt2)
  apply(subst helper)
  by simp

  fun packet_set_cnf_not_to_dnf :: "'a packet_set_cnf \<Rightarrow> 'a packet_set" where
    "packet_set_cnf_not_to_dnf (PacketSetCNF ps) = PacketSet (map (\<lambda>a. map invertt a) ps)"
  declare packet_set_cnf_not_to_dnf.simps[simp del]
  lemma packet_set_cnf_not_to_dnf_correct: "packet_set_to_set \<gamma> (packet_set_cnf_not_to_dnf P) = - packet_set_cnf_to_set \<gamma> P"
  apply(cases P)
  apply(simp add: packet_set_cnf_not_to_dnf.simps packet_set_cnf_to_set_def packet_set_to_set_alt2)
  apply(subst helper)
  by simp
  
  text\<open>Also, intersection is highly efficient in CNF\<close>
  fun packet_set_cnf_intersect :: "'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_cnf_intersect (PacketSetCNF ps1) (PacketSetCNF ps2) = PacketSetCNF (ps1 @ ps2)"
  declare packet_set_cnf_intersect.simps[simp del]
  
  lemma packet_set_cnf_intersect_correct: "packet_set_cnf_to_set \<gamma> (packet_set_cnf_intersect P1 P2) = packet_set_cnf_to_set \<gamma> P1 \<inter> packet_set_cnf_to_set \<gamma> P2"
    apply(case_tac P1)
    apply(case_tac P2)
    apply(simp add: packet_set_cnf_to_set_def packet_set_cnf_intersect.simps)
    apply(safe)
    apply(simp_all)
    done

  text\<open>Optimizing\<close>
  fun packet_set_cnf_opt1 :: "'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_cnf_opt1 (PacketSetCNF ps) = PacketSetCNF (map remdups (remdups ps))"
  declare packet_set_cnf_opt1.simps[simp del]
  
  lemma packet_set_cnf_opt1_correct: "packet_set_cnf_to_set \<gamma> (packet_set_cnf_opt1 ps) = packet_set_cnf_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_cnf_to_set_def packet_set_cnf_opt1.simps)


  fun packet_set_cnf_opt2_internal :: "(('a negation_type \<times> action negation_type) list) list \<Rightarrow> (('a negation_type \<times> action negation_type) list) list" where
    "packet_set_cnf_opt2_internal [] = []" |
    "packet_set_cnf_opt2_internal ([]#ps) = [[]]" | 
    (*TODO recursive calls missing? do similar to DNF opt?*)
    "packet_set_cnf_opt2_internal (as#ps) = (as#(filter (\<lambda>ass. \<not> set as \<subseteq> set ass) ps))" (*this might be horribly inefficient ...*)

  lemma packet_set_cnf_opt2_internal_correct: "packet_set_cnf_to_set \<gamma> (PacketSetCNF (packet_set_cnf_opt2_internal ps)) = packet_set_cnf_to_set \<gamma> (PacketSetCNF ps)"
    apply(induction ps rule:packet_set_cnf_opt2_internal.induct)
    apply(simp_all add: packet_set_cnf_to_set_def)
    by blast
  fun packet_set_cnf_opt2 :: "'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_cnf_opt2 (PacketSetCNF ps) = PacketSetCNF (packet_set_cnf_opt2_internal ps)" 
  declare packet_set_cnf_opt2.simps[simp del]

  lemma packet_set_cnf_opt2_correct: "packet_set_cnf_to_set \<gamma> (packet_set_cnf_opt2 ps) = packet_set_cnf_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_cnf_opt2.simps packet_set_cnf_opt2_internal_correct)

  fun packet_set_cnf_opt3 :: "'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_cnf_opt3 (PacketSetCNF ps) = PacketSetCNF (sort_key (\<lambda>p. length p) ps)" (*quadratic runtime of sort?*)
  declare packet_set_cnf_opt3.simps[simp del]
  lemma packet_set_cnf_opt3_correct: "packet_set_cnf_to_set \<gamma> (packet_set_cnf_opt3 ps) = packet_set_cnf_to_set \<gamma> ps"
    by(cases ps) (simp add: packet_set_cnf_opt3.simps packet_set_cnf_to_set_def)
 
  definition packet_set_cnf_opt :: "'a packet_set_cnf \<Rightarrow> 'a packet_set_cnf" where
    "packet_set_cnf_opt ps = packet_set_cnf_opt1 (packet_set_cnf_opt2 (packet_set_cnf_opt3 (ps)))" 

  lemma packet_set_cnf_opt_correct: "packet_set_cnf_to_set \<gamma> (packet_set_cnf_opt ps) = packet_set_cnf_to_set \<gamma> ps"
    using packet_set_cnf_opt_def packet_set_cnf_opt2_correct packet_set_cnf_opt3_correct packet_set_cnf_opt1_correct by metis



hide_const (open) get_action get_action_sign packet_set_repr packet_set_repr_cnf

end
