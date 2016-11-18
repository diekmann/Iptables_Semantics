section\<open>Misc\<close>
theory OpenFlow_Helpers
imports Main
begin

lemma hrule: "(S = UNIV) = (\<forall>x. x \<in> S)"
  by blast

subsection\<open>Single valuedness on lists\<close>

lemma foldr_True_set: "foldr (\<lambda>x. op \<and> (f x)) l True = (\<forall>x \<in> set l. f x)"
  by (induction l) simp_all

fun single_valued_code where
"single_valued_code [] = True" |
"single_valued_code (e#es) = (foldr (\<lambda>x. op \<and> (fst x \<noteq> fst e \<or> snd x = snd e)) es True \<and> single_valued_code es)"
lemma single_valued_code_lam[code_unfold]:
  "single_valued (set r) = single_valued_code r"
proof(induction r)
  case Nil show ?case by simp
next
  case (Cons e es)
  show ?case
  proof (rule iffI, goal_cases fwd bwd)
    case bwd
    have "single_valued (set es)" using Cons.IH conjunct2[OF bwd[unfolded single_valued_code.simps]] ..
    moreover
    have "\<forall>x\<in>set es. fst x \<noteq> fst e \<or> snd x = snd e"
      using conjunct1[OF bwd[unfolded single_valued_code.simps(2)], unfolded foldr_True_set] .
    ultimately
    show ?case unfolding single_valued_def by auto
  next
    case fwd
    have "single_valued (set es)" using fwd unfolding single_valued_def by simp
    with Cons.IH[symmetric] have "single_valued_code es" ..
    moreover
    have "\<forall>x\<in>set es. fst x \<noteq> fst e \<or> snd x = snd e" using fwd unfolding single_valued_def by clarsimp
    from conjI[OF this calculation, unfolded foldr_True_set[symmetric]]
    show ?case unfolding single_valued_code.simps .
  qed
qed

lemma set_Cons: "e \<in> set (a # as) \<longleftrightarrow> (e = a \<or> e \<in> set as)" by simp

subsection\<open>List fun\<close>

lemma sorted_const: "sorted (map (\<lambda>y. x) k)"
	by(induction k) (simp_all add: sorted_Cons)

lemma list_all_map: "list_all f (map g l) = list_all (f \<circ> g) l"
unfolding comp_def by (simp add: list_all_length) (* by(induction l) simp_all *)

lemma distinct_2lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow>
	(\<And>a b e i. f a b = f e i \<Longrightarrow> a = e \<and> b = i) \<Longrightarrow>
	distinct [f a b. a \<leftarrow> as, b \<leftarrow> bs]"
  apply(induction as)
   apply(simp;fail)
  apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
  apply(rule)
  subgoal
   apply(clarify;fail | subst distinct_map, rule)+
   by (rule inj_onI) simp
  subgoal by fastforce
done

lemma distinct_3lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow> distinct cs \<Longrightarrow>
	(\<And>a b c e i g. f a b c = f e i g \<Longrightarrow> a = e \<and> b = i \<and> c = g) \<Longrightarrow>
	distinct [f a b c. a \<leftarrow> as, b \<leftarrow> bs, c \<leftarrow> cs]"
  apply(induction as)
   apply(simp;fail)
  apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
  apply(rule)
   apply(rule distinct_2lcomprI; simp_all; fail)
  apply fastforce
done

lemma distinct_fst: "distinct (map fst a) \<Longrightarrow> distinct a" by (metis distinct_zipI1 zip_map_fst_snd)
lemma distinct_snd: "distinct (map snd a) \<Longrightarrow> distinct a" by (metis distinct_zipI2 zip_map_fst_snd)

lemma inter_empty_fst2: "(\<lambda>(p, m, a). (p, m)) ` S \<inter> (\<lambda>(p, m, a). (p, m)) ` T = {} \<Longrightarrow> S \<inter> T = {}" by blast

subsection\<open>Cardinality and Existence of Distinct Members\<close>

lemma card1_eI: "1 \<le> card S \<Longrightarrow> \<exists>y S'. S = {y} \<union> S' \<and> y \<notin> S'"
	by (metis One_nat_def card_infinite card_le_Suc_iff insert_is_Un leD zero_less_Suc)
lemma card2_eI: "2 \<le> card S \<Longrightarrow> \<exists>x y. x \<noteq> y \<and> x \<in> S \<and> y \<in> S"
proof goal_cases
	case (1)
	then have "1 \<le> card S" by simp
	note card1_eI[OF this]
	then obtain x S' where xs: "S = {x} \<union> S' \<and> x \<notin> S'" by presburger
	then have "1 \<le> card S'" 
		by (metis 1 Suc_1 card_infinite card_insert_if finite_Un insert_is_Un le0 not_less_eq_eq) 
	then obtain y where "y \<in> S'" by fastforce
	then show ?case using xs by force
qed
lemma card3_eI: "3 \<le> card S \<Longrightarrow> \<exists>x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> S \<and> y \<in> S"
proof goal_cases
  case 1
  then have "2 \<le> card S" by simp
	note card2_eI[OF this]
	then obtain x y S' where xs: "S = {x,y} \<union> S' \<and> x \<notin> S' \<and> y \<notin> S' \<and> x \<noteq> y" 
	  by (metis Set.set_insert Un_insert_left insert_eq_iff insert_is_Un)
	then have "1 \<le> card S'"
	  using 1  by (metis One_nat_def Suc_leI Un_insert_left card_gt_0_iff insert_absorb numeral_3_eq_3 singleton_insert_inj_eq card_infinite card_insert_if finite_Un insert_is_Un le0 not_less_eq_eq) (* uuuh *)
	then obtain z where "z \<in> S'" by fastforce
	then show ?case using xs by force
qed

lemma card1_eE: "finite S \<Longrightarrow> \<exists>y. y \<in> S \<Longrightarrow> 1 \<le> card S" using card_0_eq by fastforce
lemma card2_eE: "finite S \<Longrightarrow> \<exists>x y. x \<noteq> y \<and> x \<in> S \<and> y \<in> S \<Longrightarrow> 2 \<le> card S"
using card1_eE card_Suc_eq card_insert_if by fastforce
lemma card3_eE: "finite S \<Longrightarrow> \<exists>x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> S \<and> y \<in> S \<Longrightarrow> 3 \<le> card S"
using card2_eE card_Suc_eq card_insert_if oops

lemma f_Img_ex_set: "{f x|x. P x} = f ` {x. P x}" by auto

lemma set_maps: "set (List.maps f a) = (\<Union>a\<in>set a. set (f a))" 
unfolding List.maps_def set_concat set_map UN_simps(10) ..


end
