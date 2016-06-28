theory CaesarTheories
imports Main
begin

subsection\<open>Misc\<close>

lemma ex_helper: "cond something = (\<exists>x. (x = something \<and> (cond x)))" by simp

lemma hrule: "(S = UNIV) = (\<forall>x. x \<in> S)"
  by blast

lemma Union_intersection_helper: "\<Union>x = UNIV \<Longrightarrow> \<Union>y = UNIV \<Longrightarrow> \<Union>{a \<inter> b|a b. a \<in> x \<and> b \<in> y \<and> a \<inter> b \<noteq> {}} = UNIV"
  apply(subgoal_tac "\<Union>{a \<inter> b|a b. a \<in> x \<and> b \<in> y} = UNIV")
   apply(thin_tac "\<Union>x = UNIV")
   apply(thin_tac "\<Union>y = UNIV")
   apply(unfold hrule)[1]
   apply clarify
   apply(rename_tac xx)
   apply(subgoal_tac "\<exists>a b. (xx \<in> a \<inter> b \<and> a \<in> x \<and> b \<in> y \<and> a \<inter> b \<noteq> {})")
    apply blast
   apply fast
  apply auto
  apply(metis IntI UNIV_I UnionE)
done

lemma fst_pairset: "fst ` {(f1 b, f2 b) |b. b \<in> R} = {f1 b|b. b \<in> R}" 
  by force

lemma image_pair_image: "(\<lambda>(x, y). (f1 x, f2 y)) ` (\<lambda>x. (g1 x, g2 x)) ` A = (\<lambda>x. (f1 (g1 x), f2 (g2 x))) ` A"
  unfolding image_image
  by simp

lemma snd_image_pair: "snd ` (\<lambda>(x, y). (f1 x, f2 y)) ` r = (f2 \<circ> snd) ` r"
  unfolding comp_def image_image by force

lemma image_set_comprehension: "f ` set S = {f x|x. x \<in> set S}"
   by blast

subsection\<open>single valued on lists\<close>

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
  proof
    case goal2 
    have "single_valued (set es)" using Cons.IH conjunct2[OF goal2[unfolded single_valued_code.simps]] ..
    moreover
    have "\<forall>x\<in>set es. fst x \<noteq> fst e \<or> snd x = snd e"
      using conjunct1[OF goal2[unfolded single_valued_code.simps(2)], unfolded foldr_True_set] .
    ultimately
    show ?case unfolding single_valued_def by auto
  next
    case goal1
    have "single_valued (set es)" using goal1 unfolding single_valued_def by simp
    with Cons.IH[symmetric] have "single_valued_code es" ..
    moreover
    have "\<forall>x\<in>set es. fst x \<noteq> fst e \<or> snd x = snd e" using goal1 unfolding single_valued_def by clarsimp
    from conjI[OF this calculation, unfolded foldr_True_set[symmetric]]
    show ?case unfolding single_valued_code.simps .
  qed
qed

lemma set_Cons: "e \<in> set (a # as) \<longleftrightarrow> (e = a \<or> e \<in> set as)" by simp

subsection\<open>Reduction\<close>

definition "domain_for R y \<equiv> {x. (x, y) \<in> R}"
lemma "domain_for {(1::nat, ''x''), (2, ''y''), (3, ''x'')} ''x'' = {1,3}" by(auto simp add: domain_for_def)
definition "left_reduce R \<equiv> {z|b z. z = (\<Union>domain_for R b,b) \<and> b \<in> Range R}"

lemma domain_for_image: "domain_for ((\<lambda>(x, y). (f1 x, y)) ` r) a = f1 ` domain_for r a"
  unfolding domain_for_def by fast

lemma left_reduce_preimage_stable: "\<Union>(fst`(left_reduce R)) = \<Union>(fst ` R)"
  unfolding left_reduce_def domain_for_def
  by force

lemma left_reduce_alt_def: "left_reduce R = {(\<Union>{a|a. (a,b) \<in> R}, b)|b. b : Range R}"
  unfolding left_reduce_def domain_for_def by simp

lemma left_reduce_image_stable: "snd`(left_reduce R) = (snd ` R)"
  unfolding left_reduce_alt_def
  by force

definition "list_domain_for r y = (foldr (\<lambda>x f. if snd x = y then fst x # f else f) r [])"
lemma list_domain_for_eq: "set (list_domain_for r y) = domain_for (set r) y"
  unfolding list_domain_for_def domain_for_def
  by(induction r) (simp, force)

definition list_left_reduce :: "('a list \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "list_left_reduce ff R \<equiv> map (\<lambda>rs. (ff (list_domain_for R rs), rs)) (remdups (map snd R))"

lemma list_left_reduce_set_eq:
  assumes ltr: "\<And>rs. rts (ltr rs) = (\<Union>x \<in> set rs. (rts x))"
  assumes rrtsr: "\<And>r. rrtsr r \<equiv> set (map (\<lambda>(x, y). (rts x, y)) r)"
  shows "rrtsr (list_left_reduce ltr r) = left_reduce (rrtsr r)"
  unfolding list_left_reduce_def left_reduce_def
  unfolding rrtsr
  unfolding set_map set_remdups
  unfolding image_pair_image
  unfolding ltr
  unfolding list_domain_for_eq
  unfolding domain_for_image
  unfolding image_image
  unfolding Range_snd
  unfolding snd_image_pair[of _ id, unfolded id_o id_def]
  by force

lemma sorted_const: "sorted (map (\<lambda>y. x) k)"
	by(induction k) (simp_all add: sorted_Cons)

lemma list_all_map: "list_all f (map g l) = list_all (f \<circ> g) l"
unfolding comp_def by (simp add: list_all_length) (* by(induction l) simp_all *)


lemma map_injective_eq: "map f xs = map g ys \<Longrightarrow> (\<And>e. f e = g e) \<Longrightarrow> inj f \<Longrightarrow> xs = ys"
	apply(rule map_injective[rotated])
	 apply(simp)+
done

lemma list_at_eqD: "aa @ ab = ba @ bb \<Longrightarrow> length aa = length ba \<Longrightarrow> length ab = length bb \<Longrightarrow> aa = ba \<and> ab = bb"
by simp

lemma list_induct_2simul:
	"P [] [] \<Longrightarrow> (\<And>a as bs. P as bs \<Longrightarrow> P (a # as) bs) \<Longrightarrow> (\<And>b as bs. P as bs \<Longrightarrow> P as (b # bs)) \<Longrightarrow> P x y"
	apply(induction x)
	 apply(metis list_nonempty_induct)
	apply(induction y)
	 apply(simp)
	apply(simp)
done
lemma list_induct_3simul:
	"P [] [] [] \<Longrightarrow> 
	(\<And>e a b c. P a b c \<Longrightarrow> P (e # a) b c) \<Longrightarrow>
	(\<And>e a b c. P a b c \<Longrightarrow> P a (e # b) c) \<Longrightarrow>
	(\<And>e a b c. P a b c \<Longrightarrow> P a b (e # c)) \<Longrightarrow>
	P x y z"
	apply(induction x)
	 apply(induction y)
	  apply(induction z)
	    apply(simp_all)
done
lemma list_induct_4simul:
	"P [] [] [] [] \<Longrightarrow> 
	(\<And>e a b c d. P a b c d \<Longrightarrow> P (e # a) b c d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a (e # b) c d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a b (e # c) d) \<Longrightarrow>
	(\<And>e a b c d. P a b c d \<Longrightarrow> P a b c (e # d)) \<Longrightarrow>
	P x y z w"
	apply(induction x)
	 apply(induction y)
	  apply(induction z)
	   apply(induction w)
	    apply(simp_all)
done

lemma distinct_2lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow>
	(\<And>a b e i. f a b = f e i \<Longrightarrow> a = e \<and> b = i) \<Longrightarrow>
	distinct [f a b. a \<leftarrow> as, b \<leftarrow> bs]"
apply(induction as)
apply(simp;fail)
apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
apply(rule)
defer
apply fastforce
apply(clarify;fail | subst distinct_map, rule)+
apply(rule inj_onI)
apply(simp)
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

lemma distinct_4lcomprI: "distinct as \<Longrightarrow> distinct bs \<Longrightarrow> distinct cs \<Longrightarrow> distinct ds \<Longrightarrow>
	(\<And>a b c d e i g h. f a b c d = f e i g h \<Longrightarrow> a = e \<and> b = i \<and> c = g \<and> d = h) \<Longrightarrow>
	distinct [f a b c d. a \<leftarrow> as, b \<leftarrow> bs, c \<leftarrow> cs, d \<leftarrow> ds]"
apply(induction as)
apply(simp;fail)
apply(clarsimp simp only: distinct.simps simp_thms list.map concat.simps map_append distinct_append)
apply(rule)
apply(rule distinct_3lcomprI; simp_all; fail)
apply fastforce
done

lemma if_f_distrib: "(if a then b else c) k = (if a then b k else c k)" by simp

lemma distinct_fst: "distinct (map fst a) \<Longrightarrow> distinct a" by (metis distinct_zipI1 zip_map_fst_snd)
lemma distinct_snd: "distinct (map snd a) \<Longrightarrow> distinct a" by (metis distinct_zipI2 zip_map_fst_snd)

lemma inter_empty_fst2: "(\<lambda>(p, m, a). (p, m)) ` S \<inter> (\<lambda>(p, m, a). (p, m)) ` T = {} \<Longrightarrow> S \<inter> T = {}" by blast

end
