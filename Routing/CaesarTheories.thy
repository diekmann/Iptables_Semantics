theory CaesarTheories
imports Main
begin

subsection{*Misc*}

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

subsection{*single valued on lists*}

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

subsection{*Reduction*}

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
  assumes ltr: "\<And>rs. rts (ltr rs) = \<Union>set (map rts rs)"
  assumes rrtsr: "\<And>r. rrtsr r \<equiv> set (map (\<lambda>(x, y). (rts x, y)) r)"
  shows "rrtsr (list_left_reduce ltr r) = left_reduce (rrtsr r)"
  unfolding list_left_reduce_def left_reduce_def
  unfolding rrtsr
  unfolding set_map set_remdups
  unfolding image_pair_image
  unfolding ltr
  unfolding set_map
  unfolding list_domain_for_eq
  unfolding domain_for_image
  unfolding image_image
  unfolding Range_snd
  unfolding snd_image_pair[of _ id, unfolded id_o id_def]
  by force

end
