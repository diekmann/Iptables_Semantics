theory Negation_Type
imports Main
begin

section{*Negation Type*}

text{*Only negated or non-negated literals *}
datatype 'a negation_type = Pos 'a | Neg 'a

fun getPos :: "'a negation_type list \<Rightarrow> 'a list" where
  "getPos [] = []" |
  "getPos ((Pos x)#xs) = x#(getPos xs)" |
  "getPos (_#xs) = getPos xs"

fun getNeg :: "'a negation_type list \<Rightarrow> 'a list" where
  "getNeg [] = []" |
  "getNeg ((Neg x)#xs) = x#(getNeg xs)" |
  "getNeg (_#xs) = getNeg xs"


text{*If there is @{typ "'a negation_type"}, then apply a @{term map} only to @{typ 'a}.
I.e. keep @{term Neg} and @{term Pos}*}
fun NegPos_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a negation_type list \<Rightarrow> 'b negation_type list" where
  "NegPos_map _ [] = []" |
  "NegPos_map f ((Pos a)#as) = (Pos (f a))#NegPos_map f as" |
  "NegPos_map f ((Neg a)#as) = (Neg (f a))#NegPos_map f as"

text{*Example*}
lemma "NegPos_map (\<lambda>x::nat. x+1) [Pos 0, Neg 1] = [Pos 1, Neg 2]" by eval

lemma getPos_NegPos_map_simp: "(getPos (NegPos_map X (map Pos src))) = map X src"
  by(induction src) (simp_all)
lemma getNeg_NegPos_map_simp: "(getNeg (NegPos_map X (map Neg src))) = map X src"
  by(induction src) (simp_all)
lemma getNeg_Pos_empty: "(getNeg (NegPos_map X (map Pos src))) = []"
  by(induction src) (simp_all)
lemma getNeg_Neg_empty: "(getPos (NegPos_map X (map Neg src))) = []"
  by(induction src) (simp_all)
lemma getPos_NegPos_map_simp2: "(getPos (NegPos_map X src)) = map X (getPos src)"
  by(induction src rule: getPos.induct) (simp_all)
lemma getNeg_NegPos_map_simp2: "(getNeg (NegPos_map X src)) = map X (getNeg src)"
  by(induction src rule: getPos.induct) (simp_all)
lemma getPos_id: "(getPos (map Pos (getPos src))) = getPos src"
  by(induction src rule: getPos.induct) (simp_all)
lemma getNeg_id: "(getNeg (map Neg (getNeg src))) = getNeg src"
  by(induction src rule: getNeg.induct) (simp_all)
lemma getPos_empty2: "(getPos (map Neg src)) = []"
  by(induction src) (simp_all)
lemma getNeg_empty2: "(getNeg (map Pos src)) = []"
  by(induction src) (simp_all)

lemmas NegPos_map_simps = getPos_NegPos_map_simp getNeg_NegPos_map_simp getNeg_Pos_empty getNeg_Neg_empty getPos_NegPos_map_simp2 
                          getNeg_NegPos_map_simp2 getPos_id getNeg_id getPos_empty2 getNeg_empty2

lemma NegPos_map_append: "NegPos_map C (as @ bs) = NegPos_map C as @ NegPos_map C bs"
  by(induction as rule: getNeg.induct) (simp_all)

lemma getPos_set: "Pos a \<in> set x \<longleftrightarrow> a \<in> set (getPos x)"
 apply(induction x rule: getPos.induct)
 apply(auto)
 done
lemma getNeg_set: "Neg a \<in> set x \<longleftrightarrow> a \<in> set (getNeg x)"
 apply(induction x rule: getPos.induct)
 apply(auto)
 done
lemma getPosgetNeg_subset: "set x \<subseteq> set x' \<longleftrightarrow>  set (getPos x) \<subseteq> set (getPos x') \<and> set (getNeg x) \<subseteq> set (getNeg x')"
  apply(induction x rule: getPos.induct)
  apply(simp)
  apply(simp add: getPos_set)
  apply(rule iffI)
  apply(simp_all add: getPos_set getNeg_set)
done
lemma set_Pos_getPos_subset: "Pos ` set (getPos x) \<subseteq> set x"
 apply(induction x rule: getPos.induct)
 apply(simp_all)
 apply blast+
done
lemma set_Neg_getNeg_subset: "Neg ` set (getNeg x) \<subseteq> set x"
 apply(induction x rule: getNeg.induct)
 apply(simp_all)
 apply blast+
done
lemmas NegPos_set = getPos_set getNeg_set getPosgetNeg_subset set_Pos_getPos_subset set_Neg_getNeg_subset
hide_fact getPos_set getNeg_set getPosgetNeg_subset set_Pos_getPos_subset set_Neg_getNeg_subset


fun invert :: "'a negation_type \<Rightarrow> 'a negation_type" where
  "invert (Pos x) = Neg x" |
  "invert (Neg x) = (Pos x)"

end
