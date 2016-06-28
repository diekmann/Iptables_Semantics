(*  Title:       Interuptible Fold
    Author:      Thomas Tuerk <tuerk@in.tum.de>
*)
section {* Interuptible Fold *}
theory Foldi
imports Main 
begin

subsection {* Left folding *}

primrec foldli where
   "foldli [] c f \<sigma> = \<sigma>"
 | "foldli (x#xs) c f \<sigma> =
    (if c \<sigma> then foldli xs c f (f x \<sigma>) else \<sigma>)"

lemma foldli_not_cond [simp] :
   "\<not>(c \<sigma>) \<Longrightarrow>foldli xs c f \<sigma> = \<sigma>"
by (cases xs, simp_all)

lemma foldli_cong [fundef_cong]:
  assumes "l = l'" "\<sigma> = \<sigma>'" "c = c'"
  and ff': "\<And>\<sigma> x. \<lbrakk> x \<in> set l'; c' \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> = f' x \<sigma>"
  shows "foldli l c f \<sigma> = foldli l' c' f' \<sigma>'"
unfolding assms using ff'
by(induct l' arbitrary: \<sigma>') auto

text {* Notice that @{term foldli} is a generalisation of folding that respects the abortion condition. *}
lemma foldli_foldl :
  "foldli xs (\<lambda>_. True) f \<sigma> = foldl (\<lambda>\<sigma> x. f x \<sigma>) \<sigma> xs"
by (induct xs arbitrary: \<sigma>) simp_all

lemma foldli_append :
   "foldli (xs1 @ xs2) c f \<sigma> =
    foldli xs2 c f (foldli xs1 c f \<sigma>)"
by (induct xs1 arbitrary: \<sigma>, simp_all)

lemma foldli_concat :
   "foldli (concat xs) c f \<sigma> =
    foldli xs c (\<lambda>x. foldli x c f) \<sigma>"
by (induct xs arbitrary: \<sigma>, simp_all add: foldli_append)

lemma foldli_map :
  "foldli (map f1 xs) c f2 \<sigma> =
   foldli xs c (f2 \<circ> f1) \<sigma>"
by (induct xs arbitrary: \<sigma>, simp_all)

lemma foldli_snoc :
   "foldli (xs @ [x]) c f \<sigma> =
    (if c (foldli xs c f \<sigma>) then 
     f x (foldli xs c f \<sigma>) else (foldli xs c f \<sigma>))"
by (induct xs arbitrary: \<sigma>, simp_all)

lemma foldli_snoc_id[simp]: "foldli l (\<lambda>_. True) (\<lambda>x l. l@[x]) l0 = l0@l"
  by (induct l arbitrary: l0) (auto)

subsection {* Right folding *}

definition foldri :: "'x list \<Rightarrow> ('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"  where
  "foldri l = foldli (rev l)"

lemma foldri_simp[simp] : 
  "foldri [] c f \<sigma> = \<sigma>"
  "foldri (l@[x]) c f \<sigma> = (if c \<sigma> then foldri l c f (f x \<sigma>) else \<sigma>)"
  unfolding foldri_def by simp_all

lemma foldri_simp_Cons[simp] : 
  "foldri (x # l) c f \<sigma> = (if (c (foldri l c f \<sigma>)) then  f x (foldri l c f \<sigma>) else (foldri l c f \<sigma>))"
  unfolding foldri_def by (simp add: foldli_append)

lemma foldri_code[code] : 
  "foldri [] c f \<sigma> = \<sigma>"
  "foldri (x # l) c f \<sigma> = (let \<sigma>' = foldri l c f \<sigma> in if c \<sigma>' then  f x \<sigma>' else \<sigma>')"
  by simp_all

lemma foldri_not_cond [simp] :
   "\<not>(c \<sigma>) \<Longrightarrow>foldri xs c f \<sigma> = \<sigma>"
unfolding foldri_def by simp

lemma foldri_cong [fundef_cong]:
  assumes "l = l'" "\<sigma> = \<sigma>'" "c = c'"
  and ff': "\<And>\<sigma> x. \<lbrakk> x \<in> set l'; c' \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> = f' x \<sigma>"
  shows "foldri l c f \<sigma> = foldri l' c' f' \<sigma>'"
unfolding assms using ff'
by(induct l' arbitrary: \<sigma>') auto

text {* Notice that @{term foldli} is a generalisation of folding that respects the abortion condition. *}
lemma foldri_foldr :
  "foldri xs (\<lambda>_. True) f \<sigma> = foldr (\<lambda>x \<sigma>. f x \<sigma>) xs \<sigma>"
by (induct xs arbitrary: \<sigma>) simp_all

lemma foldri_append :
   "foldri (xs1 @ xs2) c f \<sigma> =
    foldri xs1 c f (foldri xs2 c f \<sigma>)"
unfolding foldri_def
by (simp add: foldli_append)

lemma foldri_concat :
   "foldri (concat xs) c f \<sigma> =
    foldri xs c (\<lambda>x. foldri x c f) \<sigma>"
unfolding foldri_def
by (simp add: rev_concat foldli_concat foldli_map o_def)

lemma foldri_map :
  "foldri (map f1 xs) c f2 \<sigma> =
   foldri xs c (f2 \<circ> f1) \<sigma>"
unfolding foldri_def
by (simp add: rev_map foldli_map)

lemma foldri_cons_id[simp]: "foldri l (\<lambda>_. True) (\<lambda>x l. x#l) [] = l"
  by (induct l) (auto)

end
