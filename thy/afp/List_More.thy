(* Author: Dmitry Traytel *)
theory List_More
imports Main "~~/src/HOL/Library/Multiset"
begin

subsection {* Library Functions *}

text {* Map with index *}

primrec map_index' :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_index' n f [] = []"
| "map_index' n f (x#xs) = f n x # map_index' (Suc n) f xs"

lemma length_map_index'[simp]: "length (map_index' n f xs) = length xs"
  by (induct xs arbitrary: n) auto

lemma map_index'_map_zip: "map_index' n f xs = map (case_prod f) (zip [n ..< n + length xs] xs)"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  hence "map_index' n f (x#xs) = f n x # map (case_prod f) (zip [Suc n ..< n + length (x # xs)] xs)" by simp
  also have "\<dots> =  map (case_prod f) (zip (n # [Suc n ..< n + length (x # xs)]) (x # xs))" by simp
  also have "(n # [Suc n ..< n + length (x # xs)]) = [n ..< n + length (x # xs)]" by (induct xs) auto
  finally show ?case by simp
qed simp

abbreviation "map_index \<equiv> map_index' 0"

lemmas map_index = map_index'_map_zip[of 0, simplified]

lemma take_map_index: "take p (map_index f xs) = map_index f (take p xs)"
  unfolding map_index by (auto simp: min_def take_map take_zip)

lemma drop_map_index: "drop p (map_index f xs) = map_index' p f (drop p xs)"
  unfolding map_index'_map_zip by (cases "p < length xs") (auto simp: drop_map drop_zip)

lemma map_map_index[simp]: "map g (map_index f xs) = map_index (\<lambda>n x. g (f n x)) xs"
  unfolding map_index by auto

lemma map_index_map[simp]: "map_index f (map g xs) = map_index (\<lambda>n x. f n (g x)) xs"
  unfolding map_index by (auto simp: map_zip_map2)

lemma set_map_index[simp]: "x \<in> set (map_index f xs) = (\<exists>i < length xs. f i (xs ! i) = x)"
  unfolding map_index by (auto simp: set_zip intro!: image_eqI[of _ "case_prod f"])

lemma set_map_index'[simp]: "x\<in>set (map_index' n f xs) 
  \<longleftrightarrow> (\<exists>i<length xs. f (n+i) (xs!i) = x) "
  unfolding map_index'_map_zip 
  by (auto simp: set_zip intro!: image_eqI[of _ "case_prod f"])


lemma nth_map_index[simp]: "p < length xs \<Longrightarrow> map_index f xs ! p = f p (xs ! p)"
  unfolding map_index by auto

lemma map_index_cong:
  "\<forall>p < length xs. f p (xs ! p) = g p (xs ! p) \<Longrightarrow> map_index f xs = map_index g xs"
  unfolding map_index by (auto simp: set_zip)

lemma map_index_id: "map_index (curry snd) xs = xs"
  unfolding map_index by auto

lemma map_index_no_index[simp]: "map_index (\<lambda>n x. f x) xs = map f xs"
  unfolding map_index by (induct xs rule: rev_induct) auto

lemma map_index_congL:
  "\<forall>p < length xs. f p (xs ! p) = xs ! p \<Longrightarrow> map_index f xs = xs"
  by (rule trans[OF map_index_cong map_index_id]) auto

lemma map_index'_is_NilD: "map_index' n f xs = [] \<Longrightarrow> xs = []"
  by (induct xs) auto

declare map_index'_is_NilD[of 0, dest!]

lemma map_index'_is_ConsD:
  "map_index' n f xs = y # ys \<Longrightarrow> \<exists>z zs. xs = z # zs \<and> f n z = y \<and> map_index' (n + 1) f zs = ys"
  by (induct xs arbitrary: n) auto

lemma map_index'_eq_imp_length_eq: "map_index' n f xs = map_index' n g ys \<Longrightarrow> length xs = length ys"
proof (induct ys arbitrary: xs n)
  case (Cons y ys) thus ?case by (cases xs) auto
qed (auto dest!: map_index'_is_NilD)

lemmas map_index_eq_imp_length_eq = map_index'_eq_imp_length_eq[of 0]

lemma map_index'_comp[simp]: "map_index' n f (map_index' n g xs) = map_index' n (\<lambda>n. f n o g n) xs"
  by (induct xs arbitrary: n) auto

lemma map_index'_append[simp]: "map_index' n f (a@b) 
  = map_index' n f a @ map_index' (n + length a) f b"
  by (induct a arbitrary: n) auto

lemma map_index_append[simp]: "map_index f (a@b) 
  = map_index f a @ map_index' (length a) f b"
  using map_index'_append[where n=0]
  by (simp del: map_index'_append)

text {* Insert at index *}

primrec insert_nth :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_nth 0 x xs = x # xs"
| "insert_nth (Suc n) x xs = (case xs of [] \<Rightarrow> [x] | y # ys \<Rightarrow> y # insert_nth n x ys)"

lemma insert_nth_take_drop[simp]: "insert_nth n x xs = take n xs @ [x] @ drop n xs"
proof (induct n arbitrary: xs)
  case Suc thus ?case by (cases xs) auto
qed simp

lemma length_insert_nth: "length (insert_nth n x xs) = Suc (length xs)"
  by (induct xs) auto

lemma length_fold_insert_nth:
  "length (fold (\<lambda>(p, b). insert_nth p b) pbs bs) = length bs + length pbs"
  by (induct pbs arbitrary: bs) auto

lemma invar_fold_insert_nth:
  "\<lbrakk>\<forall>x\<in>set pbs. p < fst x; p < length bs; bs ! p = b\<rbrakk> \<Longrightarrow>
    fold (\<lambda>(x, y). insert_nth x y) pbs bs ! p = b"
  by (induct pbs arbitrary: bs) (auto simp: nth_append)

lemma nth_fold_insert_nth:
  "\<lbrakk>sorted (map fst pbs); distinct (map fst pbs); \<forall>(p, b) \<in> set pbs. p < length bs + length pbs;
    i < length pbs; pbs ! i = (p, b)\<rbrakk> \<Longrightarrow>
  fold (\<lambda>(p, b). insert_nth p b) pbs bs ! p = b"
proof (induct pbs arbitrary: bs i p b)
  case (Cons pb pbs)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems have "p < Suc (length bs)"
    proof (induct pbs rule: rev_induct)
      case (snoc pb' pbs)
      then obtain p' b' where "pb' = (p', b')" by auto
      with snoc.prems have "\<forall>p \<in> fst ` set pbs. p < p'" "p' \<le> Suc (length bs + length pbs)"
        by (auto simp: image_iff sorted_Cons sorted_append le_eq_less_or_eq)
      with snoc.prems show ?case by (intro snoc(1)) (auto simp: sorted_Cons sorted_append)
    qed auto
    with 0 Cons.prems show ?thesis unfolding fold.simps o_apply
    by (intro invar_fold_insert_nth) (auto simp: sorted_Cons image_iff le_eq_less_or_eq nth_append)
  next
    case (Suc n) with Cons.prems show ?thesis unfolding fold.simps
      by (auto intro!: Cons(1) simp: sorted_Cons)
  qed
qed simp


text {* Product of lists *}

primrec combinatorial_product :: "'a list list \<Rightarrow> 'a list list" where
  "combinatorial_product [] = [[]]"
| "combinatorial_product (xs # xss) = List.maps (\<lambda>x. map (Cons x) (combinatorial_product xss)) xs"

abbreviation "bool_combinatorial_product n \<equiv> combinatorial_product (replicate n [True, False])"

lemma set_bool_combinatorial_product[simp]:
  "bs \<in> set (bool_combinatorial_product n) \<longleftrightarrow> length bs = n"
proof (induct bs arbitrary: n)
  case Nil thus ?case by (cases n) (auto simp: maps_def)
next
  case (Cons b bs) thus ?case by (cases n) (auto simp: maps_def)
qed

text {* More on sort & remdups *}

declare set_insort[simp]

lemma insort_remdups[simp]: "\<lbrakk>sorted xs; a \<notin> set xs\<rbrakk> \<Longrightarrow> insort a (remdups xs) = remdups (insort a xs)"
proof (induct xs)
  case (Cons x xs) thus ?case by (cases xs) (auto simp: sorted_Cons)
qed simp

lemma remdups_insort[simp]: "\<lbrakk>sorted xs; a \<in> set xs\<rbrakk> \<Longrightarrow> remdups (insort a xs) = remdups xs"
  by (induct xs) (auto simp: sorted_Cons)

lemma sort_remdups[simp]: "sort (remdups xs) = remdups (sort xs)"
  by (induct xs) auto

lemma sort_map_insort[simp]: "sorted xs \<Longrightarrow> sort (map f (insort a xs)) = insort (f a) (sort (map f xs))"
  by (induct xs) (auto simp: sorted_Cons insort_left_comm)

lemma sort_map_sort[simp]: "sort (map f (sort xs)) = sort (map f xs)"
  by (induct xs) auto

lemma remdups_append: "remdups (xs @ ys) = remdups (filter (\<lambda>x. x \<notin> set ys) xs) @ remdups ys"
  by (induct xs) auto

lemma remdups_concat_map_remdups:
  "remdups (concat (map f (remdups xs))) = remdups (concat (map f xs))"
  by (induct xs) (auto simp: remdups_append filter_empty_conv)

(*multisets only needed below*)
lemma multiset_concat_gen: "M + mset (concat xs) = fold (\<lambda>x M. M + mset x) xs M"
  by (induct xs arbitrary: M) (auto, metis union_assoc)

corollary multiset_concat: "mset (concat xs) = fold (\<lambda>x M. M + mset x) xs {#}"
  using multiset_concat_gen[of "{#}" xs] by simp

lemma fold_mset_insort[simp]: "fold (\<lambda>x M. M + mset (f x)) (insort x xs) M =
  fold (\<lambda>x M. M + mset (f x)) xs (mset (f x) + M)"
  by (induct xs arbitrary: M) (auto simp: ac_simps)

lemma fold_mset_sort[simp]:
  "fold (\<lambda>x M. M + mset (f x)) (sort xs) M = fold (\<lambda>x M. M + mset (f x)) xs M"
  by (induct xs arbitrary: M) (auto simp: ac_simps)

lemma multiset_concat_map_sort[simp]:
  "mset (concat (map f (sort xs))) = mset (concat (map f xs))"
  by (auto simp: multiset_concat fold_map o_def)

lemma sort_concat_map_sort[simp]: "sort (concat (map f (sort xs))) = sort (concat (map f xs))"
  by (auto intro: properties_for_sort)

end
