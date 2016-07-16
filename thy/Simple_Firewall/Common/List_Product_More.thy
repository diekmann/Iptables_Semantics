section\<open>List Product Helpers\<close>
theory List_Product_More
imports Main
begin

(*TODO: this definition could also go to Main*)
lemma List_product_concat_map: "List.product xs ys = concat (map (\<lambda>x. map (\<lambda>y. (x,y)) ys) xs)"
  by(induction xs) (simp)+


definition all_pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "all_pairs xs \<equiv> concat (map (\<lambda>x. map (\<lambda>y. (x,y)) xs) xs)"

lemma all_pairs_list_product: "all_pairs xs = List.product xs xs"
  by(simp add: all_pairs_def List_product_concat_map)
  
lemma all_pairs: "\<forall> (x,y) \<in> (set xs \<times> set xs). (x,y) \<in> set (all_pairs xs)"
  by(simp add: all_pairs_list_product)

lemma all_pairs_set: "set (all_pairs xs) = set xs \<times> set xs"
  by(simp add: all_pairs_list_product)

end