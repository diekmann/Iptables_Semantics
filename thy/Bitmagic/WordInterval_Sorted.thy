theory WordInterval_Sorted
imports WordInterval
        "../afp/Mergesort" (*TODO: dependnecy! import from afp directly!*)
begin


(*TODO: has afp mergesort dependency*)
definition wordinterval_sort :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
  "wordinterval_sort w \<equiv> l2br (mergesort_remdups (br2l w))"

lemma wordinterval_sort: "wordinterval_to_set (wordinterval_sort w) = wordinterval_to_set w"
  by (simp add: wordinterval_sort_def br2l l2br mergesort_remdups_correct)


end