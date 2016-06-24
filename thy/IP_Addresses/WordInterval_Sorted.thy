theory WordInterval_Sorted
imports WordInterval
        "../Automatic_Refinement/Lib/Misc" (*Mergesort. TODO: dependnecy! we need a mergesort afp entry!!*)
begin


(*TODO: has afp mergesort dependency*)
definition wordinterval_sort :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
  "wordinterval_sort w \<equiv> l2wi (mergesort_remdups (wi2l w))"

lemma wordinterval_sort: "wordinterval_to_set (wordinterval_sort w) = wordinterval_to_set w"
  by (simp add: wordinterval_sort_def wi2l l2wi mergesort_remdups_correct)


end