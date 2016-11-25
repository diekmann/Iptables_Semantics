theory WordInterval_Sorted
imports WordInterval
        "../Automatic_Refinement/Lib/Misc" (*Mergesort. TODO: dependnecy! we need a mergesort afp entry!!*)
        "~~/src/HOL/Library/Product_Lexorder"
begin


(*has afp mergesort dependency*)
text\<open>Use this and @{thm wordinterval_compress} before pretty-printing.\<close>
definition wordinterval_sort :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
  "wordinterval_sort w \<equiv> l2wi (mergesort_remdups (wi2l w))"

lemma wordinterval_sort: "wordinterval_to_set (wordinterval_sort w) = wordinterval_to_set w"
  by (simp add: wordinterval_sort_def wi2l l2wi mergesort_remdups_correct)

(*A wordinterval is essentially a tree.
  We could vastly improve the computational complexity for all operations!*)


end