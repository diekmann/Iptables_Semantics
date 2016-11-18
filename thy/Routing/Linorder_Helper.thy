text_raw\<open>\section*{Sorting a list by two keys}\<close>
theory Linorder_Helper
imports Main
begin

text\<open>Sorting is fun...\<close>

text\<open>The problem is that Isabelle does not have anything like \texttt{sortBy}, only @{const sort_key}.
This means that there is no way to sort something based on two properties, with one being infinitely more important.\<close>

text\<open>Enter this:\<close>

datatype ('a,'b) linord_helper = LinordHelper 'a 'b

instantiation linord_helper :: (linorder, linorder) linorder
begin                                  
  definition "linord_helper_less_eq1 a b \<equiv> (case a of LinordHelper a1 a2 \<Rightarrow> case b of LinordHelper b1 b2 \<Rightarrow> a1 < b1 \<or> a1 = b1 \<and> a2 \<le> b2)"
	definition "a \<le> b \<longleftrightarrow> linord_helper_less_eq1 a b"
	definition "a < b \<longleftrightarrow> (a \<noteq> b \<and> linord_helper_less_eq1 a b)"
instance
by standard (auto simp: linord_helper_less_eq1_def less_eq_linord_helper_def less_linord_helper_def split: linord_helper.splits)
end
lemmas linord_helper_less = less_linord_helper_def linord_helper_less_eq1_def
lemmas linord_helper_le = less_eq_linord_helper_def linord_helper_less_eq1_def

text\<open>Now, it is possible to use @{term "sort_key f"}, 
with @{term f} constructing a @{const LinordHelper} containing the two desired properties for sorting.\<close>

end