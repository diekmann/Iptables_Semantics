section\<open>Miscellaneous List Lemmas\<close>
theory List_Misc
imports Main
begin

lemma list_app_singletonE:
  assumes "rs\<^sub>1 @ rs\<^sub>2 = [x]"
  obtains (first) "rs\<^sub>1 = [x]" "rs\<^sub>2 = []"
        | (second) "rs\<^sub>1 = []" "rs\<^sub>2 = [x]"
using assms
by (cases "rs\<^sub>1") auto

lemma list_app_eq_cases:
  assumes "xs\<^sub>1 @ xs\<^sub>2 = ys\<^sub>1 @ ys\<^sub>2"
  obtains (longer)  "xs\<^sub>1 = take (length xs\<^sub>1) ys\<^sub>1" "xs\<^sub>2 = drop (length xs\<^sub>1) ys\<^sub>1 @ ys\<^sub>2"
        | (shorter) "ys\<^sub>1 = take (length ys\<^sub>1) xs\<^sub>1" "ys\<^sub>2 = drop (length ys\<^sub>1) xs\<^sub>1 @ xs\<^sub>2"
using assms by (cases "length xs\<^sub>1 \<le> length ys\<^sub>1") (metis append_eq_append_conv_if)+

lemma empty_concat: "concat (map (\<lambda>x. []) ms) = []" by simp
end
