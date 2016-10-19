theory List_Group
imports Sort_Descending
begin

section\<open>List Group\<close>

function (sequential) list_group_eq :: "'a list \<Rightarrow> 'a list list" where
  "list_group_eq [] = []" |
  "list_group_eq (x#xs) = [x # takeWhile (op = x) xs] @ list_group_eq (dropWhile (op = x) xs)"
by pat_completeness auto
termination list_group_eq
apply (relation "measure (\<lambda>N. length N )")
apply(simp_all add: le_imp_less_Suc length_dropWhile_le)
done

value "list_group_eq [1::int,2,2,2,3,1,4,5,5,5]"


function (sequential) list_group_eq_key :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "list_group_eq_key _ [] = []" |
  "list_group_eq_key f (x#xs) = [x # takeWhile (\<lambda>y. f x = f y) xs] @ list_group_eq_key f (dropWhile (\<lambda>y. f x = f y) xs)"
by pat_completeness auto
termination list_group_eq_key
apply (relation "measure (\<lambda>(f,N). length N )")
apply(simp_all add: le_imp_less_Suc length_dropWhile_le)
done

value "list_group_eq_key fst [(1::int, ''''), (2,''a''), (2,''b''), (2, ''c''), (3, ''c''), (1,''''), (4,'''')]"

lemma "list_group_eq_key id xs = list_group_eq xs"
apply(induction xs rule: list_group_eq.induct)
 by(simp_all add: id_def)

(*
lemma "sorted (map f (x#xs)) \<Longrightarrow> list_group_eq_key f (x#xs) = [x # filter (\<lambda>y. f x = f y) xs] @ list_group_eq_key f (filter (\<lambda>y. f x \<noteq> f y) xs)"
  apply(simp)
  oops
lemma "sorted (x#xs) \<Longrightarrow> distinct (list_group_eq_key f (x#xs)) \<Longrightarrow> distinct (list_group_eq_key f xs)"
  apply(induction xs)
   apply(simp)
oops
*)

end
