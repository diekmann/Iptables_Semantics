(*  Title:      WordInterval.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory WordInterval
imports Main
  Word_Next
  NumberWang
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

section{*WordInterval: Intervals of consecutive words*}

value "(2::nat) < 2^32" (*without Code_Target_Nat, this would be really slow*)

subsection{*Syntax*}
declare[[typedef_overloaded]]
  datatype ('a::len0) wordinterval = WordInterval
                                        "('a::len0) word" --"start (inclusive)"
                                        "('a::len0) word" --"end (inclusive)"
                                  | RangeUnion "'a wordinterval" "'a wordinterval"

subsection{*Semantics*}
  fun wordinterval_to_set :: "'a::len0 wordinterval \<Rightarrow> ('a::len0 word) set" where
    "wordinterval_to_set (WordInterval start end) = {start .. end}" |
    "wordinterval_to_set (RangeUnion r1 r2) = (wordinterval_to_set r1) \<union> (wordinterval_to_set r2)"

subsection{*Basic operations*}
  fun wordinterval_element :: "'a::len0 word \<Rightarrow> 'a::len0 wordinterval \<Rightarrow> bool" where
    "wordinterval_element el (WordInterval s e) = (s \<le> el \<and> el \<le> e)" |
    "wordinterval_element el (RangeUnion r1 r2) = (wordinterval_element el r1 \<or> wordinterval_element el r2)"
  lemma wordinterval_element_set_eq[simp]: "wordinterval_element el rg = (el \<in> wordinterval_to_set rg)"
    by(induction rg rule: wordinterval_element.induct) simp_all
  
  definition wordinterval_union :: "'a::len0 wordinterval \<Rightarrow> 'a::len0 wordinterval \<Rightarrow> 'a::len0 wordinterval" where 
    "wordinterval_union r1 r2 = RangeUnion r1 r2"
  lemma wordinterval_union_set_eq[simp]: "wordinterval_to_set (wordinterval_union r1 r2) = wordinterval_to_set r1 \<union> wordinterval_to_set r2"
    unfolding wordinterval_union_def by simp
  
  fun wordinterval_empty :: "'a::len0 wordinterval \<Rightarrow> bool" where
    "wordinterval_empty (WordInterval s e) = (e < s)" |
    "wordinterval_empty (RangeUnion r1 r2) = (wordinterval_empty r1 \<and> wordinterval_empty r2)"
  lemma wordinterval_empty_set_eq[simp]: "wordinterval_empty r \<longleftrightarrow> wordinterval_to_set r = {}"
    by(induction r) auto
  

  (*len, not len0*)
  definition Empty_WordInterval :: "'a::len wordinterval" where "Empty_WordInterval \<equiv> WordInterval 1 0"
  lemma wordinterval_empty_Empty_WordInterval: "wordinterval_empty Empty_WordInterval"
    by(simp add: Empty_WordInterval_def)
  lemma Empty_WordInterval_set_eq[simp]: "wordinterval_to_set Empty_WordInterval = {}"
    by(simp add: Empty_WordInterval_def)



subsection{*WordInterval and Lists*}
  text{*A list of @{text "(start, end)"} tuples.*}

  fun br2l :: "'a::len0 wordinterval \<Rightarrow> ('a::len0 word \<times> 'a::len0 word) list" where
    "br2l (RangeUnion r1 r2) = br2l r1 @ br2l r2" |
    "br2l (WordInterval s e) = (if e < s then [] else [(s,e)])"
  
  fun l2br :: "('a::len word \<times> 'a word) list \<Rightarrow> 'a wordinterval" where
    "l2br [] = Empty_WordInterval" | 
    "l2br [(s,e)] = (WordInterval s e)" | 
    "l2br ((s,e)#rs) = (RangeUnion (WordInterval s e) (l2br rs))"
  

  lemma l2br_append: "wordinterval_to_set (l2br (l1@l2)) = wordinterval_to_set (l2br l1) \<union> wordinterval_to_set (l2br l2)"
    proof(induction l1 arbitrary: l2 rule:l2br.induct)
    case 1 thus ?case by simp
    next
    case (2 s e l2) thus ?case by (cases l2) simp_all
    next
    case 3 thus ?case by force
    qed
  
  lemma l2br_br2l: "wordinterval_to_set (l2br (br2l r)) = wordinterval_to_set r"
    by(induction r) (simp_all add: l2br_append)

  lemma l2br: "wordinterval_to_set (l2br l) = (\<Union> (i,j) \<in> set l. {i .. j})"
    by(induction l rule: l2br.induct, simp_all)

  lemma br2l: "(\<Union>(i,j)\<in>set (br2l r). {i .. j}) = wordinterval_to_set r"
    by(induction r rule: br2l.induct, simp_all)

  lemma l2br_remdups: "wordinterval_to_set (l2br (remdups ls)) = wordinterval_to_set (l2br ls)"
    by(simp add: l2br)



subsection{*Optimizing and minimizing @{typ "('a::len0) wordinterval"}s*}
text{*Removing empty intervals*}
context
begin
  fun wordinterval_optimize_empty where
    "wordinterval_optimize_empty (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1 in (let r2o = wordinterval_optimize_empty r2 in (
      if wordinterval_empty r1o then r2o else (if wordinterval_empty r2o then r1o else (RangeUnion r1o r2o)))))" |
    "wordinterval_optimize_empty r = r"
  lemma wordinterval_optimize_empty_set_eq[simp]: "wordinterval_to_set (wordinterval_optimize_empty r) = wordinterval_to_set r"
    by(induction r) (simp_all add: Let_def)

  lemma wordinterval_optimize_empty_double: "wordinterval_optimize_empty (wordinterval_optimize_empty r) = wordinterval_optimize_empty r"
    by(induction r) (simp_all add: Let_def)

  private fun wordinterval_empty_shallow where
    "wordinterval_empty_shallow (WordInterval s e) = (e < s)" |
    "wordinterval_empty_shallow (RangeUnion _ _) = False"
  private lemma helper_optimize_shallow: "wordinterval_empty_shallow (wordinterval_optimize_empty r) = wordinterval_empty (wordinterval_optimize_empty r)"
    by(induction r) fastforce+
  private fun wordinterval_optimize_empty2 where
    "wordinterval_optimize_empty2 (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1 in (let r2o = wordinterval_optimize_empty r2 in (
      if wordinterval_empty_shallow r1o then r2o else (if wordinterval_empty_shallow r2o then r1o else (RangeUnion r1o r2o)))))" |
    "wordinterval_optimize_empty2 r = r"
  lemma wordinterval_optimize_empty_code[code_unfold]: "wordinterval_optimize_empty = wordinterval_optimize_empty2"
    by (subst fun_eq_iff, clarify, rename_tac r, induct_tac r)
       (unfold wordinterval_optimize_empty.simps wordinterval_optimize_empty2.simps Let_def helper_optimize_shallow, simp_all)
end



text{*Merging overlapping intervals*}
context
begin

  private definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
    "disjoint A B \<equiv> A \<inter> B = {}"

  private fun interval_of :: "('a::len0) word \<times> 'a word \<Rightarrow> 'a word set" where
    "interval_of (s,e) = {s .. e}"
  declare interval_of.simps[simp del]

  private definition disjoint_intervals :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool" where
    "disjoint_intervals A B \<equiv> disjoint (interval_of A) (interval_of B)"

  private definition not_disjoint_intervals :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool" where
    "not_disjoint_intervals A B \<equiv> \<not> disjoint (interval_of A) (interval_of B)"

  private lemma [code]: "not_disjoint_intervals A B = (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s \<le> e' \<and> s' \<le> e \<and> s \<le> e \<and> s' \<le> e')"
    apply(cases A, cases B)
    apply(simp add: not_disjoint_intervals_def interval_of.simps disjoint_def)
    done

  private lemma [code]: "disjoint_intervals A B = (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e')"
    apply(cases A, cases B)
    apply(simp add: disjoint_intervals_def interval_of.simps disjoint_def)
    by fastforce


  text{*BEGIN merging overlapping intervals*}
  (*result has no empty intervals and all are disjoiint. merging things such as [1,7] [8,10] would still be possible*)
  private fun merge_overlap :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list" where
   "merge_overlap s [] = [s]" |
   "merge_overlap (s,e) ((s',e')#ss) = (
      if not_disjoint_intervals (s,e) (s',e')
      then (min s s', max e e')#ss
      else (s',e')#merge_overlap (s,e) ss)"

  private lemma not_disjoint_union:
      fixes s :: "('a::len0) word"
      shows "\<not> disjoint {s..e} {s'..e'} \<Longrightarrow> {s..e} \<union> {s'..e'} = {min s s' .. max e e'}"
    by(auto simp add: disjoint_def min_def max_def)

  private lemma disjoint_subset: "disjoint A B \<Longrightarrow> A \<subseteq> B \<union> C \<Longrightarrow> A \<subseteq> C"
    unfolding disjoint_def
    by blast

  private lemma merge_overlap_helper1: "interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s) \<Longrightarrow>
      (\<Union>s \<in> set (merge_overlap A ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply blast
    apply(drule_tac C="(\<Union>x\<in>set xs. interval_of x)" in disjoint_subset)
     apply(simp_all)
    done

  private lemma merge_overlap_helper2: "\<exists>s'\<in>set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow>
          interval_of A \<union> (\<Union>s \<in> set ss. interval_of s) = (\<Union>s \<in> set (merge_overlap A ss). interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply blast
    apply(simp)
    by blast

  private lemma merge_overlap_length: "\<exists>s' \<in> set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow> length (merge_overlap A ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    done

  value[code] "merge_overlap (1:: 16 word,2)"

  private function listwordinterval_compress :: "(('a::len0) word \<times> ('a::len0) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
    "listwordinterval_compress [] = []" |
    "listwordinterval_compress (s#ss) = (
            if \<forall>s' \<in> set ss. disjoint_intervals s s'
            then s#listwordinterval_compress ss
            else listwordinterval_compress (merge_overlap s ss))"
  by(pat_completeness, auto)

  private termination listwordinterval_compress
  apply (relation "measure length")
    apply(rule wf_measure)
   apply(simp)
  using disjoint_intervals_def merge_overlap_length by fastforce

  private lemma listwordinterval_compress: "(\<Union>s \<in> set (listwordinterval_compress ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp)
    apply(intro impI)
    apply(simp add: disjoint_intervals_def)
    apply(drule merge_overlap_helper2)
    apply(simp)
    done

  value[code] "listwordinterval_compress [(1::32 word,3), (8,10), (2,5), (3,7)]"

  private lemma A_in_listwordinterval_compress: "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s)"
    using listwordinterval_compress by blast

  private lemma listwordinterval_compress_disjoint: 
    "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> B \<in> set (listwordinterval_compress ss) \<Longrightarrow> A \<noteq> B \<Longrightarrow> disjoint (interval_of A) (interval_of B)"
    apply(induction ss arbitrary: rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp split: split_if_asm)
    apply(elim disjE)
       apply(simp_all)
     apply(simp_all add: disjoint_intervals_def disjoint_def)
     apply(thin_tac [!] "False \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
     apply(blast dest: A_in_listwordinterval_compress)+
    done
  text{*END merging overlapping intervals*}




  text{*BEGIN merging adjacent intervals*}
  private fun merge_adjacent :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list" where
     "merge_adjacent s [] = [s]" |
     "merge_adjacent (s,e) ((s',e')#ss) = (
        if s \<le>e \<and> s' \<le> e' \<and> word_next e = s'
        then (s, e')#ss
        else if s \<le>e \<and> s' \<le> e' \<and> word_next e' = s
        then (s', e)#ss
        else (s',e')#merge_adjacent (s,e) ss)"

  private lemma merge_adjacent_helper: 
  "interval_of A \<union> (\<Union>s \<in> set ss. interval_of s) = (\<Union>s \<in> set (merge_adjacent A ss). interval_of s)"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add:  interval_of.simps)
    apply(intro impI conjI)
       apply (metis Un_assoc word_adjacent_union)
      apply(elim conjE)
      apply(drule(2) word_adjacent_union)
      apply(blast)
     using word_adjacent_union apply blast
    by blast

  private lemma merge_adjacent_length: "\<exists>(s', e')\<in>set ss. s \<le> e \<and> s' \<le> e' \<and> (word_next e = s' \<or> word_next e' = s)
     \<Longrightarrow> length (merge_adjacent (s,e) ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(case_tac x)
    apply(simp add: )
    by blast

  private function listwordinterval_adjacent :: "(('a::len) word \<times> ('a::len) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
    "listwordinterval_adjacent [] = []" |
    "listwordinterval_adjacent ((s,e)#ss) = (
            if \<forall>(s',e') \<in> set ss. \<not> (s \<le>e \<and> s' \<le> e' \<and> (word_next e = s' \<or> word_next e' = s))
            then (s,e)#listwordinterval_adjacent ss
            else listwordinterval_adjacent (merge_adjacent (s,e) ss))"
  by(pat_completeness, auto)

  private termination listwordinterval_adjacent
  apply (relation "measure length")
    apply(rule wf_measure)
   apply(simp)
  apply(simp)
  using merge_adjacent_length by fastforce

  private lemma listwordinterval_adjacent: "(\<Union>s \<in> set (listwordinterval_adjacent ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss rule: listwordinterval_adjacent.induct)
     apply(simp)
    apply(simp add: merge_adjacent_helper)
    done

  value[code] "listwordinterval_adjacent [(1::16 word, 3), (5, 10), (10,10), (4,4)]"
  text{*END merging adjacent intervals*}


  definition wordinterval_compress :: "('a::len) wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_compress r \<equiv> l2br (remdups (listwordinterval_adjacent (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))))"

  lemma wordinterval_compress: "wordinterval_to_set (wordinterval_compress r) = wordinterval_to_set r"
    unfolding wordinterval_compress_def
    proof -
      have interval_of': "\<And>s. interval_of s = (case s of (s,e) \<Rightarrow> {s .. e})" apply(case_tac s) using interval_of.simps by simp

      have "wordinterval_to_set (l2br (remdups (listwordinterval_adjacent (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))))) =
            (\<Union>x\<in>set (listwordinterval_adjacent (listwordinterval_compress (br2l (wordinterval_optimize_empty r)))). interval_of x)"
      using l2br l2br_remdups interval_of.simps[symmetric] by blast
      also have "\<dots> =  (\<Union>s\<in>set (br2l (wordinterval_optimize_empty r)). interval_of s)"
        by(simp add: listwordinterval_compress listwordinterval_adjacent)
      also have "\<dots> = (\<Union>(i, j)\<in>set (br2l (wordinterval_optimize_empty r)). {i..j})" by(simp add: interval_of')
      also have "\<dots> = wordinterval_to_set r" by(simp add: br2l)
      finally show "wordinterval_to_set
        (l2br (remdups (listwordinterval_adjacent (listwordinterval_compress (br2l (wordinterval_optimize_empty r))))))
          = wordinterval_to_set r" .
  qed

end

lemma "wordinterval_compress (RangeUnion (RangeUnion (WordInterval (1::32 word) 5) (WordInterval 8 10)) (WordInterval 3 7)) = WordInterval 1 0xA" by eval



(*
fun wordinterval_linearize :: "('a::len) wordinterval \<Rightarrow> ('a::len) wordinterval" where
  "wordinterval_linearize rs = list_to_wordinterval (wordinterval_to_list rs)"
lemma "wordinterval_to_set (wordinterval_linearize r) = wordinterval_to_set r"
  by(simp, metis list_to_wordinterval_set_eq wordinterval_to_list_set_eq)
*)

(*TODO: remove this*)
(*
fun wordinterval_optimize_same where "wordinterval_optimize_same rs = list_to_wordinterval (remdups (wordinterval_to_list rs))"
lemma wordinterval_optimize_same_set_eq[simp]: "wordinterval_to_set (wordinterval_optimize_same rs) = wordinterval_to_set rs"
 by(simp, subst list_to_wordinterval_set_eq) (metis image_set wordinterval_to_list_set_eq set_remdups)
*)


subsection{*Further operations*}

  text{*@{text "\<Union>"}*}
  definition wordinterval_Union :: "('a::len) wordinterval list \<Rightarrow> 'a wordinterval" where
    "wordinterval_Union ws = wordinterval_compress (foldr wordinterval_union ws Empty_WordInterval)"
  
  lemma wordinterval_Union: "wordinterval_to_set (wordinterval_Union ws) = (\<Union> w \<in> (set ws). wordinterval_to_set w)"
    by(induction ws) (simp_all add: wordinterval_compress wordinterval_Union_def)
   


context
begin
  private fun wordinterval_setminus' :: "'a::len wordinterval \<Rightarrow> 'a wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_setminus' (WordInterval s e) (WordInterval ms me) = (
      if s > e \<or> ms > me then WordInterval s e else
      if me \<ge> e
        then
          WordInterval (if ms = 0 then 1 else s) (min e (word_prev ms))
        else if ms \<le> s
        then
          WordInterval (max s (word_next me)) (if me = max_word then 0 else e)
        else
          RangeUnion (WordInterval (if ms = 0 then 1 else s) (word_prev ms)) (WordInterval (word_next me) (if me = max_word then 0 else e))
        )" |
     "wordinterval_setminus' (RangeUnion r1 r2) t = RangeUnion (wordinterval_setminus' r1 t) (wordinterval_setminus' r2 t)"|
     "wordinterval_setminus' t (RangeUnion r1 r2) = wordinterval_setminus' (wordinterval_setminus' t r1) r2"

  private lemma wordinterval_setminus'_rr_set_eq: "wordinterval_to_set(wordinterval_setminus' (WordInterval s e) (WordInterval ms me)) = 
    wordinterval_to_set (WordInterval s e) - wordinterval_to_set (WordInterval ms me)"
     apply(simp only: wordinterval_setminus'.simps)
     apply(case_tac "e < s") 
      apply simp
     apply(case_tac "me < ms") 
      apply simp
     apply(case_tac [!] "e \<le> me")
      apply(case_tac [!] "ms = 0") 
        apply(case_tac [!] "ms \<le> s") 
            apply(case_tac [!] "me = max_word")
                    apply(simp_all add: word_prev_def word_next_def min_def max_def)
            apply(safe)
                                  apply(auto)
                          apply(uint_arith) 
                         apply(uint_arith)
                        apply(uint_arith)
                       apply(uint_arith)
                      apply(uint_arith)
                     apply(uint_arith)
                    apply(uint_arith)
                   apply(uint_arith)
                  apply(uint_arith)
                 apply(uint_arith)
                apply(uint_arith)
               apply(uint_arith)
              apply(uint_arith)
             apply(uint_arith)
            apply(uint_arith)
           apply(uint_arith)
          apply(uint_arith)
         apply(uint_arith)
        apply(uint_arith)
       apply(uint_arith)
      apply(uint_arith)
     apply(uint_arith)
   done

  private lemma wordinterval_setminus'_set_eq: "wordinterval_to_set (wordinterval_setminus' r1 r2) = 
    wordinterval_to_set r1 - wordinterval_to_set r2"
    apply(induction rule: wordinterval_setminus'.induct)
      using wordinterval_setminus'_rr_set_eq apply blast
     apply auto
    done
  lemma wordinterval_setminus'_empty_struct: "wordinterval_empty r2 \<Longrightarrow> wordinterval_setminus' r1 r2 = r1"
    by(induction r1 r2 rule: wordinterval_setminus'.induct) auto


  definition wordinterval_setminus :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_setminus r1 r2 = wordinterval_compress (wordinterval_setminus' r1 r2)"

  lemma wordinterval_setminus_set_eq[simp]: "wordinterval_to_set (wordinterval_setminus r1 r2) = 
    wordinterval_to_set r1 - wordinterval_to_set r2"
    by(simp add: wordinterval_setminus_def wordinterval_compress wordinterval_setminus'_set_eq)
end

definition wordinterval_UNIV :: "'a::len wordinterval"where "wordinterval_UNIV \<equiv> WordInterval 0 max_word"
lemma wordinterval_UNIV_set_eq[simp]: "wordinterval_to_set wordinterval_UNIV = UNIV"
  unfolding wordinterval_UNIV_def
  using max_word_max by fastforce
  
fun wordinterval_invert :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
  "wordinterval_invert r = wordinterval_setminus wordinterval_UNIV r"
lemma wordinterval_invert_set_eq[simp]: "wordinterval_to_set (wordinterval_invert r) = UNIV - wordinterval_to_set r" by(auto)

lemma wordinterval_invert_UNIV_empty: "wordinterval_empty (wordinterval_invert wordinterval_UNIV)" by simp


text{*@{text "\<inter>"}*}
context
begin
  private lemma "{(s::nat) .. e} \<inter> {s' .. e'} = {} \<longleftrightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e'"
    by simp linarith
  private fun wordinterval_intersection' :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_intersection' (WordInterval s e) (WordInterval s' e') = (
        if s > e \<or> s' > e' \<or> s > e' \<or> s' > e \<or> s > e \<or> s' > e'
        then
          Empty_WordInterval
        else
          WordInterval (max s s') (min e e')
        )" |
    "wordinterval_intersection' (RangeUnion r1 r2) t = RangeUnion (wordinterval_intersection' r1 t) (wordinterval_intersection' r2 t)"|
    "wordinterval_intersection' t (RangeUnion r1 r2) = RangeUnion (wordinterval_intersection' t r1) (wordinterval_intersection' t r2)"

  private lemma wordinterval_intersection'_set_eq: 
    "wordinterval_to_set (wordinterval_intersection' r1 r2) = wordinterval_to_set r1 \<inter> wordinterval_to_set r2"
    by(induction r1 r2 rule: wordinterval_intersection'.induct) (auto)

  value[code] "wordinterval_intersection' (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10)) (WordInterval 1 3)) (WordInterval 1 3)"

  definition wordinterval_intersection :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where 
    "wordinterval_intersection r1 r2 \<equiv> wordinterval_compress (wordinterval_intersection' r1 r2)"

  lemma wordinterval_intersection_set_eq[simp]: 
    "wordinterval_to_set (wordinterval_intersection r1 r2) = wordinterval_to_set r1 \<inter> wordinterval_to_set r2"
    (*unfolding wordinterval_intersection_def wordinterval_optimize_same_set_eq by auto*)
    by(simp add: wordinterval_intersection_def wordinterval_compress wordinterval_intersection'_set_eq)

  value[code] "wordinterval_intersection (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10)) (WordInterval 1 3)) (WordInterval 1 3)"
end



(*lemma wordinterval_setminus_intersection_empty_struct_rr: 
  "wordinterval_empty (wordinterval_intersection (WordInterval r1s r1e) (WordInterval r2s r2e)) \<Longrightarrow> 
  wordinterval_setminus (WordInterval r1s r1e) (WordInterval r2s r2e) = (WordInterval r1s r1e)"
  apply(subst(asm) wordinterval_empty_set_eq) 
  apply(subst(asm) wordinterval_intersection_set_eq)
  apply(unfold wordinterval_to_set.simps(1))
  apply(cases "wordinterval_empty (WordInterval r1s r1e)", case_tac [!] "wordinterval_empty (WordInterval r2s r2e)")
     apply(unfold wordinterval_empty.simps(1))
     apply(force, force, force)
  apply(cases "r1e < r2s") 
   defer
   apply(subgoal_tac "r2e < r1s")
    defer
    apply force
   apply(simp only: wordinterval_setminus.simps)
   apply(case_tac [!] "r1e \<le> r2e", case_tac [!] "r2s \<le> r1s")
         apply(auto)
   apply (metis add.commute inc_i le_minus min_absorb1 word_le_sub1 word_prev_def word_zero_le)
  apply(metis inc_le word_next_def max.order_iff)
done*)

(*
declare wordinterval_setminus.simps(1)[simp del]
*)

(*lemma wordinterval_setminus_intersection_empty_struct:
  "wordinterval_empty (wordinterval_intersection r1 r2) \<Longrightarrow> 
  wordinterval_setminus r1 r2 = r1"
  by (induction r1 r2 rule: wordinterval_setminus.induct, auto simp add: wordinterval_setminus_intersection_empty_struct_rr) fastforce*)

definition wordinterval_subset :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where
  "wordinterval_subset r1 r2 \<equiv> wordinterval_empty (wordinterval_setminus r1 r2)"
lemma wordinterval_subset_set_eq[simp]: "wordinterval_subset r1 r2 = (wordinterval_to_set r1 \<subseteq> wordinterval_to_set r2)"
  unfolding wordinterval_subset_def by simp

definition wordinterval_eq :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where 
  "wordinterval_eq r1 r2 = (wordinterval_subset r1 r2 \<and> wordinterval_subset r2 r1)"
lemma wordinterval_eq_set_eq: "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_to_set r1 = wordinterval_to_set r2"
  unfolding wordinterval_eq_def by auto

thm iffD1[OF wordinterval_eq_set_eq]
(*declare iffD1[OF wordinterval_eq_set_eq, simp]*)

lemma wordinterval_eq_comm: "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_eq r2 r1"
  unfolding wordinterval_eq_def by fast
lemma wordinterval_to_set_alt: "wordinterval_to_set r = {x. wordinterval_element x r}"
  unfolding wordinterval_element_set_eq by blast

lemma wordinterval_un_empty: "wordinterval_empty r1 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r2"
  by(subst wordinterval_eq_set_eq, simp)
lemma wordinterval_un_emty_b: "wordinterval_empty r2 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r1"
  by(subst wordinterval_eq_set_eq, simp)

lemma wordinterval_Diff_triv: 
  "wordinterval_empty (wordinterval_intersection a b) \<Longrightarrow> wordinterval_eq (wordinterval_setminus a b) a"
  unfolding wordinterval_eq_set_eq
  by simp blast




fun wordinterval_size :: "('a::len) wordinterval \<Rightarrow> nat" where
  "wordinterval_size (RangeUnion a b) = wordinterval_size a + wordinterval_size b" |
  "wordinterval_size (WordInterval s e) = (if s \<le> e then 1 else 0)"

lemma wordinterval_size_length: "wordinterval_size r = length (br2l r)"
  by(induction r) (auto)

lemma Ex_wordinterval_nonempty: "\<exists>x::('a::len wordinterval). y \<in> wordinterval_to_set x"
proof show "y \<in> wordinterval_to_set wordinterval_UNIV" by simp qed



lemma wordinterval_eq_reflp:
  "reflp wordinterval_eq"
  apply(rule reflpI)
  by(simp only: wordinterval_eq_set_eq)
lemma wordintervalt_eq_symp:
  "symp wordinterval_eq"
  apply(rule sympI)
  by(simp add: wordinterval_eq_comm)
lemma wordinterval_eq_transp:
  "transp wordinterval_eq"
  apply(rule transpI)
  by(simp only: wordinterval_eq_set_eq)

lemma wordinterval_eq_equivp:
  "equivp wordinterval_eq"
  by (auto intro: equivpI wordinterval_eq_reflp wordintervalt_eq_symp wordinterval_eq_transp)
(*
quotient_type 'a bitrrq = "'a::len wordinterval" / "wordinterval_eq"
  by (rule wordinterval_eq_equivp)
*)




(*TODO: remove*)
(*
fun wordinterval_to_list  :: "'a::len wordinterval \<Rightarrow> ('a::len wordinterval) list" where
  "wordinterval_to_list (RangeUnion r1 r2) = wordinterval_to_list r1 @ wordinterval_to_list r2" |
  "wordinterval_to_list r = (if wordinterval_empty r then [] else [r])"

lemma wordinterval_to_list_set_eq: "(\<Union>set (map wordinterval_to_set (wordinterval_to_list rs))) = wordinterval_to_set rs"
by(induction rs) simp_all

fun list_to_wordinterval where
  "list_to_wordinterval [r] = r" |
  "list_to_wordinterval (r#rs) = (RangeUnion r (list_to_wordinterval rs))" |
  "list_to_wordinterval [] = Empty_WordInterval"

lemma list_to_wordinterval_set_eq: "wordinterval_to_set (list_to_wordinterval rs) = (\<Union>set (map wordinterval_to_set rs)) "
  by(induction rs rule: list_to_wordinterval.induct) simp_all

lemma list_to_wordinterval_set_eq_simp[simp]: "wordinterval_to_set (list_to_wordinterval (a # as)) = wordinterval_to_set (wordinterval_union a (list_to_wordinterval as))"
  by(cases as) auto
  

fun wordinterval_is_simple where "wordinterval_is_simple (WordInterval _ _) = True" | "wordinterval_is_simple (RangeUnion _ _) = False"
fun wordintervalist_union_free where
  "wordintervalist_union_free (r#rs) = (wordinterval_is_simple r \<and> wordintervalist_union_free rs)" |
  "wordintervalist_union_free [] = True"
lemma wordintervalist_union_freeX: "wordintervalist_union_free (r # rs) \<Longrightarrow> \<exists> s e. r = WordInterval s e"
  by (induction rs) (cases r, simp, simp)+
lemma wordintervalist_union_free_append: "wordintervalist_union_free (a@b) = (wordintervalist_union_free a \<and> wordintervalist_union_free b)"
  by (induction a) (auto)
lemma wordinterval_to_list_union_free: "l = wordinterval_to_list r \<Longrightarrow> wordintervalist_union_free l"
  by(induction r arbitrary: l) (simp_all add: wordintervalist_union_free_append)
*)



 definition is_lowest_element :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_lowest_element x S = (x \<in> S \<and> (\<forall>y\<in>S. y \<le> x \<longrightarrow> y = x))"
    
  fun wordinterval_lowest_element :: "'a::len0 wordinterval \<Rightarrow> 'a word option" where
    "wordinterval_lowest_element (WordInterval s e) = (if s \<le> e then Some s else None)" | 
    "wordinterval_lowest_element (RangeUnion A B) = (case (wordinterval_lowest_element A, wordinterval_lowest_element B) of
      (Some a, Some b) \<Rightarrow> Some (if a < b then a else b) |
      (None, Some b) \<Rightarrow> Some b |
      (Some a, None) \<Rightarrow> Some a |
      (None, None) \<Rightarrow> None)"

  lemma wordinterval_lowest_none_empty: "wordinterval_lowest_element r = None \<longleftrightarrow> wordinterval_empty r"
    proof(induction r)
    case WordInterval thus ?case by simp
    next
    case RangeUnion thus ?case by fastforce
    qed
    

  lemma wordinterval_lowest_element_correct_A: "wordinterval_lowest_element r = Some x \<Longrightarrow> is_lowest_element x (wordinterval_to_set r)"
    unfolding is_lowest_element_def
    apply(induction r arbitrary: x rule: wordinterval_lowest_element.induct)
     apply(rename_tac rs re x, case_tac "rs \<le> re", auto)[1]
    apply(subst(asm) wordinterval_lowest_element.simps(2))
    apply(rename_tac A B x)
    apply(case_tac     "wordinterval_lowest_element B")
     apply(case_tac[!] "wordinterval_lowest_element A")
       apply(simp_all add: wordinterval_lowest_none_empty)[3]
    apply fastforce
  done


  lemma wordinterval_lowest_element_set_eq: assumes "\<not> wordinterval_empty r"
    shows "(wordinterval_lowest_element r = Some x) = (is_lowest_element x (wordinterval_to_set r))"
    (*unfolding is_lowest_element_def*)
    proof(rule iffI)
      assume "wordinterval_lowest_element r = Some x"
      thus "is_lowest_element x (wordinterval_to_set r)"
     using wordinterval_lowest_element_correct_A wordinterval_lowest_none_empty by simp
    next
      assume "is_lowest_element x (wordinterval_to_set r)"
      with assms show "(wordinterval_lowest_element r = Some x)"
        proof(induction r arbitrary: x rule: wordinterval_lowest_element.induct)
        case 1 thus ?case by(simp add: is_lowest_element_def)
        next
        case (2 A B x)

        have is_lowest_RangeUnion: "is_lowest_element x (wordinterval_to_set A \<union> wordinterval_to_set B) \<Longrightarrow> 
          is_lowest_element x (wordinterval_to_set A) \<or> is_lowest_element x (wordinterval_to_set B)"
          by(simp add: is_lowest_element_def)
      
         (*why \<And> A B?*)
         have wordinterval_lowest_element_RangeUnion: "\<And>a b A B. wordinterval_lowest_element A = Some a \<Longrightarrow> wordinterval_lowest_element B = Some b \<Longrightarrow>
                  wordinterval_lowest_element (RangeUnion A B) = Some (min a b)"
           by(auto dest!: wordinterval_lowest_element_correct_A simp add: is_lowest_element_def min_def)
         
        from 2 show ?case
        apply(case_tac     "wordinterval_lowest_element B")
         apply(case_tac[!] "wordinterval_lowest_element A")
           apply(auto simp add: is_lowest_element_def)[3]
        apply(subgoal_tac "\<not> wordinterval_empty A \<and> \<not> wordinterval_empty B")
         prefer 2
         using arg_cong[where f = Not, OF wordinterval_lowest_none_empty] apply blast
        apply(drule(1) wordinterval_lowest_element_RangeUnion)
        apply(simp split: option.split_asm add: min_def)
         apply(drule is_lowest_RangeUnion)
         apply(elim disjE)
          apply(simp add: is_lowest_element_def)
         apply(clarsimp simp add: wordinterval_lowest_none_empty)
        
        apply(simp add: is_lowest_element_def)
        apply(clarsimp simp add: wordinterval_lowest_none_empty)
        using wordinterval_lowest_element_correct_A[simplified is_lowest_element_def]
        by (metis Un_iff not_le)
      qed
    qed
   
    
end
