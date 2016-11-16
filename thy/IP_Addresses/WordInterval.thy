(*  Title:      WordInterval.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory WordInterval
imports Main
  Word_Next
  "~~/src/HOL/Word/Word"
begin

section\<open>WordInterval: Executable datatype for Machine Word Sets\<close>
text\<open>Stores ranges of machine words as interval. This has been proven quite efficient for 
     IP Addresses.\<close>
(*NOTE: All algorithms here use a straight-forward implementation. There is a lot of room for 
        improving the computation complexity, for example by making the WordInterval a balanced,
        sorted tree.*)

subsection\<open>Syntax\<close>
context
  notes [[typedef_overloaded]]
begin
  datatype ('a::len0) wordinterval = WordInterval
                                        "('a::len0) word" --"start (inclusive)"
                                        "('a::len0) word" --"end (inclusive)"
                                  | RangeUnion "'a wordinterval" "'a wordinterval"
end

subsection\<open>Semantics\<close>
  fun wordinterval_to_set :: "'a::len0 wordinterval \<Rightarrow> ('a::len0 word) set"
  where
    "wordinterval_to_set (WordInterval start end) =
        {start .. end}" |
    "wordinterval_to_set (RangeUnion r1 r2) =
        wordinterval_to_set r1 \<union> wordinterval_to_set r2"

(*Note: The runtime of all the operations could be improved, for example by keeping the tree sorted
  and balanced.*)

subsection\<open>Basic operations\<close>
  text\<open>@{text \<in>}\<close>
  fun wordinterval_element :: "'a::len0 word \<Rightarrow> 'a::len0 wordinterval \<Rightarrow> bool" where
    "wordinterval_element el (WordInterval s e) \<longleftrightarrow> s \<le> el \<and> el \<le> e" |
    "wordinterval_element el (RangeUnion r1 r2) \<longleftrightarrow>
                                            wordinterval_element el r1 \<or> wordinterval_element el r2"
  lemma wordinterval_element_set_eq[simp]:
    "wordinterval_element el rg = (el \<in> wordinterval_to_set rg)"
    by(induction rg rule: wordinterval_element.induct) simp_all
  
  definition wordinterval_union
    :: "'a::len0 wordinterval \<Rightarrow> 'a::len0 wordinterval \<Rightarrow> 'a::len0 wordinterval" where 
    "wordinterval_union r1 r2 = RangeUnion r1 r2"
  lemma wordinterval_union_set_eq[simp]:
    "wordinterval_to_set (wordinterval_union r1 r2) = wordinterval_to_set r1 \<union> wordinterval_to_set r2"
    unfolding wordinterval_union_def by simp
  
  fun wordinterval_empty :: "'a::len0 wordinterval \<Rightarrow> bool" where
    "wordinterval_empty (WordInterval s e) \<longleftrightarrow> e < s" |
    "wordinterval_empty (RangeUnion r1 r2) \<longleftrightarrow> wordinterval_empty r1 \<and> wordinterval_empty r2"
  lemma wordinterval_empty_set_eq[simp]: "wordinterval_empty r \<longleftrightarrow> wordinterval_to_set r = {}"
    by(induction r) auto
  
  definition Empty_WordInterval :: "'a::len wordinterval" where
    "Empty_WordInterval \<equiv> WordInterval 1 0"
  lemma wordinterval_empty_Empty_WordInterval: "wordinterval_empty Empty_WordInterval"
    by(simp add: Empty_WordInterval_def)
  lemma Empty_WordInterval_set_eq[simp]: "wordinterval_to_set Empty_WordInterval = {}"
    by(simp add: Empty_WordInterval_def)



subsection\<open>WordInterval and Lists\<close>
  text\<open>A list of @{text "(start, end)"} tuples.\<close>

  text\<open>wordinterval to list\<close>
  fun wi2l :: "'a::len0 wordinterval \<Rightarrow> ('a::len0 word \<times> 'a::len0 word) list" where
    "wi2l (RangeUnion r1 r2) = wi2l r1 @ wi2l r2" |
    "wi2l (WordInterval s e) = (if e < s then [] else [(s,e)])"
  
  text\<open>list to wordinterval\<close>
  fun l2wi :: "('a::len word \<times> 'a word) list \<Rightarrow> 'a wordinterval" where
    "l2wi [] = Empty_WordInterval" | 
    "l2wi [(s,e)] = (WordInterval s e)" | 
    "l2wi ((s,e)#rs) = (RangeUnion (WordInterval s e) (l2wi rs))"
  

  lemma l2wi_append: "wordinterval_to_set (l2wi (l1@l2)) =
                      wordinterval_to_set (l2wi l1) \<union> wordinterval_to_set (l2wi l2)"
    proof(induction l1 arbitrary: l2 rule:l2wi.induct)
    case 1 thus ?case by simp
    next
    case (2 s e l2) thus ?case by (cases l2) simp_all
    next
    case 3 thus ?case by force
    qed
  
  lemma l2wi_wi2l: "wordinterval_to_set (l2wi (wi2l r)) = wordinterval_to_set r"
    by(induction r) (simp_all add: l2wi_append)

  lemma l2wi: "wordinterval_to_set (l2wi l) = (\<Union> (i,j) \<in> set l. {i .. j})"
    by(induction l rule: l2wi.induct, simp_all)

  lemma wi2l: "(\<Union>(i,j)\<in>set (wi2l r). {i .. j}) = wordinterval_to_set r"
    by(induction r rule: wi2l.induct, simp_all)

  lemma l2wi_remdups: "wordinterval_to_set (l2wi (remdups ls)) = wordinterval_to_set (l2wi ls)"
    by(simp add: l2wi)



subsection\<open>Optimizing and minimizing @{typ "('a::len) wordinterval"}s\<close>
text\<open>Removing empty intervals\<close>
context
begin
  fun wordinterval_optimize_empty :: "'a::len0 wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_optimize_empty (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1;
                                                           r2o = wordinterval_optimize_empty r2
      in if
        wordinterval_empty r1o
      then
        r2o
      else if
        wordinterval_empty r2o
      then
        r1o
      else
        RangeUnion r1o r2o)" |
    "wordinterval_optimize_empty r = r"
  lemma wordinterval_optimize_empty_set_eq[simp]:
    "wordinterval_to_set (wordinterval_optimize_empty r) = wordinterval_to_set r"
    by(induction r) (simp_all add: Let_def)

  lemma wordinterval_optimize_empty_double:
    "wordinterval_optimize_empty (wordinterval_optimize_empty r) = wordinterval_optimize_empty r"
    by(induction r) (simp_all add: Let_def)

  private fun wordinterval_empty_shallow :: "'a::len0 wordinterval \<Rightarrow> bool"  where
    "wordinterval_empty_shallow (WordInterval s e) \<longleftrightarrow> e < s" |
    "wordinterval_empty_shallow (RangeUnion _ _) \<longleftrightarrow> False"
  private lemma helper_optimize_shallow:
    "wordinterval_empty_shallow (wordinterval_optimize_empty r) =
      wordinterval_empty (wordinterval_optimize_empty r)"
    by(induction r) fastforce+
  private fun wordinterval_optimize_empty2 where
    "wordinterval_optimize_empty2 (RangeUnion r1 r2) = (let r1o = wordinterval_optimize_empty r1;
                                                            r2o = wordinterval_optimize_empty r2
      in if
        wordinterval_empty_shallow r1o
      then
        r2o
      else if
        wordinterval_empty_shallow r2o
      then
        r1o
      else
        RangeUnion r1o r2o)" |
    "wordinterval_optimize_empty2 r = r"
  lemma wordinterval_optimize_empty_code[code_unfold]:
    "wordinterval_optimize_empty = wordinterval_optimize_empty2"
    by (subst fun_eq_iff, clarify, rename_tac r, induct_tac r)
       (unfold wordinterval_optimize_empty.simps wordinterval_optimize_empty2.simps
               Let_def helper_optimize_shallow, simp_all)
end



text\<open>Merging overlapping intervals\<close>
context
begin

  private definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
    "disjoint A B \<equiv> A \<inter> B = {}"

  private primrec interval_of :: "('a::len0) word \<times> 'a word \<Rightarrow> 'a word set" where
    "interval_of (s,e) = {s .. e}"
  declare interval_of.simps[simp del]

  private definition disjoint_intervals
    :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool"
  where
    "disjoint_intervals A B \<equiv> disjoint (interval_of A) (interval_of B)"

  private definition not_disjoint_intervals
    :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) \<Rightarrow> bool"
  where
    "not_disjoint_intervals A B \<equiv> \<not> disjoint (interval_of A) (interval_of B)"

  private lemma [code]:
    "not_disjoint_intervals A B =
      (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s \<le> e' \<and> s' \<le> e \<and> s \<le> e \<and> s' \<le> e')"
    apply(cases A, cases B)
    apply(simp add: not_disjoint_intervals_def interval_of.simps disjoint_def)
    done

  private lemma [code]:
    "disjoint_intervals A B =
      (case A of (s,e) \<Rightarrow> case B of (s',e') \<Rightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e')"
    apply(cases A, cases B)
    apply(simp add: disjoint_intervals_def interval_of.simps disjoint_def)
    by fastforce


  text\<open>BEGIN merging overlapping intervals\<close>
  (*result has no empty intervals and all are disjoint.
    merging things such as [1,7] [8,10] would still be possible*)
  private fun merge_overlap
    :: "(('a::len0) word \<times> ('a::len0) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list"
  where
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
     apply(simp; fail)
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
     apply(simp; fail)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    apply(intro impI conjI)
     apply(drule not_disjoint_union)
     apply blast
    apply(simp)
    by blast

  private lemma merge_overlap_length:
    "\<exists>s' \<in> set ss. \<not> disjoint (interval_of A) (interval_of s') \<Longrightarrow>
      length (merge_overlap A ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add: not_disjoint_intervals_def interval_of.simps)
    done

  lemma "merge_overlap (1:: 16 word,2) [(1, 7)] = [(1, 7)]" by eval
  lemma "merge_overlap (1:: 16 word,2) [(2, 7)] = [(1, 7)]" by eval
  lemma "merge_overlap (1:: 16 word,2) [(3, 7)] = [(3, 7), (1,2)]" by eval

  private function listwordinterval_compress
    :: "(('a::len0) word \<times> ('a::len0) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
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

  private lemma listwordinterval_compress:
    "(\<Union>s \<in> set (listwordinterval_compress ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp)
    apply(intro impI)
    apply(simp add: disjoint_intervals_def)
    apply(drule merge_overlap_helper2)
    apply(simp)
    done

  lemma "listwordinterval_compress [(1::32 word,3), (8,10), (2,5), (3,7)] = [(8, 10), (1, 7)]"
    by eval

  private lemma A_in_listwordinterval_compress: "A \<in> set (listwordinterval_compress ss) \<Longrightarrow>
    interval_of A \<subseteq> (\<Union>s \<in> set ss. interval_of s)"
    using listwordinterval_compress by blast

  private lemma listwordinterval_compress_disjoint: 
    "A \<in> set (listwordinterval_compress ss) \<Longrightarrow> B \<in> set (listwordinterval_compress ss) \<Longrightarrow>
      A \<noteq> B \<Longrightarrow> disjoint (interval_of A) (interval_of B)"
    apply(induction ss arbitrary: rule: listwordinterval_compress.induct)
     apply(simp)
    apply(simp split: if_split_asm)
    apply(elim disjE)
       apply(simp_all)
     apply(simp_all add: disjoint_intervals_def disjoint_def)
     apply(thin_tac [!] "False \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _")
     apply(blast dest: A_in_listwordinterval_compress)+
    done
  text\<open>END merging overlapping intervals\<close>


  text\<open>BEGIN merging adjacent intervals\<close>
  private fun merge_adjacent
    :: "(('a::len) word \<times> ('a::len) word) \<Rightarrow> ('a word \<times> 'a word) list \<Rightarrow> ('a word \<times> 'a word) list"
  where
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
     apply(simp; fail)
    apply(rename_tac x xs)
    apply(cases A, rename_tac a b)
    apply(case_tac x)
    apply(simp add:  interval_of.simps)
    apply(intro impI conjI)
       apply (metis Un_assoc word_adjacent_union)
      apply(elim conjE)
      apply(drule(2) word_adjacent_union)
      apply(blast)
     using word_adjacent_union apply (metis (no_types, lifting) inf_sup_aci(6))
    by blast

  private lemma merge_adjacent_length:
    "\<exists>(s', e')\<in>set ss. s \<le> e \<and> s' \<le> e' \<and> (word_next e = s' \<or> word_next e' = s)
     \<Longrightarrow> length (merge_adjacent (s,e) ss) = length ss"
    apply(induction ss)
     apply(simp)
    apply(rename_tac x xs)
    apply(case_tac x)
    apply(simp add: )
    by blast

  private function listwordinterval_adjacent
    :: "(('a::len) word \<times> ('a::len) word) list \<Rightarrow> ('a word \<times> 'a word) list" where
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

  private lemma listwordinterval_adjacent:
    "(\<Union>s \<in> set (listwordinterval_adjacent ss). interval_of s) = (\<Union>s \<in> set ss. interval_of s)"
    apply(induction ss rule: listwordinterval_adjacent.induct)
     apply(simp)
    apply(simp add: merge_adjacent_helper)
    done

  lemma "listwordinterval_adjacent [(1::16 word, 3), (5, 10), (10,10), (4,4)] = [(10, 10), (1, 10)]"
    by eval
  text\<open>END merging adjacent intervals\<close>


  definition wordinterval_compress :: "('a::len) wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_compress r \<equiv>
      l2wi (remdups (listwordinterval_adjacent (listwordinterval_compress
        (wi2l (wordinterval_optimize_empty r)))))"

  text\<open>Correctness: Compression preserves semantics\<close>
  lemma wordinterval_compress:
    "wordinterval_to_set (wordinterval_compress r) = wordinterval_to_set r"
    unfolding wordinterval_compress_def
    proof -
      have interval_of': "interval_of s = (case s of (s,e) \<Rightarrow> {s .. e})" for s
        by (cases s) (simp add: interval_of.simps)

      have "wordinterval_to_set (l2wi (remdups (listwordinterval_adjacent
              (listwordinterval_compress (wi2l (wordinterval_optimize_empty r)))))) =
            (\<Union>x\<in>set (listwordinterval_adjacent (listwordinterval_compress
                (wi2l (wordinterval_optimize_empty r)))). interval_of x)"
        by (force simp: interval_of' l2wi)
      also have "\<dots> =  (\<Union>s\<in>set (wi2l (wordinterval_optimize_empty r)). interval_of s)"
        by(simp add: listwordinterval_compress listwordinterval_adjacent)
      also have "\<dots> = (\<Union>(i, j)\<in>set (wi2l (wordinterval_optimize_empty r)). {i..j})"
        by(simp add: interval_of')
      also have "\<dots> = wordinterval_to_set r" by(simp add: wi2l)
      finally show "wordinterval_to_set
        (l2wi (remdups (listwordinterval_adjacent (listwordinterval_compress
            (wi2l (wordinterval_optimize_empty r))))))
          = wordinterval_to_set r" .
  qed

end

text\<open>Example\<close>
lemma "(wi2l \<circ> (wordinterval_compress :: 32 wordinterval \<Rightarrow> 32 wordinterval) \<circ> l2wi)
          [(70, 80001), (0,0), (150, 8000), (1,3), (42,41), (3,7), (56, 200), (8,10)] =
          [(56, 80001), (0, 10)]" by eval

lemma "wordinterval_compress (RangeUnion (RangeUnion (WordInterval (1::32 word) 5)
                                                        (WordInterval 8 10)) (WordInterval 3 7)) =
       WordInterval 1 10" by eval



subsection\<open>Further operations\<close>

  text\<open>@{text "\<Union>"}\<close>
  definition wordinterval_Union :: "('a::len) wordinterval list \<Rightarrow> 'a wordinterval" where
    "wordinterval_Union ws = wordinterval_compress (foldr wordinterval_union ws Empty_WordInterval)"
  
  lemma wordinterval_Union:
    "wordinterval_to_set (wordinterval_Union ws) = (\<Union> w \<in> (set ws). wordinterval_to_set w)"
    by(induction ws) (simp_all add: wordinterval_compress wordinterval_Union_def)
   

context
begin
  private fun wordinterval_setminus'
    :: "'a::len wordinterval \<Rightarrow> 'a wordinterval \<Rightarrow> 'a wordinterval" where
    "wordinterval_setminus' (WordInterval s e) (WordInterval ms me) = (
      if s > e \<or> ms > me then WordInterval s e else
      if me \<ge> e
        then
          WordInterval (if ms = 0 then 1 else s) (min e (word_prev ms))
        else if ms \<le> s
        then
          WordInterval (max s (word_next me)) (if me = max_word then 0 else e)
        else
          RangeUnion (WordInterval (if ms = 0 then 1 else s) (word_prev ms))
                     (WordInterval (word_next me) (if me = max_word then 0 else e))
        )" |
     "wordinterval_setminus' (RangeUnion r1 r2) t =
        RangeUnion (wordinterval_setminus' r1 t) (wordinterval_setminus' r2 t)"|
     "wordinterval_setminus' t (RangeUnion r1 r2) =
        wordinterval_setminus' (wordinterval_setminus' t r1) r2"

  private lemma wordinterval_setminus'_rr_set_eq:
    "wordinterval_to_set(wordinterval_setminus' (WordInterval s e) (WordInterval ms me)) = 
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

  private lemma wordinterval_setminus'_set_eq:
    "wordinterval_to_set (wordinterval_setminus' r1 r2) =
      wordinterval_to_set r1 - wordinterval_to_set r2"
    apply(induction rule: wordinterval_setminus'.induct)
      using wordinterval_setminus'_rr_set_eq apply blast
     apply auto
    done
  lemma wordinterval_setminus'_empty_struct:
    "wordinterval_empty r2 \<Longrightarrow> wordinterval_setminus' r1 r2 = r1"
    by(induction r1 r2 rule: wordinterval_setminus'.induct) auto


  definition wordinterval_setminus
    :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_setminus r1 r2 = wordinterval_compress (wordinterval_setminus' r1 r2)"

  lemma wordinterval_setminus_set_eq[simp]: "wordinterval_to_set (wordinterval_setminus r1 r2) = 
    wordinterval_to_set r1 - wordinterval_to_set r2"
    by(simp add: wordinterval_setminus_def wordinterval_compress wordinterval_setminus'_set_eq)
end

definition wordinterval_UNIV :: "'a::len wordinterval" where
  "wordinterval_UNIV \<equiv> WordInterval 0 max_word"
lemma wordinterval_UNIV_set_eq[simp]: "wordinterval_to_set wordinterval_UNIV = UNIV"
  unfolding wordinterval_UNIV_def
  using max_word_max by fastforce
  
fun wordinterval_invert :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
  "wordinterval_invert r = wordinterval_setminus wordinterval_UNIV r"
lemma wordinterval_invert_set_eq[simp]:
  "wordinterval_to_set (wordinterval_invert r) = UNIV - wordinterval_to_set r" by(auto)

lemma wordinterval_invert_UNIV_empty:
  "wordinterval_empty (wordinterval_invert wordinterval_UNIV)" by simp


text\<open>@{text "\<inter>"}\<close>
context
begin
  private lemma "{(s::nat) .. e} \<inter> {s' .. e'} = {} \<longleftrightarrow> s > e' \<or> s' > e \<or> s > e \<or> s' > e'"
    by simp linarith
  private fun wordinterval_intersection'
    :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where
    "wordinterval_intersection' (WordInterval s e) (WordInterval s' e') = (
        if s > e \<or> s' > e' \<or> s > e' \<or> s' > e \<or> s > e \<or> s' > e'
        then
          Empty_WordInterval
        else
          WordInterval (max s s') (min e e')
        )" |
    "wordinterval_intersection' (RangeUnion r1 r2) t =
        RangeUnion (wordinterval_intersection' r1 t) (wordinterval_intersection' r2 t)"|
    "wordinterval_intersection' t (RangeUnion r1 r2) =
        RangeUnion (wordinterval_intersection' t r1) (wordinterval_intersection' t r2)"

  private lemma wordinterval_intersection'_set_eq: 
    "wordinterval_to_set (wordinterval_intersection' r1 r2) =
      wordinterval_to_set r1 \<inter> wordinterval_to_set r2"
    by(induction r1 r2 rule: wordinterval_intersection'.induct) (auto)

  lemma "wordinterval_intersection'
          (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10))
                      (WordInterval 1 3)) (WordInterval 1 3) =
          RangeUnion (RangeUnion (WordInterval 1 3) (WordInterval 1 0)) (WordInterval 1 3)" by eval

  definition wordinterval_intersection
    :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> 'a::len wordinterval" where 
    "wordinterval_intersection r1 r2 \<equiv> wordinterval_compress (wordinterval_intersection' r1 r2)"

  lemma wordinterval_intersection_set_eq[simp]: 
    "wordinterval_to_set (wordinterval_intersection r1 r2) =
      wordinterval_to_set r1 \<inter> wordinterval_to_set r2"
    by(simp add: wordinterval_intersection_def
                 wordinterval_compress wordinterval_intersection'_set_eq)

  lemma "wordinterval_intersection
          (RangeUnion (RangeUnion (WordInterval (1::32 word) 3) (WordInterval 8 10))
                      (WordInterval 1 3)) (WordInterval 1 3) =
          WordInterval 1 3" by eval
end


definition wordinterval_subset :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where
  "wordinterval_subset r1 r2 \<equiv> wordinterval_empty (wordinterval_setminus r1 r2)"
lemma wordinterval_subset_set_eq[simp]:
  "wordinterval_subset r1 r2 = (wordinterval_to_set r1 \<subseteq> wordinterval_to_set r2)"
  unfolding wordinterval_subset_def by simp

definition wordinterval_eq :: "'a::len wordinterval \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where 
  "wordinterval_eq r1 r2 = (wordinterval_subset r1 r2 \<and> wordinterval_subset r2 r1)"
lemma wordinterval_eq_set_eq:
  "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_to_set r1 = wordinterval_to_set r2"
  unfolding wordinterval_eq_def by auto

thm iffD1[OF wordinterval_eq_set_eq]
(*declare iffD1[OF wordinterval_eq_set_eq, simp]*)

lemma wordinterval_eq_comm: "wordinterval_eq r1 r2 \<longleftrightarrow> wordinterval_eq r2 r1"
  unfolding wordinterval_eq_def by fast
lemma wordinterval_to_set_alt: "wordinterval_to_set r = {x. wordinterval_element x r}"
  unfolding wordinterval_element_set_eq by blast

lemma wordinterval_un_empty:
  "wordinterval_empty r1 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r2"
  by(subst wordinterval_eq_set_eq, simp)
lemma wordinterval_un_emty_b:
  "wordinterval_empty r2 \<Longrightarrow> wordinterval_eq (wordinterval_union r1 r2) r1"
  by(subst wordinterval_eq_set_eq, simp)

lemma wordinterval_Diff_triv: 
  "wordinterval_empty (wordinterval_intersection a b) \<Longrightarrow> wordinterval_eq (wordinterval_setminus a b) a"
  unfolding wordinterval_eq_set_eq
  by simp blast



text\<open>A size of the datatype, does not correspond to the cardinality of the corresponding set\<close>
fun wordinterval_size :: "('a::len) wordinterval \<Rightarrow> nat" where
  "wordinterval_size (RangeUnion a b) = wordinterval_size a + wordinterval_size b" |
  "wordinterval_size (WordInterval s e) = (if s \<le> e then 1 else 0)"

lemma wordinterval_size_length: "wordinterval_size r = length (wi2l r)"
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


text\<open>The smallest element in the interval\<close>
  definition is_lowest_element :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_lowest_element x S = (x \<in> S \<and> (\<forall>y\<in>S. y \<le> x \<longrightarrow> y = x))"

  lemma 
  	fixes x :: "'a :: complete_lattice"
  	assumes "x \<in> S"
  	shows " x = Inf S \<Longrightarrow> is_lowest_element x S"
  using assms apply(simp add: is_lowest_element_def)
   by (simp add: Inf_lower eq_iff)

  lemma 
  	fixes x :: "'a :: linorder"
  	assumes "finite S" and "x \<in> S"
  	shows "is_lowest_element x S \<longleftrightarrow> x = Min S"
  apply(rule)
  subgoal
   apply(simp add: is_lowest_element_def)
   apply(subst Min_eqI[symmetric])
   using assms by(auto)
  by (metis Min.coboundedI assms(1) assms(2) dual_order.antisym is_lowest_element_def)

text\<open>Smallest element in the interval\<close>
  fun wordinterval_lowest_element :: "'a::len0 wordinterval \<Rightarrow> 'a word option" where
    "wordinterval_lowest_element (WordInterval s e) = (if s \<le> e then Some s else None)" | 
    "wordinterval_lowest_element (RangeUnion A B) =
      (case (wordinterval_lowest_element A, wordinterval_lowest_element B) of
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
    

  lemma wordinterval_lowest_element_correct_A:
    "wordinterval_lowest_element r = Some x \<Longrightarrow> is_lowest_element x (wordinterval_to_set r)"
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
         have wordinterval_lowest_element_RangeUnion:
          "\<And>a b A B. wordinterval_lowest_element A = Some a \<Longrightarrow>
                  wordinterval_lowest_element B = Some b \<Longrightarrow>
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


text\<open>Cardinality approximation for @{typ "('a::len) wordinterval"}s\<close>
context
begin
  lemma card_atLeastAtMost_word: fixes s::"('a::len) word" shows "card {s..e} = Suc (unat e) - (unat s)"
    apply(cases "s > e")
     apply(simp)
     apply(subst(asm) Word.word_less_nat_alt)
     apply simp
    apply(subst Word_Lemmas.upto_enum_set_conv2[symmetric])
    apply(subst List.card_set)
    apply(simp add: remdups_enum_upto)
    done

  fun wordinterval_card :: "('a::len) wordinterval \<Rightarrow> nat" where
    "wordinterval_card (WordInterval s e) = Suc (unat e) - (unat s)" |
    "wordinterval_card (RangeUnion a b) = wordinterval_card a + wordinterval_card b"

  lemma wordinterval_card: "wordinterval_card r \<ge> card (wordinterval_to_set r)"
    proof(induction r)
    case WordInterval thus ?case by (simp add: card_atLeastAtMost_word)
    next
    case (RangeUnion r1 r2)
      have "card (wordinterval_to_set r1 \<union> wordinterval_to_set r2) \<le>
              card (wordinterval_to_set r1) + card (wordinterval_to_set r2)"
        using Finite_Set.card_Un_le by blast
      with RangeUnion show ?case by(simp)
    qed

  text\<open>With @{thm wordinterval_compress} it should be possible to get the exact cardinality\<close>
end
    
end
