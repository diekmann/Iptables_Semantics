theory Lib_toString
imports Main
begin


section{*toString Functions*}

(*http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"
definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

definition list_toString :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
  "list_toString toStr ls = ''[''@ concat (splice (map toStr ls) (replicate (length ls - 1) '', ''))  @'']''"

lemma "list_toString string_of_nat [1,2,3] = ''[1, 2, 3]''" by eval

(*HACK: rewrite quotes such that they are better printable by Isabelle*)
definition quote_rewrite :: "string \<Rightarrow> string" where
  "quote_rewrite \<equiv> map (\<lambda>c. if c = Char Nibble2 Nibble2 then CHR ''~'' else c)"
value "quote_rewrite (''foo''@[Char Nibble2 Nibble2])"


fun bool_toString :: "bool \<Rightarrow> string" where
  "bool_toString True = ''True''" |
  "bool_toString False = ''False''"

subsection{*Enum set to string*}
  fun enum_one_in_set_toString :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> (string \<times> 'a set option)" where
    "enum_one_in_set_toString _     []     S = ('''', None)" |
    "enum_one_in_set_toString toStr (s#ss) S = (if s \<in> S then (toStr s, Some (S - {s})) else enum_one_in_set_toString toStr ss S)"

  lemma enum_one_in_set_toString_finite_card_le: "finite S \<Longrightarrow> (x, Some S') = enum_one_in_set_toString toStr ss S \<Longrightarrow> card S' < card S"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    by (metis card_gt_0_iff diff_less equals0D lessI)
    
  

  function enum_set_toString_list :: "('a \<Rightarrow> string) \<Rightarrow> ('a::enum) set \<Rightarrow> string list" where
    "enum_set_toString_list toStr S = (if S = {} then [] else
      case enum_one_in_set_toString toStr (Enum.enum) S of (_, None) \<Rightarrow> []
                                               |  (str, Some S') \<Rightarrow> str#enum_set_toString_list toStr S')"
  by(pat_completeness) auto
  
  termination enum_set_toString_list
  apply (relation "measure (\<lambda>(_,S). card S)")
  apply(simp_all add: card_gt_0_iff enum_one_in_set_toString_finite_card_le)
  done

end
