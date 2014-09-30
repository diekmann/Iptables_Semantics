theory Packet_Set
imports Fixed_Action "Primitive_Matchers/Negation_Type_Matching" Datatype_Selectors
begin

section{*Packet Set*}

text{*@{const alist_and} transforms @{typ "'a negation_type list \<Rightarrow> 'a match_expr"} and uses conjunction as connective. *}


  

text{*inner is and, outer is or*}
definition to_negation_type :: "'a match_expr \<Rightarrow> ('a negation_type list) list" where
 "to_negation_type m = map to_negation_type_nnf (normalize_match m)"

term normalize_match
term normalized_match
thm normalized_match_normalize_match


(*probably wants a simple ruleset*)

definition to_packet_set :: "('a, 'packet) match_tac \<Rightarrow> action \<Rightarrow> ('a negation_type list) list \<Rightarrow> 'packet set" where
  "to_packet_set \<gamma> a ms \<equiv> {p. \<exists> m \<in> set ms. matches \<gamma> (alist_and m) a p}"



(*TODO create a output_format directory*)



end
