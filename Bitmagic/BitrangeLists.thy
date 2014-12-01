theory BitrangeLists
imports Bitrange
begin

subsection{*Bitrange to List*}
text{*A list of @{text "(start, end)"} tuples.*}

  fun br2l :: "'a::len bitrange \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "br2l (RangeUnion r1 r2) = br2l r1 @ br2l r2" |
    "br2l (Bitrange s e) = (if e < s then [] else [(s,e)])"
  
  fun l2br :: "('a::len word \<times> 'a::len word) list \<Rightarrow> 'a::len bitrange" where
    "l2br [] = Empty_Bitrange" | 
    "l2br ((s,e)#rs) = (RangeUnion (Bitrange s e) (l2br rs))"
  

  lemma l2br_append: "bitrange_to_set (l2br (l1@l2)) = bitrange_to_set (l2br l1) \<union> bitrange_to_set (l2br l2)"
    by(induction l1) (auto)
  
  lemma l2br_br2l: "bitrange_to_set (l2br (br2l r)) = bitrange_to_set r"
    by(induction r) (simp_all add: l2br_append)


end
