theory Conntrack_State
imports "../Common/Negation_Type"
begin


datatype ctstate = CT_New | CT_Established | CT_Untracked

text{*The state associated with a packet can be added as a tag to the packet.
      See @{file "../Semantics_Stateful.thy"}.*}

fun match_ctstate :: "ctstate set \<Rightarrow> ctstate \<Rightarrow> bool" where
"match_ctstate S s_tag \<longleftrightarrow> s_tag \<in> S"

fun ctstate_conjunct :: "ctstate set \<Rightarrow> ctstate set \<Rightarrow> ctstate set option" where
  "ctstate_conjunct S1 S2 = (if S1 \<inter> S2 = {} then None else Some (S1 \<inter> S2))"

value[code] "ctstate_conjunct {CT_Established, CT_New} {CT_New}"

lemma ctstate_conjunct_correct: "match_ctstate S1 pkt \<and> match_ctstate S2 pkt \<longleftrightarrow> 
  (case ctstate_conjunct S1 S2 of None \<Rightarrow> False | Some S' \<Rightarrow> match_ctstate S' pkt)"
  apply simp
  by blast

function ctstate_set_toString_list :: "ctstate set \<Rightarrow> string list" where
  "ctstate_set_toString_list S = (if S = {} then [] else
    if CT_New \<in> S then ''NEW''#ctstate_set_toString_list (S - {CT_New}) else
    if CT_Established \<in> S then ''ESTABLISHED''#ctstate_set_toString_list (S - {CT_Established}) else
    if CT_Untracked \<in> S then ''UNTRACKED''#ctstate_set_toString_list (S - {CT_Untracked}) else [''ERROR-unkown-ctstate''])"
by(pat_completeness) auto

instance ctstate :: finite
proof
  have "UNIV = {CT_New, CT_Established, CT_Untracked}" using ctstate.exhaust by auto 
  thus "finite (UNIV:: ctstate set)" using finite.simps by auto 
qed
  
lemma "finite (S :: ctstate set)" by simp

termination ctstate_set_toString_list
apply (relation "measure (\<lambda>(S). card S)")
apply(simp_all add: card_gt_0_iff)
done

definition ctstate_set_toString :: "ctstate set \<Rightarrow> string" where
  "ctstate_set_toString S = concat (splice (ctstate_set_toString_list S) (replicate (length (ctstate_set_toString_list S) - 1) '',''))"

value[code] "ctstate_set_toString {CT_New, CT_New, CT_Established}"

end
