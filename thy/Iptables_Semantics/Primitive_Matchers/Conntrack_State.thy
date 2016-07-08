theory Conntrack_State
imports "../Common/Negation_Type" "../../Simple_Firewall/Common/Lib_Enum_toString"
begin


datatype ctstate = CT_New | CT_Established | CT_Related | CT_Untracked | CT_Invalid

text\<open>The state associated with a packet can be added as a tag to the packet.
      See @{file "../Semantics_Stateful.thy"}.\<close>

fun match_ctstate :: "ctstate set \<Rightarrow> ctstate \<Rightarrow> bool" where
"match_ctstate S s_tag \<longleftrightarrow> s_tag \<in> S"

fun ctstate_conjunct :: "ctstate set \<Rightarrow> ctstate set \<Rightarrow> ctstate set option" where
  "ctstate_conjunct S1 S2 = (if S1 \<inter> S2 = {} then None else Some (S1 \<inter> S2))"

value[code] "ctstate_conjunct {CT_Established, CT_New} {CT_New}"

lemma ctstate_conjunct_correct: "match_ctstate S1 pkt \<and> match_ctstate S2 pkt \<longleftrightarrow> 
  (case ctstate_conjunct S1 S2 of None \<Rightarrow> False | Some S' \<Rightarrow> match_ctstate S' pkt)"
  apply simp
  by blast

lemma UNIV_ctstate: "UNIV = {CT_New, CT_Established, CT_Related, CT_Untracked, CT_Invalid}" using ctstate.exhaust by auto 

(*
function ctstate_set_toString_list :: "ctstate set \<Rightarrow> string list" where
  "ctstate_set_toString_list S = (if S = {} then [] else
    if CT_New \<in> S then ''NEW''#ctstate_set_toString_list (S - {CT_New}) else
    if CT_Established \<in> S then ''ESTABLISHED''#ctstate_set_toString_list (S - {CT_Established}) else
    if CT_Related \<in> S then ''RELATED''#ctstate_set_toString_list (S - {CT_Related}) else
    if CT_Untracked \<in> S then ''UNTRACKED''#ctstate_set_toString_list (S - {CT_Untracked}) else [''ERROR-unkown-ctstate''])"
by(pat_completeness) auto

termination ctstate_set_toString_list
  apply(relation "measure (\<lambda>(S). card S)")
  apply(simp_all add: card_gt_0_iff)
  done

*)
instance ctstate :: finite
proof
  from UNIV_ctstate show "finite (UNIV:: ctstate set)" using finite.simps by auto 
qed

  
lemma "finite (S :: ctstate set)" by simp


instantiation "ctstate" :: enum
begin
  definition "enum_ctstate = [CT_New, CT_Established, CT_Related, CT_Untracked, CT_Invalid]"

  definition "enum_all_ctstate P \<longleftrightarrow> P CT_New \<and> P CT_Established \<and> P CT_Related \<and> P CT_Untracked \<and> P CT_Invalid"
  
  definition "enum_ex_ctstate P \<longleftrightarrow> P CT_New \<or> P CT_Established \<or> P CT_Related \<or> P CT_Untracked \<or> P CT_Invalid"
instance proof
  show "UNIV = set (enum_class.enum :: ctstate list)"
    by(simp add: UNIV_ctstate enum_ctstate_def)
  next
  show "distinct (enum_class.enum :: ctstate list)"
    by(simp add: enum_ctstate_def)
  next
  show "\<And>P. (enum_class.enum_all :: (ctstate \<Rightarrow> bool) \<Rightarrow> bool) P = Ball UNIV P"
    by(simp add: UNIV_ctstate enum_all_ctstate_def)
  next
  show "\<And>P. (enum_class.enum_ex :: (ctstate \<Rightarrow> bool) \<Rightarrow> bool) P = Bex UNIV P"
    by(simp add: UNIV_ctstate enum_ex_ctstate_def)
qed
end

definition ctstate_is_UNIV :: "ctstate set \<Rightarrow> bool" where
  "ctstate_is_UNIV c \<equiv> CT_New \<in> c \<and> CT_Established \<in> c \<and> CT_Related \<in> c \<and> CT_Untracked \<in> c \<and> CT_Invalid \<in> c"

lemma ctstate_is_UNIV: "ctstate_is_UNIV c \<longleftrightarrow> c = UNIV"
  unfolding ctstate_is_UNIV_def
  apply(simp add: UNIV_ctstate)
  apply(rule iffI)
  apply(clarify)
   using UNIV_ctstate apply fastforce
   apply(simp)
  done


value[code] "ctstate_is_UNIV {CT_Established}"



fun ctstate_toString :: "ctstate \<Rightarrow> string" where
  "ctstate_toString CT_New = ''NEW''" |
  "ctstate_toString CT_Established = ''ESTABLISHED''" |
  "ctstate_toString CT_Related = ''RELATED''" |
  "ctstate_toString CT_Untracked = ''UNTRACKED''" |
  "ctstate_toString CT_Invalid = ''INVALID''"


definition ctstate_set_toString :: "ctstate set \<Rightarrow> string" where
  "ctstate_set_toString S = list_separated_toString '','' ctstate_toString (enum_set_to_list S)"

lemma "ctstate_set_toString {CT_New, CT_New, CT_Established} = ''NEW,ESTABLISHED''" by eval


end
