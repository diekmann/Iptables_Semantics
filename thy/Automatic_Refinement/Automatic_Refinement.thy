section {* Entry Point for the Automatic Refinement Tool *}
theory Automatic_Refinement
imports 
  "Tool/Autoref_Tool"
  "Autoref_Bindings_HOL"
begin
  text {* The automatic refinement tool should be used by 
    importing this theory *}

subsection {* Convenience *}

text {* The following lemmas can be used to add tags to theorems *}
lemma PREFER_I: "P x \<Longrightarrow> PREFER P x" by simp
lemma PREFER_D: "PREFER P x \<Longrightarrow> P x" by simp

lemmas PREFER_sv_D = PREFER_D[of single_valued]
lemma PREFER_id_D: "PREFER_id R \<Longrightarrow> R=Id" by simp

abbreviation "PREFER_RUNIV \<equiv> PREFER (\<lambda>R. Range R = UNIV)"
lemmas PREFER_RUNIV_D = PREFER_D[of "(\<lambda>R. Range R = UNIV)"]

lemma SIDE_GEN_ALGO_D: "SIDE_GEN_ALGO P \<Longrightarrow> P" by simp

lemma GEN_OP_D: "GEN_OP c a R \<Longrightarrow> (c,a)\<in>R"
  by simp

lemma MINOR_PRIO_TAG_I: "P \<Longrightarrow> (MINOR_PRIO_TAG p \<Longrightarrow> P)" by auto
lemma MAJOR_PRIO_TAG_I: "P \<Longrightarrow> (MAJOR_PRIO_TAG p \<Longrightarrow> P)" by auto
lemma PRIO_TAG_I: "P \<Longrightarrow> (PRIO_TAG ma mi \<Longrightarrow> P)" by auto

end
