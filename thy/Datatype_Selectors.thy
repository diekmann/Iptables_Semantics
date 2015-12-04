theory Datatype_Selectors
imports Main
begin

text{*
  Running Example: @{text "datatype_new iptrule_match = is_Src: Src (src_range: ipt_ipv4range)"}

  A discriminator @{text disc} tells whether a value is of a certain constructor.
    Example: @{text "is_Src"}

  A selector @{text sel} select the inner value.
    Example: @{text "src_range"}

  A constructor @{text C} constructs a value
    Example: @{text "Src"}


  The are well-formed if the belong together.
*}
fun wf_disc_sel :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "wf_disc_sel (disc, sel) C \<longleftrightarrow> (\<forall>a. disc a \<longrightarrow> C (sel a) = a) \<and> (\<forall>a. (*disc (C a) \<longrightarrow>*) sel (C a) = a)"

declare wf_disc_sel.simps[simp del]

end
