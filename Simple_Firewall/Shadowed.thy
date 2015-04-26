theory Shadowed
imports SimpleFw_Semantics
  "../Common/Negation_Type_DNF"
begin


section{*Optimizing Simple Firewall*}

subsection{*Removing Shadowed Rules*}
(*Testing, not executable*)

text{*Assumes: @{term "simple_ruleset"}*}
fun rmshadow :: "simple_rule list \<Rightarrow> simple_packet set \<Rightarrow> simple_rule list" where
  "rmshadow [] _ = []" |
  "rmshadow ((SimpleRule m a)#rs) P = (if (\<forall>p\<in>P. \<not> simple_matches m p)
    then 
      rmshadow rs P
    else
      (SimpleRule m a) # (rmshadow rs {p \<in> P. \<not> simple_matches m p}))"


subsubsection{*Soundness*}
  lemma rmshadow_sound: 
    "p \<in> P \<Longrightarrow> simple_fw (rmshadow rs P) p = simple_fw rs p"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons.IH Cons.prems have IH1: "simple_fw (rmshadow rs P) p = simple_fw rs p" by (simp)
    let ?P'="{p \<in> P. \<not> simple_matches (match_sel r) p}"
    from Cons.IH Cons.prems have IH2: "\<And>m. p \<in> ?P' \<Longrightarrow> simple_fw (rmshadow rs ?P') p = simple_fw rs p" by simp
    from Cons.prems show ?case
      apply(cases r, rename_tac m a)
      apply(simp)
      apply(case_tac "\<forall>p\<in>P. \<not> simple_matches m p")
       apply(simp add: IH1 nomatch)
      apply(case_tac "p \<in> ?P'")
       apply(frule IH2)
       apply(simp add: nomatch IH1)
      apply(simp)
      apply(case_tac a)
       apply(simp_all)
      by fast+
  qed


value "rmshadow [SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = Proto TCP, sports = (0, 0xFFFF), dports = (0x16, 0x16)\<rparr>
          simple_action.Drop,
        SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF), dports = (0, 0xFFFF)\<rparr>
          simple_action.Accept,
        SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = Proto TCP, sports = (0, 0xFFFF), dports = (0x138E, 0x138E)\<rparr>
          simple_action.Drop] UNIV"


subsection{*A datastructure for sets of packets*}
  text{*Previous algorithm is not executable because we have no code for @{typ "simple_packet set"}.*}
  
  text{*A set of simple packets is represented by a DNF expression of simple matches.*}
  type_synonym simple_packet_set="simple_match dnf"
  
  definition simple_packet_set :: "simple_packet_set \<Rightarrow> simple_packet set" where
    "simple_packet_set sps \<equiv> {p. dnf_to_bool (\<lambda>m. simple_matches m p) sps}"
  
  lemma simple_packet_set_alt: "simple_packet_set sps =
    (\<Union> cnf \<in> set sps. 
          {p. \<forall> c \<in> set cnf. case c of Pos x \<Rightarrow> simple_matches x p
                                    |  Neg x \<Rightarrow> \<not> simple_matches x p})"
    unfolding simple_packet_set_def
    using dnf_to_bool_set cnf_to_bool_set by blast
  
  definition simple_packet_set_UNIV :: simple_packet_set where
    "simple_packet_set_UNIV \<equiv> dnf_True"
  lemma "simple_packet_set simple_packet_set_UNIV = UNIV"
    unfolding simple_packet_set_UNIV_def simple_packet_set_def using dnf_True by blast

  (*Idea: replace (\<forall>p\<in>P. \<not> simple_matches m p) by something with uses simple_packet_set*)
  lemma "(\<forall>p\<in>P. \<not> simple_matches m p) \<longleftrightarrow> P \<inter> {p. simple_matches m p} = {}" by auto
  (*simple_packet_set_is_empty
    We can approximate simple_packet_set_is_empty.
      Only if simple_packet_set_is_empty returns True, then the set must be empty
      Other direction (if it is empty, the it must return true) can be ignored for the soundness (not completeness)
      of the rmshadow algorithm because if the set is not empty, the ruleset is not modified.
      *)


end
