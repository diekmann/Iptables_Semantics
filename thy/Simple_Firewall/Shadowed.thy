section\<open>Shadowed Rules\<close>
theory Shadowed
imports SimpleFw_Semantics
begin


subsection\<open>Removing Shadowed Rules\<close>
text\<open>Testing, not executable\<close>

text\<open>Assumes: @{term "simple_ruleset"}\<close>
fun rmshadow :: "'i::len simple_rule list \<Rightarrow> 'i simple_packet set \<Rightarrow> 'i simple_rule list" where
  "rmshadow [] _ = []" |
  "rmshadow ((SimpleRule m a)#rs) P = (if (\<forall>p\<in>P. \<not> simple_matches m p)
    then 
      rmshadow rs P
    else
      (SimpleRule m a) # (rmshadow rs {p \<in> P. \<not> simple_matches m p}))"


subsubsection\<open>Soundness\<close>
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

  corollary rmshadow:
    fixes p :: "'i::len simple_packet"
    shows "simple_fw (rmshadow rs UNIV) p = simple_fw rs p"
    using rmshadow_sound[of p] by simp

text\<open>A different approach where we start with the empty set of packets and collect packets which are already ``matched-away''.\<close>
fun rmshadow' :: "'i::len simple_rule list \<Rightarrow> 'i simple_packet set \<Rightarrow> 'i simple_rule list" where
  "rmshadow' [] _ = []" |
  "rmshadow' ((SimpleRule m a)#rs) P = (if {p. simple_matches m p} \<subseteq> P
    then 
      rmshadow' rs P
    else
      (SimpleRule m a) # (rmshadow' rs (P \<union> {p. simple_matches m p})))"

  lemma rmshadow'_sound: 
    "p \<notin> P \<Longrightarrow> simple_fw (rmshadow' rs P) p = simple_fw rs p"
  proof(induction rs arbitrary: P)
  case Nil thus ?case by simp
  next
  case (Cons r rs)
    from Cons.IH Cons.prems have IH1: "simple_fw (rmshadow' rs P) p = simple_fw rs p" by (simp)
    let ?P'="{p. simple_matches (match_sel r) p}"
    from Cons.IH Cons.prems have IH2: "\<And>m. p \<notin> (Collect (simple_matches m)) \<Longrightarrow> simple_fw (rmshadow' rs (P \<union> Collect (simple_matches m))) p = simple_fw rs p" by simp
    have nomatch_m: "\<And>m. p \<notin> P \<Longrightarrow> {p. simple_matches m p} \<subseteq> P \<Longrightarrow> \<not> simple_matches m p" by blast
    from Cons.prems show ?case
      apply(cases r, rename_tac m a)
      apply(simp)
      apply(case_tac "{p. simple_matches m p} \<subseteq> P")
       apply(simp add: IH1)
       apply(drule nomatch_m)
        apply(assumption)
       apply(simp add: nomatch)
      apply(simp)
      apply(case_tac a)
       apply(simp_all)
       apply(simp_all add: IH2)
      done
  qed

corollary 
  fixes p :: "'i::len simple_packet"
  shows "simple_fw (rmshadow rs UNIV) p = simple_fw (rmshadow' rs {}) p"
  using rmshadow'_sound[of p] rmshadow_sound[of p] by simp


text\<open>Previous algorithm is not executable because we have no code for @{typ "'i::len simple_packet set"}.
      To get some code, some efficient set operations would be necessary.
        We either need union and subset or intersection and negation.
        Both subset and negation are complicated.
      Probably the BDDs which related work uses is really necessary.
\<close>

(*Drafting set operations which might be necessary for an executable implementation. But BDDs might just be the thing here.*)
context
begin
  private type_synonym 'i simple_packet_set = "'i simple_match list"

  private definition simple_packet_set_toSet :: "'i::len simple_packet_set \<Rightarrow> 'i simple_packet set" where
    "simple_packet_set_toSet ms = {p. \<exists>m \<in> set ms. simple_matches m p}"

  private lemma simple_packet_set_toSet_alt: "simple_packet_set_toSet ms = (\<Union> m \<in> set ms. {p. simple_matches m p})"
    unfolding simple_packet_set_toSet_def by blast

  private definition simple_packet_set_union :: "'i::len simple_packet_set \<Rightarrow>'i  simple_match \<Rightarrow> 'i simple_packet_set" where
    "simple_packet_set_union ps m = m # ps"

  private lemma "simple_packet_set_toSet (simple_packet_set_union ps m) = simple_packet_set_toSet ps \<union> {p. simple_matches m p}"
    unfolding simple_packet_set_toSet_def simple_packet_set_union_def by simp blast

   (*either a sound but not complete executable implementation or a better idea to implement subset*)
   private lemma "(\<exists>m' \<in> set ms.
        {i. match_iface iif i} \<subseteq> {i. match_iface (iiface m') i} \<and>
        {i. match_iface oif i} \<subseteq> {i. match_iface (oiface m') i} \<and>
        {ip. simple_match_ip sip ip} \<subseteq> {ip. simple_match_ip (src m') ip} \<and>
        {ip. simple_match_ip dip ip} \<subseteq> {ip. simple_match_ip (dst m') ip} \<and>
        {p. match_proto protocol p} \<subseteq> {p. match_proto (proto m') p} \<and>
        {p. simple_match_port sps p} \<subseteq> {p. simple_match_port (sports m') p} \<and>
        {p. simple_match_port dps p} \<subseteq> {p. simple_match_port (dports m') p}
      )
    \<Longrightarrow> {p. simple_matches \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=protocol, sports=sps, dports=dps \<rparr> p} \<subseteq> (simple_packet_set_toSet ms)"
      unfolding simple_packet_set_toSet_def simple_packet_set_union_def
      apply(simp add: simple_matches.simps)
      apply(simp add: Set.Collect_mono_iff)
      apply clarify
      apply meson
      done

    text\<open>subset or negation ... One efficient implementation would suffice.\<close>
    private lemma "{p:: 'i::len simple_packet. simple_matches m p} \<subseteq> (simple_packet_set_toSet ms) \<longleftrightarrow>
      {p:: 'i::len simple_packet. simple_matches m p} \<inter> (\<Inter> m \<in> set ms. {p. \<not> simple_matches m p}) = {}" (is "?l \<longleftrightarrow> ?r")
    proof - 
      have "?l \<longleftrightarrow> {p. simple_matches m p} - (simple_packet_set_toSet ms) = {}" by blast
      also have "\<dots> \<longleftrightarrow> {p. simple_matches m p} - (\<Union> m \<in> set ms. {p:: 'i::len simple_packet. simple_matches m p}) = {}"
      using simple_packet_set_toSet_alt by blast
      also have "\<dots> \<longleftrightarrow> ?r" by blast
      finally show ?thesis .
    qed

end
end
