theory Shadowed
imports SimpleFw_Semantics
  "../Common/Negation_Type_DNF"
  "../Primitive_Matchers/Ports"
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



text{*A different approach where we start with the empty set of packets and collect packets which are already ``matched-away''.*}
fun rmshadow' :: "simple_rule list \<Rightarrow> simple_packet set \<Rightarrow> simple_rule list" where
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
       apply(drule_tac m=m in nomatch_m)
        apply(simp)
       apply(simp add: nomatch)
      apply(simp)
      apply(case_tac a)
       apply(simp_all)
       apply(simp_all add: IH2)
      done
  qed

corollary "simple_fw (rmshadow rs UNIV) p = simple_fw (rmshadow' rs {}) p"
  using rmshadow'_sound rmshadow_sound by auto

value "rmshadow [SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = Proto TCP, sports = (0, 0xFFFF), dports = (0x16, 0x16)\<rparr>
          simple_action.Drop,
        SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = ProtoAny, sports = (0, 0xFFFF), dports = (0, 0xFFFF)\<rparr>
          simple_action.Accept,
        SimpleRule \<lparr>iiface = Iface ''+'', oiface = Iface ''+'', src = (0, 0), dst = (0, 0), proto = Proto TCP, sports = (0, 0xFFFF), dports = (0x138E, 0x138E)\<rparr>
          simple_action.Drop] UNIV"


(*
subsection{*A datastructure for sets of packets*}
text{*Previous algorithm is not executable because we have no code for @{typ "simple_packet set"}.*}


  (*assume: no interface wildcards
    then we should be able to store a packet set in the following*)
  (*TODO: accessors colide with simple_match*)


  type_synonym simple_packet_set = "simple_match list"

  fun simple_packet_set_toSet :: "simple_packet_set \<Rightarrow> simple_packet set" where
    "simple_packet_set_toSet ms = {p. \<exists>m \<in> set ms. simple_matches m p}"

  fun simple_packet_set_union :: "simple_packet_set \<Rightarrow> simple_match \<Rightarrow> simple_packet_set" where
    "simple_packet_set_union ps m = m #ps"

  lemma "simple_packet_set_toSet (simple_packet_set_union ps m) = simple_packet_set_toSet ps \<union> {p. simple_matches m p}"
    apply(simp) by blast


  
  definition "iface_subset = undefined"
  lemma "iface_subset ifce1 ifce2 \<longleftrightarrow> {i. match_iface ifce1 i} \<subseteq> {i. match_iface ifce2 i}" sorry

  fun simple_packet_set_subset :: "simple_match \<Rightarrow> simple_packet_set \<Rightarrow> bool" where
    "simple_packet_set_subset m [] \<longleftrightarrow> empty_match m" |
    "simple_packet_set_subset \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=protocol, sports=sps, dports=dps \<rparr> ms \<longleftrightarrow> 
        (\<exists>m' \<in> set ms. iface_subset iif (iiface m')) \<and>
        (\<exists>m' \<in> set ms. iface_subset oif (oiface m')) \<and> undefined" (*TODO: continue!*)
*)
end
