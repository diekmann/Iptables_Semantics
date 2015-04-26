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
  
  (*assume: no interface wildcards
    then we should be able to store a packet set in the following*)
  (*TODO: accessors colide with simple_match*)
  record simple_packet_set =
      iiface :: "iface dnf"
      oiface :: "iface dnf"
      src :: "(ipv4addr \<times> nat) list"
      dst :: "(ipv4addr \<times> nat) list"
      proto :: "protocol list"
      sports :: "(16 word \<times> 16 word) list"
      dports :: "(16 word \<times> 16 word) list"
  
  fun simple_packet_set_toSet :: "simple_packet_set \<Rightarrow> simple_packet set" where
    "simple_packet_set_toSet \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> = 
        {p. dnf_to_bool (\<lambda>m. match_iface m (p_iiface p)) iif \<and>
            dnf_to_bool (\<lambda>m. match_iface m (p_oiface p)) oif \<and> 
            (\<exists>rng \<in> set sip. simple_match_ip rng (p_src p))}"
            (*\<dots>*)
  (*
    what can we do with this representation?
                            \<union>    \<inter>                   negate                            is_empty
    iface dnf               @    dnf_and              dnf_not                          ? \<rightarrow> no iface wildcards, should be doable
    cidr list               @    smallest prefix      to bitrange, negate, cidrsplit   []
    protocol                @    ?              ?                          ?
    port-interval list      @    intersect bitrange   bitrange negate                  []
  *)
  
  (*Idea: replace (\<forall>p\<in>P. \<not> simple_matches m p) by something with uses simple_packet_set*)
  lemma "(\<forall>p\<in>P. \<not> simple_matches m p) \<longleftrightarrow> P \<inter> {p. simple_matches m p} = {}" by auto
  (*simple_packet_set_is_empty
    We can approximate simple_packet_set_is_empty.
      Only if simple_packet_set_is_empty returns True, then the set must be empty
      Other direction (if it is empty, the it must return true) can be ignored for the soundness (not completeness)
      of the rmshadow algorithm because if the set is not empty, the ruleset is not modified.
      *)



end
