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
      proto :: "protocol set"
      sports :: "(16 word \<times> 16 word) list"
      dports :: "(16 word \<times> 16 word) list"
    (*
    what can we do with this representation?
                            \<union>    \<inter>                   negate                            is_empty
    iface dnf               @    dnf_and              dnf_not                          ? \<rightarrow> no iface wildcards, should be doable
    cidr list               @    smallest prefix      to bitrange, negate, cidrsplit   []
    protocol                \<union>    \<inter>                   -                                 = {}
    port-interval list      @    intersect bitrange   bitrange negate                  []
  *)

  fun simple_packet_set_toSet :: "simple_packet_set \<Rightarrow> simple_packet set" where
    "simple_packet_set_toSet \<lparr>iiface=iifs, oiface=oifs, src=sips, dst=dips, proto=protocols, sports=spss, dports=dpss \<rparr> = 
        {p. (dnf_to_bool (\<lambda>m. match_iface m (p_iiface p)) iifs) \<and>
            (dnf_to_bool (\<lambda>m. match_iface m (p_oiface p)) oifs) \<and> 
            (\<exists>rng \<in> set sips. simple_match_ip rng (p_src p)) \<and>
            (\<exists>rng \<in> set dips. simple_match_ip rng (p_dst p)) \<and>
            (\<exists>proto \<in> protocols. match_proto proto (p_proto p)) \<and>
            (\<exists>rng \<in> set spss. simple_match_port rng (p_sport p)) \<and>
            (\<exists>rng \<in> set dpss. simple_match_port rng (p_dport p)) }"

  text{*Did we forget anything? no.*}
  lemma "p \<in> (simple_packet_set_toSet
                \<lparr>simple_packet_set.iiface=[[Pos iif]], oiface=[[Pos oif]], src=[sip], dst=[dip], proto={protocol}, sports=[sps], dports=[dps] \<rparr>) \<longleftrightarrow>
         simple_matches \<lparr>simple_match.iiface=iif, oiface=oif, src=sip, dst=dip, proto=protocol, sports=sps, dports=dps \<rparr> p"
    by(simp add: simple_matches.simps)

  fun optimize :: "simple_packet_set \<Rightarrow> simple_packet_set" where
    "optimize \<lparr>iiface=iifs, oiface=oifs, src=sips, dst=dips, proto=protocols, sports=spss, dports=dpss \<rparr> = 
      \<lparr>iiface=iifs, oiface=oifs, (*todo*)
       src= remdups sips, dst= remdups dips, (*todo: implode ranges?*)
       proto=protocols, 
       sports = filter (\<lambda>(s,e). s \<le> e) spss,
       dports = filter (\<lambda>(s,e). s \<le> e) dpss \<rparr>"
  lemma "simple_packet_set_toSet (optimize pkts) = simple_packet_set_toSet pkts"
    proof -
    { fix pss p
      have "(\<exists>rng \<in> set (filter (\<lambda>(s,e). s \<le> e) pss). simple_match_port rng p) \<longleftrightarrow> (\<exists>rng \<in> set pss. simple_match_port rng p)"
        by(induction pss)(auto) }
    thus ?thesis
    apply(cases pkts, rename_tac iifs oifs sips dips protocols spss dpss)
    by simp
  qed

  fun is_empty :: "simple_packet_set \<Rightarrow> bool" where
    "is_empty \<lparr>iiface=iifs, oiface=oifs, src=sips, dst=dips, proto=protocols, sports=spss, dports=dpss \<rparr> \<longleftrightarrow>
        iifs = [] (*todo*) \<or> oifs = [] \<or> (*todo*)
        sips = [] \<or> dips = [] \<or>
        protocols = {} \<or>
        spss = [] \<or> dpss = [] (*TODO*)"
   lemma "is_empty pkts \<longleftrightarrow> simple_packet_set_toSet pkts = {}"
     apply(cases pkts, rename_tac iifs oifs sips dips protocols spss dpss)
     apply(simp)
     apply(rule iffI)
      apply(elim disjE, simp_all)
     oops (* \<longrightarrow> direction holds*)

  fun invert :: "simple_packet_set \<Rightarrow> simple_packet_set" where
    "invert \<lparr>iiface=iifs, oiface=oifs, src=sips, dst=dips, proto=protocols, sports=spss, dports=dpss \<rparr> = 
      \<lparr>iiface=dnf_not iifs, oiface=dnf_not oifs,
             src= sips, dst=  dips, (*todo*)
             proto=-protocols, 
             sports = filter (\<lambda>(s,e). s \<le> e) spss,
             dports = filter (\<lambda>(s,e). s \<le> e) dpss \<rparr>"
  
  (*Idea: replace (\<forall>p\<in>P. \<not> simple_matches m p) by something with uses simple_packet_set*)
  lemma "(\<forall>p\<in>P. \<not> simple_matches m p) \<longleftrightarrow> P \<inter> {p. simple_matches m p} = {}" by auto
  (*simple_packet_set_is_empty
    We can approximate simple_packet_set_is_empty.
      Only if simple_packet_set_is_empty returns True, then the set must be empty
      Other direction (if it is empty, the it must return true) can be ignored for the soundness (not completeness)
      of the rmshadow algorithm because if the set is not empty, the ruleset is not modified.
      *)


end
