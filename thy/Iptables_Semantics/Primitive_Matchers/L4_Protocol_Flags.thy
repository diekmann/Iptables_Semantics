theory L4_Protocol_Flags
imports "../../Simple_Firewall/Primitives/L4_Protocol"
begin

section\<open>Matching TCP Flags\<close>
  (*man iptables-extensions, [!] --tcp-flags mask comp*)
  datatype ipt_tcp_flags = TCP_Flags "tcp_flag set" --"mask"
                                     "tcp_flag set" --"comp"
  
  (*--syn: Only match TCP packets with the SYN bit set and the ACK,RST and FIN bits cleared. [...] It is equivalent to --tcp-flags SYN,RST,ACK,FIN SYN.*)
  definition ipt_tcp_syn :: "ipt_tcp_flags" where
    "ipt_tcp_syn \<equiv> TCP_Flags {TCP_SYN,TCP_RST,TCP_ACK,TCP_FIN} {TCP_SYN}"
  
  fun match_tcp_flags :: "ipt_tcp_flags \<Rightarrow> tcp_flag set \<Rightarrow> bool" where
     "match_tcp_flags (TCP_Flags fmask c) flags \<longleftrightarrow> (flags \<inter> fmask) = c"
  
  lemma "match_tcp_flags ipt_tcp_syn {TCP_SYN, TCP_URG, TCP_PSH}" by eval
  
  lemma match_tcp_flags_nomatch: "\<not> c \<subseteq> fmask \<Longrightarrow> \<not> match_tcp_flags (TCP_Flags fmask c) pkt" by auto
  
  definition ipt_tcp_flags_NoMatch :: "ipt_tcp_flags" where
    "ipt_tcp_flags_NoMatch \<equiv> TCP_Flags {} {TCP_SYN}"
  lemma ipt_tcp_flags_NoMatch: "\<not> match_tcp_flags ipt_tcp_flags_NoMatch pkt" by(simp add: ipt_tcp_flags_NoMatch_def)
  
  definition ipt_tcp_flags_Any :: ipt_tcp_flags where
    "ipt_tcp_flags_Any \<equiv> TCP_Flags {} {}"
  lemma ipt_tcp_flags_Any: "match_tcp_flags ipt_tcp_flags_Any pkt" by(simp add: ipt_tcp_flags_Any_def)

  lemma ipt_tcp_flags_Any_isUNIV: "fmask = {} \<and> c = {} \<longleftrightarrow> (\<forall>pkt. match_tcp_flags (TCP_Flags fmask c) pkt)" by auto
  
  fun match_tcp_flags_conjunct :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags" where
    "match_tcp_flags_conjunct (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) = (
          if c1 \<subseteq> fmask1 \<and> c2 \<subseteq> fmask2 \<and> fmask1 \<inter> fmask2 \<inter> c1 = fmask1 \<inter> fmask2 \<inter> c2
          then (TCP_Flags (fmask1 \<union> fmask2) (c1 \<union> c2))
          else ipt_tcp_flags_NoMatch)"
  
  lemma match_tcp_flags_conjunct: "match_tcp_flags (match_tcp_flags_conjunct f1 f2) pkt \<longleftrightarrow> match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt"
    apply(cases f1, cases f2, simp)
    apply(rename_tac fmask1 c1 fmask2 c2)
    apply(intro conjI impI)
     apply(elim conjE)
     apply blast
    apply(simp add: ipt_tcp_flags_NoMatch)
    apply fast
    done
  declare match_tcp_flags_conjunct.simps[simp del]


  text\<open>Same as @{const match_tcp_flags_conjunct}, but returns @{const None} if result cannot match anyway\<close>
  definition match_tcp_flags_conjunct_option :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags option" where
    "match_tcp_flags_conjunct_option f1 f2 = (case match_tcp_flags_conjunct f1 f2 of (TCP_Flags fmask c) \<Rightarrow> if c \<subseteq> fmask then Some (TCP_Flags fmask c) else None)"

  lemma "match_tcp_flags_conjunct_option ipt_tcp_syn (TCP_Flags {TCP_RST,TCP_ACK} {TCP_RST}) = None" by eval


  lemma match_tcp_flags_conjunct_option_Some: "match_tcp_flags_conjunct_option f1 f2 = Some f3 \<Longrightarrow>
      match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt \<longleftrightarrow> match_tcp_flags f3 pkt"
    apply(simp add: match_tcp_flags_conjunct_option_def split: ipt_tcp_flags.split_asm split_if_asm)
    using match_tcp_flags_conjunct by blast
  lemma match_tcp_flags_conjunct_option_None: "match_tcp_flags_conjunct_option f1 f2 = None \<Longrightarrow>
      \<not>(match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt)"
    apply(simp add: match_tcp_flags_conjunct_option_def split: ipt_tcp_flags.split_asm split_if_asm)
    using match_tcp_flags_conjunct match_tcp_flags_nomatch by metis

  lemma match_tcp_flags_conjunct_option: "(case match_tcp_flags_conjunct_option f1 f2 of None \<Rightarrow> False | Some f3 \<Rightarrow> match_tcp_flags f3 pkt) \<longleftrightarrow> match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt"
    apply(simp split: option.split)
    using match_tcp_flags_conjunct_option_Some match_tcp_flags_conjunct_option_None by blast



  fun ipt_tcp_flags_equal :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> bool" where
    "ipt_tcp_flags_equal (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) = (
          if c1 \<subseteq> fmask1 \<and> c2 \<subseteq> fmask2
          then c1 = c2 \<and> fmask1 = fmask2
          else  (\<not> c1 \<subseteq> fmask1) \<and> (\<not> c2 \<subseteq> fmask2))"
  context
  begin
    private lemma funny_set_falg_fmask_helper: "c2 \<subseteq> fmask2 \<Longrightarrow> (c1 = c2 \<and> fmask1 = fmask2) = (\<forall>pkt. (pkt \<inter> fmask1 = c1) = (pkt \<inter> fmask2 = c2))"
    apply rule
     apply presburger
    apply(subgoal_tac "fmask1 = fmask2")
     apply blast
    (*"e": Try this: by (metis Diff_Compl Diff_eq Int_lower2 Un_Diff_Int compl_sup disjoint_eq_subset_Compl inf_assoc inf_commute inf_sup_absorb) (> 1.0 s, timed out).
      Isar proof (300 ms):*)
    proof -
      assume a1: "c2 \<subseteq> fmask2"
      assume a2: "\<forall>pkt. (pkt \<inter> fmask1 = c1) = (pkt \<inter> fmask2 = c2)"
      have f3: "\<And>A Aa. (A::'a set) - - Aa = Aa - - A"
        by (simp add: inf_commute)
      have f4: "\<And>A Aa. (A::'a set) - - (- Aa) = A - Aa"
        by simp
      have f5: "\<And>A Aa Ab. (A::'a set) - - Aa - - Ab = A - - (Aa - - Ab)"
        by blast
      have f6: "\<And>A Aa. (A::'a set) - (- A - Aa) = A"
        by fastforce
      have f7: "\<And>A Aa. - (A::'a set) - - Aa = Aa - A"
        using f4 f3 by presburger
      have f8: "\<And>A Aa. - (A::'a set) = - (A - Aa) - (A - - Aa)"
        by blast
      have f9: "c1 = - (- c1)"
        by blast
      have f10: "\<And>A. A - c1 - c1 = A - c1"
        by blast
      have "\<And>A. A - - (fmask1 - - fmask2) = c2 \<or> A - - fmask1 \<noteq> c1"
        using f6 f5 a2 by (metis (no_types) Diff_Compl)
      hence f11: "\<And>A. - A - - (fmask1 - - fmask2) = c2 \<or> fmask1 - A \<noteq> c1"
        using f7 by meson
      have "c2 - fmask2 = {}"
        using a1 by force
      hence f12: "- c2 - (fmask2 - c2) = - fmask2"
        by blast
      hence "fmask2 - - c2 = c2"
        by blast
      hence f13: "fmask1 - - c2 = c1"
        using f3 a2 by simp
      hence f14: "c1 = c2"
        using f11 by blast
      hence f15: "fmask2 - (fmask1 - c1) = c1"
        using f13 f10 f9 f8 f7 f3 a2 by (metis Diff_Compl)
      have "fmask1 - (fmask2 - c1) = c1"
        using f14 f12 f10 f9 f8 f4 f3 a2 by (metis Diff_Compl)
      thus "fmask1 = fmask2"
        using f15 by blast
    qed
  
    lemma ipt_tcp_flags_equal: "ipt_tcp_flags_equal f1 f2 \<longleftrightarrow> (\<forall>pkt. match_tcp_flags f1 pkt = match_tcp_flags f2 pkt)"
      apply(cases f1, cases f2, simp)
      apply(rename_tac fmask1 c1 fmask2 c2)
      apply(intro conjI impI)
       using funny_set_falg_fmask_helper apply metis
      apply blast
     done
  end
  declare ipt_tcp_flags_equal.simps[simp del]
end
