theory Protocol
imports "../Common/Negation_Type" "../Common/Lib_toString"
begin

section{*Protocols*}

datatype primitive_protocol = TCP | UDP | ICMP | OtherProtocol nat

datatype protocol = ProtoAny | Proto "primitive_protocol" (*probably negation_type?*)

(*TODO add negation type. Conjunction is still easy since we don't have wildcards
  E.g. TCP \<and> \<not> UDP \<longleftrightarrow> TCP
       TCP \<and> \<not> TCP \<longleftrightarrow> False
       TCP \<and> UDP \<longleftrightarrow> TCP = UDP
*)

fun match_proto :: "protocol \<Rightarrow> primitive_protocol \<Rightarrow> bool" where
  "match_proto ProtoAny _ \<longleftrightarrow> True" |
  "match_proto (Proto (p)) p_p \<longleftrightarrow> p_p = p"

  fun simple_proto_conjunct :: "protocol \<Rightarrow> protocol \<Rightarrow> protocol option" where
    "simple_proto_conjunct ProtoAny proto = Some proto" |
    "simple_proto_conjunct proto ProtoAny = Some proto" |
    "simple_proto_conjunct (Proto p1) (Proto p2) = (if p1 = p2 then Some (Proto p1) else None)"

  lemma simple_proto_conjunct_correct: "match_proto p1 pkt \<and> match_proto p2 pkt \<longleftrightarrow> 
    (case simple_proto_conjunct p1 p2 of None \<Rightarrow> False | Some proto \<Rightarrow> match_proto proto pkt)"
    apply(cases p1)
     apply(simp_all)
    apply(rename_tac pp1)
    apply(cases p2)
     apply(simp_all)
    done


section{*TCP flags*}
  datatype tcp_flag = TCP_SYN | TCP_ACK | TCP_FIN | TCP_RST | TCP_URG | TCP_PSH (*| TCP_ALL | TCP_NONE*)

  lemma UNIV_tcp_flag: "UNIV = {TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST, TCP_URG, TCP_PSH}" using tcp_flag.exhaust by auto 
  instance tcp_flag :: finite
  proof
    from UNIV_tcp_flag show "finite (UNIV:: tcp_flag set)" using finite.simps by auto 
  qed
  instantiation "tcp_flag" :: enum
  begin
    definition "enum_tcp_flag = [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST, TCP_URG, TCP_PSH]"
  
    definition "enum_all_tcp_flag P \<longleftrightarrow> P TCP_SYN \<and> P TCP_ACK \<and> P TCP_FIN \<and> P TCP_RST \<and> P TCP_URG \<and> P TCP_PSH"
    
    definition "enum_ex_tcp_flag P \<longleftrightarrow> P TCP_SYN \<or> P TCP_ACK \<or> P TCP_FIN \<or> P TCP_RST \<or> P TCP_URG \<or> P TCP_PSH"
  instance proof
    show "UNIV = set (enum_class.enum :: tcp_flag list)"
      by(simp add: UNIV_tcp_flag enum_tcp_flag_def)
    next
    show "distinct (enum_class.enum :: tcp_flag list)"
      by(simp add: enum_tcp_flag_def)
    next
    show "\<And>P. (enum_class.enum_all :: (tcp_flag \<Rightarrow> bool) \<Rightarrow> bool) P = Ball UNIV P"
      by(simp add: UNIV_tcp_flag enum_all_tcp_flag_def)
    next
    show "\<And>P. (enum_class.enum_ex :: (tcp_flag \<Rightarrow> bool) \<Rightarrow> bool) P = Bex UNIV P"
      by(simp add: UNIV_tcp_flag enum_ex_tcp_flag_def)
  qed
  end
  
  (*man iptables-extensions, [!] --tcp-flags mask comp*)
  datatype ipt_tcp_flags = TCP_Flags "tcp_flag set" --"mask"
                                     "tcp_flag set" --"comp"
  
  (*--syn: Only match TCP packets with the SYN bit set and the ACK,RST and FIN bits cleared. [...] It is equivalent to --tcp-flags SYN,RST,ACK,FIN SYN.*)
  definition ipt_tcp_syn :: "ipt_tcp_flags" where
    "ipt_tcp_syn \<equiv> TCP_Flags {TCP_SYN,TCP_RST,TCP_ACK,TCP_FIN} {TCP_SYN}"
  
  fun match_tcp_flags :: "ipt_tcp_flags \<Rightarrow> tcp_flag set \<Rightarrow> bool" where
     "match_tcp_flags (TCP_Flags mask c) flags \<longleftrightarrow> (flags \<inter> mask) = c"
  
  lemma "match_tcp_flags ipt_tcp_syn {TCP_SYN, TCP_URG, TCP_PSH}" by eval
  
  lemma match_tcp_flags_nomatch: "\<not> c \<subseteq> mask \<Longrightarrow> \<not> match_tcp_flags (TCP_Flags mask c) pkt" by auto
  
  definition ipt_tcp_flags_NoMatch :: "ipt_tcp_flags" where
    "ipt_tcp_flags_NoMatch \<equiv> TCP_Flags {} {TCP_SYN}"
  lemma ipt_tcp_flags_NoMatch: "\<not> match_tcp_flags ipt_tcp_flags_NoMatch pkt" by(simp add: ipt_tcp_flags_NoMatch_def)
  
  definition ipt_tcp_flags_Any :: ipt_tcp_flags where
    "ipt_tcp_flags_Any \<equiv> TCP_Flags {} {}"
  lemma ipt_tcp_flags_Any: "match_tcp_flags ipt_tcp_flags_Any pkt" by(simp add: ipt_tcp_flags_Any_def)

  lemma ipt_tcp_flags_Any_isUNIV: "mask = {} \<and> c = {} \<longleftrightarrow> (\<forall>pkt. match_tcp_flags (TCP_Flags mask c) pkt)" by auto
  
  fun match_tcp_flags_conjunct :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags" where
    "match_tcp_flags_conjunct (TCP_Flags mask1 c1) (TCP_Flags mask2 c2) = (
          if c1 \<subseteq> mask1 \<and> c2 \<subseteq> mask2 \<and> mask1 \<inter> mask2 \<inter> c1 = mask1 \<inter> mask2 \<inter> c2
          then (TCP_Flags (mask1 \<union> mask2) (c1 \<union> c2))
          else ipt_tcp_flags_NoMatch)"
  
  lemma match_tcp_flags_conjunct: "match_tcp_flags (match_tcp_flags_conjunct f1 f2) pkt \<longleftrightarrow> match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt"
    apply(cases f1, cases f2, simp)
    apply(rename_tac mask1 c1 mask2 c2)
    apply(intro conjI impI)
     apply(elim conjE)
     apply blast
    apply(simp add: ipt_tcp_flags_NoMatch)
    apply fast
    done
  declare match_tcp_flags_conjunct.simps[simp del]


  text{*Same as @{const match_tcp_flags_conjunct}, but returns @{const None} if result cannot match anyway*}
  definition match_tcp_flags_conjunct_option :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags option" where
    "match_tcp_flags_conjunct_option f1 f2 = (case match_tcp_flags_conjunct f1 f2 of (TCP_Flags mask c) \<Rightarrow> if c \<subseteq> mask then Some (TCP_Flags mask c) else None)"

  lemma match_tcp_flags_conjunct_option: "(case match_tcp_flags_conjunct_option f1 f2 of None \<Rightarrow> False | Some f3 \<Rightarrow> match_tcp_flags f3 pkt) \<longleftrightarrow> match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt"
    apply(simp add: match_tcp_flags_conjunct_option_def)
    apply(case_tac "match_tcp_flags_conjunct f1 f2")
    apply(simp del: match_tcp_flags.simps)
    apply(rule conjI impI)
     using match_tcp_flags_conjunct apply metis
    using match_tcp_flags_conjunct match_tcp_flags_nomatch apply metis
    done



  fun ipt_tcp_flags_equal :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> bool" where
    "ipt_tcp_flags_equal (TCP_Flags mask1 c1) (TCP_Flags mask2 c2) = (
          if c1 \<subseteq> mask1 \<and> c2 \<subseteq> mask2
          then c1 = c2 \<and> mask1 = mask2
          else  (\<not> c1 \<subseteq> mask1) \<and> (\<not> c2 \<subseteq> mask2))"
  context
  begin
    private lemma funny_set_falg_mask_helper: "c2 \<subseteq> mask2 \<Longrightarrow> (c1 = c2 \<and> mask1 = mask2) = (\<forall>pkt. (pkt \<inter> mask1 = c1) = (pkt \<inter> mask2 = c2))"
    apply rule
     apply presburger
    apply(subgoal_tac "mask1 = mask2")
     apply blast
    (*"e": Try this: by (metis Diff_Compl Diff_eq Int_lower2 Un_Diff_Int compl_sup disjoint_eq_subset_Compl inf_assoc inf_commute inf_sup_absorb) (> 1.0 s, timed out).
      Isar proof (300 ms):*)
    proof -
      assume a1: "c2 \<subseteq> mask2"
      assume a2: "\<forall>pkt. (pkt \<inter> mask1 = c1) = (pkt \<inter> mask2 = c2)"
      have f3: "\<And>A Aa. (A\<Colon>'a set) - - Aa = Aa - - A"
        by (simp add: inf_commute)
      have f4: "\<And>A Aa. (A\<Colon>'a set) - - (- Aa) = A - Aa"
        by simp
      have f5: "\<And>A Aa Ab. (A\<Colon>'a set) - - Aa - - Ab = A - - (Aa - - Ab)"
        by blast
      have f6: "\<And>A Aa. (A\<Colon>'a set) - (- A - Aa) = A"
        by fastforce
      have f7: "\<And>A Aa. - (A\<Colon>'a set) - - Aa = Aa - A"
        using f4 f3 by presburger
      have f8: "\<And>A Aa. - (A\<Colon>'a set) = - (A - Aa) - (A - - Aa)"
        by blast
      have f9: "c1 = - (- c1)"
        by blast
      have f10: "\<And>A. A - c1 - c1 = A - c1"
        by blast
      have "\<And>A. A - - (mask1 - - mask2) = c2 \<or> A - - mask1 \<noteq> c1"
        using f6 f5 a2 by (metis (no_types) Diff_Compl)
      hence f11: "\<And>A. - A - - (mask1 - - mask2) = c2 \<or> mask1 - A \<noteq> c1"
        using f7 by meson
      have "c2 - mask2 = {}"
        using a1 by force
      hence f12: "- c2 - (mask2 - c2) = - mask2"
        by blast
      hence "mask2 - - c2 = c2"
        by blast
      hence f13: "mask1 - - c2 = c1"
        using f3 a2 by simp
      hence f14: "c1 = c2"
        using f11 by blast
      hence f15: "mask2 - (mask1 - c1) = c1"
        using f13 f10 f9 f8 f7 f3 a2 by (metis Diff_Compl)
      have "mask1 - (mask2 - c1) = c1"
        using f14 f12 f10 f9 f8 f4 f3 a2 by (metis Diff_Compl)
      thus "mask1 = mask2"
        using f15 by blast
    qed
  
    lemma ipt_tcp_flags_equal: "ipt_tcp_flags_equal f1 f2 \<longleftrightarrow> (\<forall>pkt. match_tcp_flags f1 pkt = match_tcp_flags f2 pkt)"
      apply(cases f1, cases f2, simp)
      apply(rename_tac mask1 c1 mask2 c2)
      apply(intro conjI impI)
       using funny_set_falg_mask_helper apply metis
      apply blast
     done
  end
  declare ipt_tcp_flags_equal.simps[simp del]


  fun tcp_flag_toString :: "tcp_flag \<Rightarrow> string" where
    "tcp_flag_toString TCP_SYN = ''TCP_SYN''" |
    "tcp_flag_toString TCP_ACK = ''TCP_ACK''" |
    "tcp_flag_toString TCP_FIN = ''TCP_FIN''" |
    "tcp_flag_toString TCP_RST = ''TCP_RST''" |
    "tcp_flag_toString TCP_URG = ''TCP_URG''" |
    "tcp_flag_toString TCP_PSH = ''TCP_PSH''"


  definition ipt_tcp_flags_toString :: "tcp_flag set \<Rightarrow> char list" where
    "ipt_tcp_flags_toString flags \<equiv> list_toString tcp_flag_toString (enum_set_to_list flags)"

  lemma "ipt_tcp_flags_toString {TCP_SYN,TCP_SYN,TCP_ACK} = ''[TCP_SYN, TCP_ACK]''" by eval
end
