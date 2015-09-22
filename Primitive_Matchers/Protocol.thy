theory Protocol
imports "../Common/Negation_Type"
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
  
  lemma ipt_tcp_flags_matchany: "match_tcp_flags (TCP_Flags {} {}) pkt" by(simp)
  
  fun match_tcp_flags_conjunct :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags" where
    "match_tcp_flags_conjunct (TCP_Flags mask1 c1) (TCP_Flags mask2 c2) = (
          if c1 \<subseteq> mask1 \<and> c2 \<subseteq> mask2 \<and> mask1 \<inter> mask2 \<inter> c1 = mask1 \<inter> mask2 \<inter> c2
          then (TCP_Flags (mask1 \<union> mask2) (c1 \<union> c2))
          else ipt_tcp_flags_NoMatch)"
  
  
  lemma match_tcp_flags_conjunct: "match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt \<longleftrightarrow> match_tcp_flags (match_tcp_flags_conjunct f1 f2) pkt"
    apply(cases f1, cases f2, simp)
    apply(rename_tac mask1 c1 mask2 c2)
    apply(intro conjI impI)
     apply(elim conjE)
     apply blast
    apply(simp add: ipt_tcp_flags_NoMatch)
    apply fast
    done

  fun tcp_flag_toString :: "tcp_flag \<Rightarrow> string" where
    "tcp_flag_toString TCP_SYN = ''TCP_SYN''" |
    "tcp_flag_toString TCP_ACK = ''TCP_ACK''" |
    "tcp_flag_toString TCP_FIN = ''TCP_FIN''" |
    "tcp_flag_toString TCP_RST = ''TCP_RST''" |
    "tcp_flag_toString TCP_URG = ''TCP_URG''" |
    "tcp_flag_toString TCP_PSH = ''TCP_PSH''"



  (*TODO: move to generic toString*)
  fun enum_one_in_set_toString :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> (string \<times> 'a set option)" where
    "enum_one_in_set_toString _     []     S = ('''', None)" |
    "enum_one_in_set_toString toStr (s#ss) S = (if s \<in> S then (toStr s, Some (S - {s})) else enum_one_in_set_toString toStr ss S)"

  lemma enum_one_in_set_toString_finite_card_le: "finite S \<Longrightarrow> (x, Some S') = enum_one_in_set_toString toStr ss S \<Longrightarrow> card S' < card S"
    apply(induction ss)
     apply(simp)
    apply(simp split: split_if_asm)
    by (metis card_gt_0_iff diff_less equals0D lessI)
    
  

  function enum_set_toString_list :: "('a \<Rightarrow> string) \<Rightarrow> ('a::enum) set \<Rightarrow> string list" where
    "enum_set_toString_list toStr S = (if S = {} then [] else
      case enum_one_in_set_toString toStr (Enum.enum) S of (_, None) \<Rightarrow> []
                                               |  (str, Some S') \<Rightarrow> str#enum_set_toString_list toStr S')"
  by(pat_completeness) auto
  
  termination enum_set_toString_list
  apply (relation "measure (\<lambda>(_,S). card S)")
  apply(simp_all add: card_gt_0_iff enum_one_in_set_toString_finite_card_le)
  done

  value[code] "enum_set_toString_list tcp_flag_toString {TCP_SYN,TCP_SYN,TCP_ACK}"
end
