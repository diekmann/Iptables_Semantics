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

lemma ipt_tcp_flags_matchany: "match_tcp_flags (TCP_Flags {} {}) pkt" by(simp)


(*
fun match_tcp_flags_conjunct :: "ipt_tcp_flags \<Rightarrow> ipt_tcp_flags \<Rightarrow> ipt_tcp_flags" where
  "match_tcp_flags_conjunct (TCP_Flags mask1 c1) (TCP_Flags mask2 c2) = (TCP_Flags ((mask1 \<inter> c1) \<union> (mask2 \<inter> c2)) (c1 \<union> c2))"*)

(*a conjunct is possible*)
lemma "\<exists>mask3 c3. \<forall>pkt. match_tcp_flags f1 pkt \<and> match_tcp_flags f2 pkt \<longleftrightarrow> match_tcp_flags (TCP_Flags mask3 c3) pkt"
  apply(cases f1, cases f2, simp)
  apply(rename_tac mask1 c1 mask2 c2)
  apply(case_tac "c1 \<subseteq> mask1 \<and> c2 \<subseteq> mask2")
   prefer 2
   apply(rule_tac x="{}" in exI)
   apply(rule_tac x="{TCP_SYN}" in exI)
   apply(clarify)
   apply blast (*MatchNone*)
  apply(case_tac "mask1 \<inter> mask2 = {}")
   apply(rule_tac x="mask1 \<union> mask2" in exI)
   apply(rule_tac x="c1 \<union> c2" in exI)
   apply(clarify)
   apply blast
  apply(case_tac "c1 \<inter> c2 \<subseteq> mask1 \<inter> mask2")
   prefer 2
   apply(rule_tac x="{}" in exI)
   apply(rule_tac x="{TCP_SYN}" in exI)
   apply(clarify)
   apply blast (*MatchNone*)
  apply(case_tac "mask1 \<inter> mask2 \<inter> c1 \<noteq> mask1 \<inter> mask2 \<inter> c2")
   apply(rule_tac x="{}" in exI)
   apply(rule_tac x="{TCP_SYN}" in exI)
   apply(clarify)
   apply blast (*MatchNone*)
  apply(simp)
  apply(rule_tac x="mask1 \<union> mask2" in exI)
  apply(rule_tac x="c1 \<union> c2" in exI)
  apply(clarify)
  by blast

lemma "(\<exists>f. f \<in> mask1 \<and> f \<in> mask2 \<and> (f \<in> c2 \<and> f \<notin> c1 \<or> f \<in> c1 \<and> f \<notin> c2)) \<longleftrightarrow> mask1 \<inter> mask2 \<inter> c1 \<noteq> mask1 \<inter> mask2 \<inter> c2"
  by blast


end
