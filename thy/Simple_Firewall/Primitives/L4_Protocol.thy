theory L4_Protocol
imports "../Common/Lib_Enum_toString" "~~/src/HOL/Word/Word"
begin

section\<open>Transport Layer Protocols\<close>
type_synonym primitive_protocol = "8 word"

definition "ICMP \<equiv> 1 :: 8 word"
definition "TCP \<equiv> 6 :: 8 word"
definition "UDP \<equiv> 17 :: 8 word"
context begin (*let's not pollute the namespace too much*)
qualified definition "SCTP \<equiv> 132  :: 8 word"
qualified definition "IGMP \<equiv> 2 :: 8 word"
qualified definition "GRE \<equiv> 47 :: 8 word"
qualified definition "ESP \<equiv> 50 :: 8 word"
qualified definition "AH \<equiv> 51 :: 8 word"
qualified definition "IPv6ICMP \<equiv> 58 :: 8 word"
end
(* turn http://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml into a separate file or so? *)

datatype protocol = ProtoAny | Proto "primitive_protocol"

fun match_proto :: "protocol \<Rightarrow> primitive_protocol \<Rightarrow> bool" where
  "match_proto ProtoAny _ \<longleftrightarrow> True" |
  "match_proto (Proto (p)) p_p \<longleftrightarrow> p_p = p"

  fun simple_proto_conjunct :: "protocol \<Rightarrow> protocol \<Rightarrow> protocol option" where
    "simple_proto_conjunct ProtoAny proto = Some proto" |
    "simple_proto_conjunct proto ProtoAny = Some proto" |
    "simple_proto_conjunct (Proto p1) (Proto p2) = (if p1 = p2 then Some (Proto p1) else None)"
  lemma simple_proto_conjunct_asimp[simp]: "simple_proto_conjunct proto ProtoAny = Some proto"
    by(cases proto) simp_all

  lemma simple_proto_conjunct_correct: "match_proto p1 pkt \<and> match_proto p2 pkt \<longleftrightarrow> 
    (case simple_proto_conjunct p1 p2 of None \<Rightarrow> False | Some proto \<Rightarrow> match_proto proto pkt)"
    apply(cases p1)
     apply(simp_all)
    apply(cases p2)
     apply(simp_all)
    done

  lemma simple_proto_conjunct_Some: "simple_proto_conjunct p1 p2 = Some proto \<Longrightarrow> 
    match_proto proto pkt \<longleftrightarrow> match_proto p1 pkt \<and> match_proto p2 pkt"
    using simple_proto_conjunct_correct by simp
  lemma simple_proto_conjunct_None: "simple_proto_conjunct p1 p2 = None \<Longrightarrow> 
    \<not> (match_proto p1 pkt \<and> match_proto p2 pkt)"
    using simple_proto_conjunct_correct by simp

  lemma conjunctProtoD:
    "simple_proto_conjunct a (Proto b) = Some x \<Longrightarrow> x = Proto b \<and> (a = ProtoAny \<or> a = Proto b)"
  by(cases a) (simp_all split: if_splits)
  lemma conjunctProtoD2:
    "simple_proto_conjunct (Proto b) a = Some x \<Longrightarrow> x = Proto b \<and> (a = ProtoAny \<or> a = Proto b)"
  by(cases a) (simp_all split: if_splits)

  text\<open>Originally, there was a @{typ nat} in the protocol definition, allowing infinitely many protocols 
        This was intended behavior. We want to prevent things such as @{term "\<not>TCP = UDP"}.
        So be careful with what you prove...\<close>
  lemma primitive_protocol_Ex_neq: "p = Proto pi \<Longrightarrow> \<exists>p'. p' \<noteq> pi" 
  proof
  	show "pi + 1 \<noteq> pi" by simp
  qed
  lemma protocol_Ex_neq: "\<exists>p'. Proto p' \<noteq> p"
    by(cases p) (simp_all add: primitive_protocol_Ex_neq)

section\<open>TCP flags\<close>
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

subsection\<open>TCP Flags to String\<close>
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
