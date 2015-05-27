theory Protocol
imports "../Common/Negation_Type"
begin

datatype primitive_protocol = TCP | UDP | ICMP

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

end
