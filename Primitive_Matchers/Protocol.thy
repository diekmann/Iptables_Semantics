theory Protocol
imports "../Output_Format/Negation_Type"
begin

datatype primitive_protocol = TCP | UDP | ICMP

datatype protocol = ProtoAny | Proto "primitive_protocol negation_type"

fun match_proto :: "protocol \<Rightarrow> primitive_protocol \<Rightarrow> bool" where
  "match_proto ProtoAny _ \<longleftrightarrow> True" |
  "match_proto (Proto (Pos p)) p_p \<longleftrightarrow> p_p = p" |
  "match_proto (Proto (Neg p)) p_p \<longleftrightarrow> p_p \<noteq> p"

end
