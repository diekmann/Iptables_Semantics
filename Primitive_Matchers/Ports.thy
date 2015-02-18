theory Ports
imports String 
  "~~/src/HOL/Word/Word"
  "../Bitmagic/BitrangeLists" 
begin

section{*Ports (layer 4)*}

text{*list of (start, end) port ranges*}
type_synonym ipt_ports = "(16 word \<times> 16 word) list"


fun ports_to_set :: "ipt_ports \<Rightarrow> (16 word) set" where
  "ports_to_set [] = {}" |
  "ports_to_set ((s,e)#ps) = {s..e} \<union> ports_to_set ps"

lemma ports_to_set: "ports_to_set pts = \<Union> {{s..e} | s e . (s,e) \<in> set pts}"
  apply(induction pts)
   apply(simp)
  apply(rename_tac p pts, case_tac p)
  apply(simp)
  by blast

text{*We can reuse the bitrange theory to reason about ports*}
lemma ports_to_set_bitrange: "ports_to_set ps = bitrange_to_set (l2br ps)"
  by(induction ps rule: l2br.induct) (auto)

end
