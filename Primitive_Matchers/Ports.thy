theory Ports
imports String 
  "~~/src/HOL/Word/Word"
  "../Bitmagic/WordInterval_Lists" 
begin

section{*Ports (layer 4)*}
text{*E.g. source and destination ports for TCP/UDP*}


text{*list of (start, end) port ranges*}
type_synonym ipt_ports = "(16 word \<times> 16 word) list"

fun ports_to_set :: "ipt_ports \<Rightarrow> (16 word) set" where
  "ports_to_set [] = {}" |
  "ports_to_set ((s,e)#ps) = {s..e} \<union> ports_to_set ps"

lemma ports_to_set: "ports_to_set pts = \<Union> {{s..e} | s e . (s,e) \<in> set pts}"
  proof(induction pts)
  case Nil thus ?case by simp
  next
  case (Cons p pts) thus ?case by(cases p, simp, blast)
  qed

text{*We can reuse the wordinterval theory to reason about ports*}
lemma ports_to_set_wordinterval: "ports_to_set ps = wordinterval_to_set (l2br ps)"
  by(induction ps rule: l2br.induct) (auto)

end
