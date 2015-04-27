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


definition "ports_invert" :: "ipt_ports \<Rightarrow> ipt_ports" where
  "ports_invert ps = br2l (wordinterval_invert (l2br ps))"

lemma ports_invert: "ports_to_set (ports_invert ps) = - ports_to_set ps"
  by(auto simp add: ports_invert_def l2br_br2l ports_to_set_wordinterval)

end
