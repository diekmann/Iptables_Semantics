theory Ports
imports String 
  "~~/src/HOL/Word/Word"
  "../../IP_Addresses/WordInterval_Lists" 
begin

section\<open>Ports (layer 4)\<close>
text\<open>E.g. source and destination ports for TCP/UDP\<close>


text\<open>list of (start, end) port ranges\<close>
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

text\<open>We can reuse the wordinterval theory to reason about ports\<close>
lemma ports_to_set_wordinterval: "ports_to_set ps = wordinterval_to_set (l2wi ps)"
  by(induction ps rule: l2wi.induct) (auto)


definition "ports_invert" :: "ipt_ports \<Rightarrow> ipt_ports" where
  "ports_invert ps = wi2l (wordinterval_invert (l2wi ps))"

lemma ports_invert: "ports_to_set (ports_invert ps) = - ports_to_set ps"
  by(auto simp add: ports_invert_def l2wi_wi2l ports_to_set_wordinterval)

end
