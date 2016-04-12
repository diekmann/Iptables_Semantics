theory Firewall_Common
imports Main Firewall_Common_Decision_State
begin

section{*Firewall Basic Syntax*}

text{*
Our firewall model supports the following actions.
*}
datatype action = Accept | Drop | Log | Reject | Call string | Return | Goto string | Empty | Unknown

text{*
The type parameter @{typ 'a} denotes the primitive match condition For example, matching
on source IP address or on protocol.
We list the primitives to an algebra. Note that we do not have an Or expression.
*}
datatype 'a match_expr = Match 'a | MatchNot "'a match_expr" | MatchAnd "'a match_expr" "'a match_expr" | MatchAny

definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"


datatype 'a rule = Rule (get_match: "'a match_expr") (get_action: action)

lemma rules_singleton_rev_E: "[Rule m a] = rs\<^sub>1 @ rs\<^sub>2 \<Longrightarrow> (rs\<^sub>1 = [Rule m a] \<Longrightarrow> rs\<^sub>2 = [] \<Longrightarrow> P m a) \<Longrightarrow> (rs\<^sub>1 = [] \<Longrightarrow> rs\<^sub>2 = [Rule m a] \<Longrightarrow> P m a) \<Longrightarrow> P m a"
by (cases rs\<^sub>1) auto




section{*Basic Algorithms*}
text{*These algorithms should be valid for all firewall models. The corresponding proofs follow once the semantics are defined. *}


text{*The actions Log and Empty do not modify the packet processing in any way. They can be removed.*}
fun rm_LogEmpty :: "'a rule list \<Rightarrow> 'a rule list" where
  "rm_LogEmpty [] = []" |
  "rm_LogEmpty ((Rule _ Empty)#rs) = rm_LogEmpty rs" |
  "rm_LogEmpty ((Rule _ Log)#rs) = rm_LogEmpty rs" |
  "rm_LogEmpty (r#rs) = r # rm_LogEmpty rs"

lemma rm_LogEmpty_filter: "rm_LogEmpty rs = filter (\<lambda>r. get_action r \<noteq> Log \<and> get_action r \<noteq> Empty) rs"
 by(induction rs rule: rm_LogEmpty.induct) (simp_all)

lemma rm_LogEmpty_seq: "rm_LogEmpty (rs1@rs2) = rm_LogEmpty rs1 @ rm_LogEmpty rs2"
  by(simp add: rm_LogEmpty_filter)





text{*Optimize away MatchAny matches*}
fun opt_MatchAny_match_expr :: "'a match_expr \<Rightarrow> 'a match_expr" where
  "opt_MatchAny_match_expr MatchAny = MatchAny" |
  "opt_MatchAny_match_expr (Match a) = (Match a)" |
  "opt_MatchAny_match_expr (MatchNot (MatchNot m)) = (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchNot m) = MatchNot (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchAnd MatchAny MatchAny) = MatchAny" |
  "opt_MatchAny_match_expr (MatchAnd MatchAny m) = (opt_MatchAny_match_expr m)" |
  (*note: remove recursive call to opt_MatchAny_match_expr to make it probably faster*)
  "opt_MatchAny_match_expr (MatchAnd m MatchAny) = (opt_MatchAny_match_expr m)" |
  "opt_MatchAny_match_expr (MatchAnd _ (MatchNot MatchAny)) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) _) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr (MatchAnd m1 m2) = MatchAnd (opt_MatchAny_match_expr m1) (opt_MatchAny_match_expr m2)"
(* without recursive call: need to apply multiple times until it stabelizes *)


text{*It is still a good idea to apply @{const opt_MatchAny_match_expr} multiple times. Example:*}
lemma "MatchNot (opt_MatchAny_match_expr (MatchAnd MatchAny (MatchNot MatchAny))) = MatchNot (MatchNot MatchAny)" by simp
lemma "m = (MatchAnd (MatchAnd MatchAny MatchAny) (MatchAnd MatchAny MatchAny)) \<Longrightarrow> 
  (opt_MatchAny_match_expr^^2) m \<noteq> opt_MatchAny_match_expr m" by(simp add: funpow_def)

end
