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

datatype 'a rule = Rule (get_match: "'a match_expr") (get_action: action)


definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"

end
