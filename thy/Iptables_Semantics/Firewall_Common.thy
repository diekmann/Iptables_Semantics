section\<open>Firewall Basic Syntax\<close>
theory Firewall_Common
imports Main "../Simple_Firewall/Firewall_Common_Decision_State" 
  "Common/Repeat_Stabilize"
begin

text\<open>
Our firewall model supports the following actions.
\<close>
datatype action = Accept | Drop | Log | Reject | Call string | Return | Goto string | Empty | Unknown

text\<open>
We support the following algebra over primitives of type @{typ 'a}. 
The type parameter @{typ 'a} denotes the primitive match condition. For example, matching
on source IP address or on protocol.
We lift the primitives to an algebra. Note that we do not have an Or expression.
\<close>
datatype 'a match_expr = Match 'a
                       | MatchNot "'a match_expr"
                       | MatchAnd "'a match_expr" "'a match_expr"
                       | MatchAny

definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"

text\<open>A firewall rule consists of a match expression and an action.\<close>
datatype 'a rule = Rule (get_match: "'a match_expr") (get_action: action)

lemma rules_singleton_rev_E:
  "[Rule m a] = rs\<^sub>1 @ rs\<^sub>2 \<Longrightarrow>
   (rs\<^sub>1 = [Rule m a] \<Longrightarrow> rs\<^sub>2 = [] \<Longrightarrow> P m a) \<Longrightarrow>
   (rs\<^sub>1 = [] \<Longrightarrow> rs\<^sub>2 = [Rule m a] \<Longrightarrow> P m a) \<Longrightarrow> P m a"
by (cases rs\<^sub>1) auto



section\<open>Basic Algorithms\<close>
text\<open>These algorithms should be valid for all firewall semantics.
     The corresponding proofs follow once the semantics are defined.\<close>


text\<open>The actions Log and Empty do not modify the packet processing in any way. They can be removed.\<close>
fun rm_LogEmpty :: "'a rule list \<Rightarrow> 'a rule list" where
  "rm_LogEmpty [] = []" |
  "rm_LogEmpty ((Rule _ Empty)#rs) = rm_LogEmpty rs" |
  "rm_LogEmpty ((Rule _ Log)#rs) = rm_LogEmpty rs" |
  "rm_LogEmpty (r#rs) = r # rm_LogEmpty rs"

lemma rm_LogEmpty_filter: "rm_LogEmpty rs = filter (\<lambda>r. get_action r \<noteq> Log \<and> get_action r \<noteq> Empty) rs"
 by(induction rs rule: rm_LogEmpty.induct) (simp_all)

lemma rm_LogEmpty_seq: "rm_LogEmpty (rs1@rs2) = rm_LogEmpty rs1 @ rm_LogEmpty rs2"
  by(simp add: rm_LogEmpty_filter)





text\<open>Optimize away MatchAny matches\<close>
fun opt_MatchAny_match_expr_once :: "'a match_expr \<Rightarrow> 'a match_expr" where
  "opt_MatchAny_match_expr_once MatchAny = MatchAny" |
  "opt_MatchAny_match_expr_once (Match a) = (Match a)" |
  "opt_MatchAny_match_expr_once (MatchNot (MatchNot m)) = (opt_MatchAny_match_expr_once m)" |
  "opt_MatchAny_match_expr_once (MatchNot m) = MatchNot (opt_MatchAny_match_expr_once m)" |
  "opt_MatchAny_match_expr_once (MatchAnd MatchAny MatchAny) = MatchAny" |
  "opt_MatchAny_match_expr_once (MatchAnd MatchAny m) = (opt_MatchAny_match_expr_once m)" |
  (*note: remove recursive call to opt_MatchAny_match_expr_once to make it probably faster*)
  "opt_MatchAny_match_expr_once (MatchAnd m MatchAny) = (opt_MatchAny_match_expr_once m)" |
  "opt_MatchAny_match_expr_once (MatchAnd _ (MatchNot MatchAny)) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr_once (MatchAnd (MatchNot MatchAny) _) = (MatchNot MatchAny)" |
  "opt_MatchAny_match_expr_once (MatchAnd m1 m2) = MatchAnd (opt_MatchAny_match_expr_once m1) (opt_MatchAny_match_expr_once m2)"
(* without recursive call: need to apply multiple times until it stabelizes *)


text\<open>It is still a good idea to apply @{const opt_MatchAny_match_expr_once} multiple times. Example:\<close>
lemma "MatchNot (opt_MatchAny_match_expr_once (MatchAnd MatchAny (MatchNot MatchAny))) = MatchNot (MatchNot MatchAny)" by simp
lemma "m = (MatchAnd (MatchAnd MatchAny MatchAny) (MatchAnd MatchAny MatchAny)) \<Longrightarrow> 
  (opt_MatchAny_match_expr_once^^2) m \<noteq> opt_MatchAny_match_expr_once m" by(simp add: funpow_def)

definition opt_MatchAny_match_expr :: "'a match_expr \<Rightarrow> 'a match_expr" where
  "opt_MatchAny_match_expr m \<equiv> repeat_stabilize 2 opt_MatchAny_match_expr_once m"



text\<open>Rewrite @{const Reject} actions to @{const Drop} actions.
      If we just care about the filtering decision (@{const FinalAllow} or @{const FinalDeny}), they should be equal.\<close>
fun rw_Reject :: "'a rule list \<Rightarrow> 'a rule list" where
  "rw_Reject [] = []" |
  "rw_Reject ((Rule m Reject)#rs) = (Rule m Drop)#rw_Reject rs" |
  "rw_Reject (r#rs) = r # rw_Reject rs"



text\<open>We call a ruleset simple iff the only actions are @{const Accept} and @{const Drop}\<close>
  definition simple_ruleset :: "'a rule list \<Rightarrow> bool" where
    "simple_ruleset rs \<equiv> \<forall>r \<in> set rs. get_action r = Accept \<or> get_action r = Drop"

  lemma simple_ruleset_tail: "simple_ruleset (r#rs) \<Longrightarrow> simple_ruleset rs" by (simp add: simple_ruleset_def)

  lemma simple_ruleset_append: "simple_ruleset (rs\<^sub>1 @ rs\<^sub>2) \<longleftrightarrow> simple_ruleset rs\<^sub>1 \<and> simple_ruleset rs\<^sub>2"
    by(simp add: simple_ruleset_def, blast)







text\<open>Structural properties about match expressions\<close>
  fun has_primitive :: "'a match_expr \<Rightarrow> bool" where
    "has_primitive MatchAny = False" |
    "has_primitive (Match a) = True" |
    "has_primitive (MatchNot m) = has_primitive m" |
    "has_primitive (MatchAnd m1 m2) = (has_primitive m1 \<or> has_primitive m2)"

  text\<open>Is a match expression equal to the @{const MatchAny} expression?
        Only applicable if no primitives are in the expression.\<close>
  fun matcheq_matchAny :: "'a match_expr \<Rightarrow> bool" where
    "matcheq_matchAny MatchAny \<longleftrightarrow> True" |
    "matcheq_matchAny (MatchNot m) \<longleftrightarrow> \<not> (matcheq_matchAny m)" |
    "matcheq_matchAny (MatchAnd m1 m2) \<longleftrightarrow> matcheq_matchAny m1 \<and> matcheq_matchAny m2" |
    "matcheq_matchAny (Match _) = undefined"

  fun matcheq_matchNone :: "'a match_expr \<Rightarrow> bool" where
    "matcheq_matchNone MatchAny = False" |
    "matcheq_matchNone (Match _) = False" |
    "matcheq_matchNone (MatchNot MatchAny) = True" |
    "matcheq_matchNone (MatchNot (Match _)) = False" |
    "matcheq_matchNone (MatchNot (MatchNot m)) = matcheq_matchNone m" |
    "matcheq_matchNone (MatchNot (MatchAnd m1 m2)) \<longleftrightarrow> matcheq_matchNone (MatchNot m1) \<and> matcheq_matchNone (MatchNot m2)" |
    "matcheq_matchNone (MatchAnd m1 m2) \<longleftrightarrow>  matcheq_matchNone m1 \<or> matcheq_matchNone m2"
  
  lemma matachAny_matchNone: "\<not> has_primitive m \<Longrightarrow> matcheq_matchAny m \<longleftrightarrow> \<not> matcheq_matchNone m"
    by(induction m rule: matcheq_matchNone.induct)(simp_all)
  
  lemma matcheq_matchNone_no_primitive: "\<not> has_primitive m \<Longrightarrow> matcheq_matchNone (MatchNot m) \<longleftrightarrow> \<not> matcheq_matchNone m"
    by(induction m rule: matcheq_matchNone.induct) (simp_all)






text\<open>optimizing match expressions\<close>

fun optimize_matches_option :: "('a match_expr \<Rightarrow> 'a match_expr option) \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "optimize_matches_option _ [] = []" |
  "optimize_matches_option f (Rule m a#rs) = (case f m of None \<Rightarrow> optimize_matches_option f rs | Some m \<Rightarrow> (Rule m a)#optimize_matches_option f rs)"

lemma optimize_matches_option_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_option f rs)"
  proof(induction rs rule:optimize_matches_option.induct)
  qed(simp_all add: simple_ruleset_def split: option.split)

lemma optimize_matches_option_preserves:
  "(\<And> r m. r \<in> set rs \<Longrightarrow> f (get_match r) = Some m \<Longrightarrow> P m) \<Longrightarrow>
    \<forall> r \<in> set (optimize_matches_option f rs). P (get_match r)"
  apply(induction rs rule: optimize_matches_option.induct)
   apply(simp; fail)
  apply(simp split: option.split)
  by fastforce
(*
lemma optimize_matches_option_preserves':
  "\<forall> m \<in> set rs. P (get_match m) \<Longrightarrow> \<forall>m. P m \<longrightarrow> (\<forall>m'. f m = Some m' \<longrightarrow> P m') \<Longrightarrow> \<forall>m \<in> set (optimize_matches_option f rs). P (get_match m)"
  using optimize_matches_option_preserves[simplified] by metis
*)
lemma optimize_matches_option_append: "optimize_matches_option f (rs1@rs2) = optimize_matches_option f rs1 @ optimize_matches_option f rs2"
  proof(induction rs1 rule: optimize_matches_option.induct)
  qed(simp_all split: option.split)



definition optimize_matches :: "('a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "optimize_matches f rs =  optimize_matches_option (\<lambda>m. (if matcheq_matchNone (f m) then None else Some (f m))) rs"

lemma optimize_matches_append: "optimize_matches f (rs1@rs2) = optimize_matches f rs1 @ optimize_matches f rs2"
  by(simp add: optimize_matches_def optimize_matches_option_append)

(*Warning: simplifier loops with this lemma*)
lemma optimize_matches_fst: "optimize_matches f (r#rs) = optimize_matches f [r]@optimize_matches f rs"
by(cases r)(simp add: optimize_matches_def)

lemma optimize_matches_preserves: "(\<And> r. r \<in> set rs \<Longrightarrow> P (f (get_match r))) \<Longrightarrow>
    \<forall> r \<in> set (optimize_matches f rs). P (get_match r)"
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_preserves)
  by(auto split: split_if_asm)

lemma optimize_matches_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches f rs)"
  by(simp add: optimize_matches_def optimize_matches_option_simple_ruleset)


definition optimize_matches_a :: "(action \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a rule list \<Rightarrow> 'a rule list" where
  "optimize_matches_a f rs = map (\<lambda>r. Rule (f (get_action r) (get_match r)) (get_action r)) rs"

lemma optimize_matches_a_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_a f rs)"
  by(simp add: optimize_matches_a_def simple_ruleset_def)

lemma optimize_matches_a_simple_ruleset_eq:
  "simple_ruleset rs \<Longrightarrow> (\<And> m a. a = Accept \<or> a = Drop \<Longrightarrow> f1 a m = f2 a m) \<Longrightarrow> optimize_matches_a f1 rs = optimize_matches_a f2 rs"
apply(induction rs)
 apply(simp add: optimize_matches_a_def)
apply(simp add: optimize_matches_a_def)
apply(simp add: simple_ruleset_def)
done

lemma optimize_matches_a_preserves: "(\<And> r. r \<in> set rs \<Longrightarrow> P (f (get_action r) (get_match r)))
    \<Longrightarrow> \<forall> r \<in> set (optimize_matches_a f rs). P (get_match r)"
  by(induction rs)(simp_all add: optimize_matches_a_def)



end
