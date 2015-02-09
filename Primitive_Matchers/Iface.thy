theory Iface
imports String "../Output_Format/Negation_Type"
begin

section{*Network Interfaces*}

(*I don't think I can find a good way to support negated interfaces.
  Probably we should stick with simple interfaces for now.
  Reasons why negated interfaces are a problem:
  * Conjunction of Negated and not Negated interface cannot be expressed of one interface
  * Negated interfaces cannot (without additional assumption) be translated to non-negated interfaces.
    Example: Neg ''eth++'', when trying to translate this to a set of non-negated interfaces, 
    it must be possible to have the interface 'eth+' in this set, where the final + is NOT treated as wildcard!*)


(*TODO: refactor, move negation_type interfaces to attic, but keep useful lemmas, add (dead) file to session for future use.
We don't have any ruleset with negated interfaces and I don't see why one would need them*)

(*TODO: add some rule that says an interface starting with ! is invalid (because we want to fail if negation occurs!)*)

datatype iface = Iface "string negation_type"
datatype simple_iface = IfaceSimple "string"  --"no negation supported, but wildcards"

(*TODO: iface to simple_iface*)

definition IfaceAny :: iface where
  "IfaceAny \<equiv> Iface (Pos ''+'')"
definition IfaceFalse :: iface where
  "IfaceFalse \<equiv> Iface (Neg ''+'')"

text_raw{*If the interface name ends in a ``+'', then any interface which begins with this name will match. (man iptables)

Here is how iptables handles this wildcard on my system. A packet for the loopback interface \texttt{lo} is matched by the following expressions
\begin{itemize}
  \item lo
  \item lo+
  \item l+
  \item +
\end{itemize}

It is not matched by the following expressions
\begin{itemize}
  \item lo++
  \item lo+++
  \item lo1+
  \item lo1
\end{itemize}

By the way: \texttt{Warning: weird characters in interface ` ' ('/' and ' ' are not allowed by the kernel).}
*}


  
subsection{*Helpers for the interface name (@{typ string})*}
  (*Do not use outside this thy! Type is really misleading.*)
  text{*
    argument 1: interface as in firewall rule - Wildcard support
    argument 2: interface a packet came from - No wildcard support*}
  fun internal_iface_name_match :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "internal_iface_name_match []     []         \<longleftrightarrow> True" |
    "internal_iface_name_match (i#is) []         \<longleftrightarrow> (i = CHR ''+'' \<and> is = [])" |
    "internal_iface_name_match []     (_#_)      \<longleftrightarrow> False" |
    "internal_iface_name_match (i#is) (p_i#p_is) \<longleftrightarrow> (if (i = CHR ''+'' \<and> is = []) then True else (
          (p_i = i) \<and> internal_iface_name_match is p_is
    ))"
  
  (*<*)
  --"Examples"
    lemma "internal_iface_name_match ''lo'' ''lo''" by eval
    lemma "internal_iface_name_match ''lo+'' ''lo''" by eval
    lemma "internal_iface_name_match ''l+'' ''lo''" by eval
    lemma "internal_iface_name_match ''+'' ''lo''" by eval
    lemma "\<not> internal_iface_name_match ''lo++'' ''lo''" by eval
    lemma "\<not> internal_iface_name_match ''lo+++'' ''lo''" by eval
    lemma "\<not> internal_iface_name_match ''lo1+'' ''lo''" by eval
    lemma "\<not> internal_iface_name_match ''lo1'' ''lo''" by eval
    text{*The wildcard interface name*}
    lemma "internal_iface_name_match ''+'' ''''" by eval (*>*)


  fun iface_name_is_wildcard :: "string \<Rightarrow> bool" where
    "iface_name_is_wildcard [] \<longleftrightarrow> False" |
    "iface_name_is_wildcard [s] \<longleftrightarrow> s = CHR ''+''" |
    "iface_name_is_wildcard (_#ss) \<longleftrightarrow> iface_name_is_wildcard ss"
  lemma iface_name_is_wildcard_alt: "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> last eth = CHR ''+''"
    apply(induction eth rule: iface_name_is_wildcard.induct)
      apply(simp_all)
    done
  lemma iface_name_is_wildcard_alt': "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> hd (rev eth) = CHR ''+''"
    apply(simp add: iface_name_is_wildcard_alt)
    using hd_rev by fastforce
  lemma iface_name_is_wildcard_fst: "iface_name_is_wildcard (i # is) \<Longrightarrow> is \<noteq> [] \<Longrightarrow> iface_name_is_wildcard is"
    by(simp add: iface_name_is_wildcard_alt)


  fun internal_iface_name_to_set :: "string \<Rightarrow> string set" where
    "internal_iface_name_to_set i = (if \<not> iface_name_is_wildcard i
      then
        {i}
      else
        {(butlast i)@cs | cs. True})"
   lemma "{(butlast i)@cs | cs. True} = (\<lambda>s. (butlast i)@s) ` (UNIV::string set)" by fastforce
   lemma internal_iface_name_to_set: "internal_iface_name_match i p_iface \<longleftrightarrow> p_iface \<in> internal_iface_name_to_set i"
    apply(induction i p_iface rule: internal_iface_name_match.induct)
       apply(simp_all)
    apply(safe)
           apply(simp_all add: iface_name_is_wildcard_fst)
     apply (metis (full_types) iface_name_is_wildcard.simps(3) list.exhaust)
    by (metis append_butlast_last_id)

subsection{*Matching*}
  fun match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
    "match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> internal_iface_name_match i p_iface" |
    "match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> \<not> internal_iface_name_match i p_iface"
  
  --"Examples"
    lemma "  match_iface (Iface (Pos ''lo''))    ''lo''"
          "  match_iface (Iface (Pos ''lo+''))   ''lo''"
          "  match_iface (Iface (Pos ''l+''))    ''lo''"
          "  match_iface (Iface (Pos ''+''))     ''lo''"
          "\<not> match_iface (Iface (Pos ''lo++''))  ''lo''"
          "\<not> match_iface (Iface (Pos ''lo+++'')) ''lo''"
          "\<not> match_iface (Iface (Pos ''lo1+''))  ''lo''"
          "\<not> match_iface (Iface (Pos ''lo1''))   ''lo''"
          "  match_iface (Iface (Pos ''+''))     ''eth0''"
          "\<not> match_iface (Iface (Neg ''+''))     ''eth0''"
          "\<not> match_iface (Iface (Neg ''eth+''))  ''eth0''"
          "  match_iface (Iface (Neg ''lo+''))   ''eth0''"
          "\<not> match_iface (Iface (Neg ''lo+''))   ''loX''"
          "\<not> match_iface (Iface (Pos ''''))      ''loX''"
          "  match_iface (Iface (Neg ''''))      ''loX''"
          "\<not> match_iface (Iface (Pos ''foobar+''))     ''foo''" by eval+

  lemma match_IfaceAny: "match_iface IfaceAny i"
    by(cases i, simp_all add: IfaceAny_def)
  lemma match_IfaceFalse: "\<not> match_iface IfaceFalse i"
    by(cases i, simp_all add: IfaceFalse_def)


  --{*@{const match_iface} explained by the individual cases*}
  lemma match_iface_case_pos_nowildcard: "\<not> iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Pos i)) p_i \<longleftrightarrow> i = p_i"
    apply(simp)
    apply(induction i p_i rule: internal_iface_name_match.induct)
       apply(auto simp add: iface_name_is_wildcard_alt split: split_if_asm)
    done
  lemma match_iface_case_neg_nowildcard: "\<not> iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Neg i)) p_i \<longleftrightarrow> i \<noteq> p_i"
    apply(simp)
    apply(induction i p_i rule: internal_iface_name_match.induct)
       apply(auto simp add: iface_name_is_wildcard_alt split: split_if_asm)
    done
  lemma match_iface_case_pos_wildcard_prefix:
    "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Pos i)) p_i \<longleftrightarrow> butlast i = take (length i - 1) p_i"
    apply(simp)
    apply(induction i p_i rule: internal_iface_name_match.induct)
       apply(simp_all)
     apply(simp add: iface_name_is_wildcard_alt split: split_if_asm)
    apply(intro conjI)
     apply(simp add: iface_name_is_wildcard_alt split: split_if_asm)
    apply(intro impI)
    apply(simp add: iface_name_is_wildcard_fst)
    by (metis One_nat_def length_0_conv list.sel(1) list.sel(3) take_Cons')
  lemma match_iface_case_pos_wildcard_length: "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Pos i)) p_i \<Longrightarrow> length p_i \<ge> (length i - 1)"
    apply(simp)
    apply(induction i p_i rule: internal_iface_name_match.induct)
       apply(simp_all)
     apply(simp add: iface_name_is_wildcard_alt split: split_if_asm)
    done
  corollary match_iface_case_pos_wildcard:
    "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Pos i)) p_i \<longleftrightarrow> butlast i = take (length i - 1) p_i \<and> length p_i \<ge> (length i - 1)"
    using match_iface_case_pos_wildcard_length match_iface_case_pos_wildcard_prefix by blast
  lemma match_iface_case_neg_wildcard_prefix: "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface (Neg i)) p_i \<longleftrightarrow> butlast i \<noteq> take (length i - 1) p_i"
    apply(simp)
    apply(induction i p_i rule: internal_iface_name_match.induct)
       apply(simp_all)
     apply(simp add: iface_name_is_wildcard_alt split: split_if_asm)
    apply(intro conjI)
     apply(simp add: iface_name_is_wildcard_alt split: split_if_asm)
    apply(simp add: iface_name_is_wildcard_fst)
    by (metis One_nat_def length_0_conv list.sel(1) list.sel(3) take_Cons')
  (* TODO: match_iface_case_neg_wildcard_length? hmm, p_i can be shorter or longer, essentially different*)


  lemma "match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> p_iface \<in> internal_iface_name_to_set i"
    using internal_iface_name_to_set by simp
  lemma "match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> p_iface \<notin> internal_iface_name_to_set i"
    using internal_iface_name_to_set by simp
  lemma "match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> p_iface \<in> - (internal_iface_name_to_set i)"
    using internal_iface_name_to_set by simp
  --"beware of handling of + as normal non-wildcard character!"
  lemma "match_iface (Iface (Neg ''eth++'')) ''eth''" by eval

  definition internal_iface_name_wildcard_longest :: "string \<Rightarrow> string \<Rightarrow> string option" where
    "internal_iface_name_wildcard_longest i1 i2 = (
      if 
        take (min (length i1 - 1) (length i2 - 1)) i1 = take (min (length i1 - 1) (length i2 - 1)) i2
      then
        Some (if length i1 \<le> length i2 then i2 else i1)
      else
        None)"
  lemma "internal_iface_name_wildcard_longest ''eth+'' ''eth3+'' = Some ''eth3+''" by eval
  lemma "internal_iface_name_wildcard_longest ''eth+'' ''e+'' = Some ''eth+''" by eval
  lemma "internal_iface_name_wildcard_longest ''eth+'' ''lo'' = None" by eval


  lemma internal_iface_name_wildcard_longest_correct: "iface_name_is_wildcard i1 \<Longrightarrow> iface_name_is_wildcard i2 \<Longrightarrow> 
         match_iface (Iface (Pos i1)) p_i \<and> match_iface (Iface (Pos i2)) p_i \<longleftrightarrow>
         (case internal_iface_name_wildcard_longest i1 i2 of None \<Rightarrow> False | Some x \<Rightarrow> match_iface (Iface (Pos x)) p_i)"
    apply(simp split:option.split)
    apply(intro conjI impI allI)
     apply(simp add: internal_iface_name_wildcard_longest_def split: split_if_asm)
     apply(drule match_iface_case_pos_wildcard_prefix[of i1 p_i, simplified butlast_conv_take match_iface.simps])
     apply(drule match_iface_case_pos_wildcard_prefix[of i2 p_i, simplified butlast_conv_take match_iface.simps])
     apply (metis One_nat_def min.commute take_take)
    apply(rename_tac x)
    apply(simp add: internal_iface_name_wildcard_longest_def split: split_if_asm)
     apply(simp add: min_def split: split_if_asm)
     apply(case_tac "internal_iface_name_match x p_i")
      apply(simp_all)
     apply(frule match_iface_case_pos_wildcard_prefix[of i1 p_i])
     apply(frule_tac i=x in match_iface_case_pos_wildcard_prefix[of _ p_i])
     apply(simp add: butlast_conv_take)
     apply (metis min_def take_take)
    apply(case_tac "internal_iface_name_match x p_i")
     apply(simp_all)
    apply(frule match_iface_case_pos_wildcard_prefix[of i2 p_i])
    apply(frule_tac i=x in match_iface_case_pos_wildcard_prefix[of _ p_i])
    apply(simp add: butlast_conv_take min_def split:split_if_asm)
    by (metis min.commute min_def take_take)
    
    
     

  (*Text: probably not necessary to look at negated ifaces here, just translate iface to simple_iface with same behaviour!*)
  text{*
  If the interfaces are no wildcards, they must be equal, otherwise None
  If one is a wildcard, the other one must `match', return the non-wildcard
  If both are wildcards: Longest prefix of both
  *}
  fun most_specific_iface :: "iface \<Rightarrow> iface \<Rightarrow> iface option" where
    "most_specific_iface (Iface (Pos i1)) (Iface (Pos i2)) = (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of
      (True,  True) \<Rightarrow> map_option (\<lambda>i. Iface (Pos i)) (internal_iface_name_wildcard_longest i1 i2) |
      (True,  False) \<Rightarrow> (if match_iface (Iface (Pos i1)) i2 then Some (Iface (Pos i2)) else None) |
      (False, True) \<Rightarrow> (if match_iface (Iface (Pos i2)) i1 then Some (Iface (Pos i1)) else None) |
      (False, False) \<Rightarrow> (if i1 = i2 then Some (Iface (Pos i1)) else None))"
  (*TODO: merging Pos and Neg Iface!! ? ? Requires returning a list?*)
  (* Pos and neg merging: if they don't share the same prefix, Neg can be ignored
     More complicated examples:
     Pos eth+ but Neg eth42
      \<longrightarrow> Pos {eth@X@[''+'']. length X \<le> length ''42'' \<and> X \<noteq> ''42''} \<union> {eth42@[x]@[''+'']}
      oh shit, I hope this never happens in reality, this is really a blowup!
     Pos eth+ but Neg eth42+
      \<longrightarrow> Pos {eth@X@[''+'']. length X \<le> length ''42'' \<and> X \<noteq> ''42''}
  *)
  (*TODO: restrict string to the printable ascii chars, add a placeholder element (not a char but a constructor) which represents one arbitrary char*)


  definition all_chars :: "char list" where
    "all_chars \<equiv> Enum.enum"
  lemma [simp]: "set all_chars = (UNIV::char set)"
     by(simp add: all_chars_def enum_UNIV)

  value "(map (\<lambda>c. c#''!'') all_chars):: string list"
  
  (*value "List.n_lists 2 all_chars" daam, this takes forever!*)
  thm List.n_lists.simps
  (*fun all_strings_except :: "string \<Rightarrow> string list" where
    "all_strings_except [] = [[]]" |
    "all_strings_except (s#ss) = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) (remove1 s all_chars)) (all_strings_except ss))"
   value "all_strings_except ''et''"*)

  (*we can compute this, but its horribly inefficient! TODO: reduce size of valid chars to the printable ones*)
  lemma strings_of_length_n: "set (List.n_lists n all_chars) = {s::string. length s = n}"
    apply(induction n)
     apply(simp)
    apply(simp)
    apply(safe)
     apply(simp)
    apply(simp)
    apply(rename_tac n x)
    apply(rule_tac x="drop 1 x" in exI)
    apply(simp)
    apply(case_tac x)
     apply(simp_all)
    done
  definition non_wildcard_ifaces :: "nat \<Rightarrow> string list" where
   "non_wildcard_ifaces n \<equiv> filter (\<lambda>i. \<not> iface_name_is_wildcard i) (List.n_lists n all_chars)"
  export_code non_wildcard_ifaces in SML (*Can be exported, ... but I wouldn't run it!*)
  lemma non_wildcard_ifaces: "set (non_wildcard_ifaces n) = {s::string. length s = n \<and> \<not> iface_name_is_wildcard s}"
    using strings_of_length_n non_wildcard_ifaces_def by auto

  lemma  "(\<Union> i \<in> set (non_wildcard_ifaces n). internal_iface_name_to_set i) = {s::string. length s = n \<and> \<not> iface_name_is_wildcard s}"
   apply(simp_all only: internal_iface_name_to_set.simps if_True if_False not_True_eq_False not_False_eq_True non_wildcard_ifaces)
   apply(simp_all split: split_if_asm split_if)
   done

  fun non_wildcard_ifaces_upto :: "nat \<Rightarrow> string list" where
    "non_wildcard_ifaces_upto 0 = [[]]" |
    "non_wildcard_ifaces_upto (Suc n) = (non_wildcard_ifaces (Suc n)) @ non_wildcard_ifaces_upto n"
  lemma non_wildcard_ifaces_upto: "set (non_wildcard_ifaces_upto n) = {s::string. length s \<le> n \<and> \<not> iface_name_is_wildcard s}"
    apply(induction n)
     apply(simp)
     apply fastforce
    apply(simp add: non_wildcard_ifaces)
    by fastforce

  lemma inv_i_wildcard: "- {i@cs | cs. True} = {c | c. length c < length i} \<union> {c@cs | c cs. length c = length i \<and> c \<noteq> i}"
    apply(rule)
     prefer 2
     apply(safe)[1]
      apply(simp add:)
     apply(simp add:)
    apply(simp)
    apply(rule Compl_anti_mono[where B="{i @ cs |cs. True}" and A="- ({c | c. length c < length i} \<union> {c@cs | c cs. length c = length i \<and> c \<noteq> i})", simplified])
    apply(safe)
    apply(simp)
    apply(case_tac "(length i) = length x")
     apply(erule_tac x=x in allE, simp)
     apply(blast)
    apply(erule_tac x="take (length i) x" in allE)
    apply(simp add: min_def)
    by (metis append_take_drop_id)
  lemma inv_i_nowildcard: "- {i::string} = {c | c. length c < length i} \<union> {c@cs | c cs. length c \<ge> length i \<and> c \<noteq> i}"
  proof -
    have x: "{c | c. length c = length i \<and> c \<noteq> i}  \<union> {c | c. length c > length i} = {c@cs | c cs. length c \<ge> length i \<and> c \<noteq> i}"
    apply(safe)
    apply force+
    done
    have "- {i::string} = {c |c . c \<noteq> i}"
     by(safe, simp)
    also have "\<dots> = {c | c. length c < length i} \<union> {c | c. length c = length i \<and> c \<noteq> i}  \<union> {c | c. length c > length i}"
    by(auto)
    finally show ?thesis using x by auto
  qed

   
  lemma inv_iface_name_set: "- (internal_iface_name_to_set i) = (
    if iface_name_is_wildcard i
    then
      {c |c. length c < length (butlast i)} \<union> {c @ cs |c cs. length c = length (butlast i) \<and> c \<noteq> butlast i}
      (*{s@cs | s cs. length s \<le> length i - 1 \<and> s \<noteq> take (length s) i}*) (*no ''+'' at end (as one would write donw the iface) but allow arbitrary string*)
    else
      {c | c. length c < length i} \<union> {c@cs | c cs. length c \<ge> length i \<and> c \<noteq> i}
      (*\<dots> \<union> X = \<dots> \<union> {c | c. length c = length i \<and> c \<noteq> i}  \<union> {c | c. length c > length i} and is essentially {c@''+'' | len c = len i \<and> c \<noteq> i}
        TODO: this should help when writing as an interface string*)
  )"
  apply(case_tac "iface_name_is_wildcard i")
   apply(simp_all only: internal_iface_name_to_set.simps if_True if_False not_True_eq_False not_False_eq_True)
   apply(subst inv_i_wildcard)
   apply(simp)
  apply(subst inv_i_nowildcard)
  apply(simp)
  done


  (*TODO: need to write it as interface strings!*)
  lemma  "- (internal_iface_name_to_set i) = (
    if iface_name_is_wildcard i
    then
      (\<Union> s \<in> set (non_wildcard_ifaces_upto (length i - 1)). internal_iface_name_to_set s) \<union> 
      (\<Union> s \<in> {c @ cs |c cs. length c = length (butlast i) \<and> c \<noteq> butlast i}. internal_iface_name_to_set s)
    else
      {} (*TODO*)
  )"
  apply(subst inv_iface_name_set)
  apply(case_tac "iface_name_is_wildcard i")
   apply(simp_all only: internal_iface_name_to_set.simps if_True if_False not_True_eq_False not_False_eq_True)
   apply(simp)
  oops

  (*TODO: function rewrite Neg Iface to Pos Iface*)
  fun neg_iface_name_to_pos_iface_name :: "string \<Rightarrow> string list" where
    "neg_iface_name_to_pos_iface_name i = (if iface_name_is_wildcard i
      then
        (non_wildcard_ifaces_upto (length i - 1)) @ map (\<lambda>s. s@''+'') (filter (\<lambda>s. s \<noteq> butlast i) (non_wildcard_ifaces (length i - 1)))
      else
        [] (*TODO*)
    )"
  lemma "- (internal_iface_name_to_set i) = (\<Union> s \<in> set (neg_iface_name_to_pos_iface_name i). internal_iface_name_to_set s)"
    apply(subst inv_iface_name)
    apply(subst neg_iface_name_to_pos_iface_name.simps)
    apply(case_tac "iface_name_is_wildcard i")
     apply(simp_all only: internal_iface_name_to_set.simps if_True if_False not_True_eq_False not_False_eq_True)
     apply(simp add: non_wildcard_ifaces_upto non_wildcard_ifaces)
     apply(simp add: iface_name_is_wildcard_alt)
     apply(safe)
     apply(auto)[1]
     
  oops


  fun iface_to_simple_iface :: "iface \<Rightarrow> simple_iface list" where
    "iface_to_simple_iface (Iface (Pos i)) = [IfaceSimple i]" |
    "iface_to_simple_iface (Iface (Neg i)) = map IfaceSimple (neg_iface_name_to_pos_iface_name i)"

  hide_const (open) internal_iface_name_wildcard_longest

hide_const (open) internal_iface_name_match

end
