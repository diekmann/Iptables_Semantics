section\<open>Network Interfaces\<close>
theory Iface
imports String
        "~~/src/HOL/Library/Char_ord" (*WARNING: importing char ord*)
begin

text\<open>Network interfaces, e.g. \texttt{eth0}, \texttt{wlan1}, ...

iptables supports wildcard matching, e.g. \texttt{eth+} will match \texttt{eth}, \texttt{eth1}, \texttt{ethFOO}, ...
The character `+' is only a wildcard if it appears at the end.
\<close>

datatype iface = Iface (iface_sel: "string")  --"no negation supported, but wildcards"


text\<open>Just a normal lexicographical ordering on the interface strings. Used only for optimizing code.
     WARNING: not a semantic ordering.\<close>
(*We cannot use List_lexord because it clashed with the Word_Lib imported ordering!*)
instantiation iface :: linorder
begin
  function (sequential) less_eq_iface :: "iface \<Rightarrow> iface \<Rightarrow> bool" where
    "(Iface []) \<le> (Iface _) \<longleftrightarrow> True" |
    "(Iface _) \<le> (Iface []) \<longleftrightarrow> False" |
    "(Iface (a#as)) \<le> (Iface (b#bs)) \<longleftrightarrow> (if a = b then Iface as \<le> Iface bs else a \<le> b)"
   by(pat_completeness) auto
  termination "less_eq :: iface \<Rightarrow> _ \<Rightarrow> bool"
    apply(relation "measure (\<lambda>is. size (iface_sel (fst is)) + size (iface_sel (snd is)))")
    apply(rule wf_measure, unfold in_measure comp_def)
    apply(simp)
    done
  
  lemma Iface_less_eq_empty: "Iface x \<le> Iface [] \<Longrightarrow> x = []"
    by(induction "Iface x" "Iface []" rule: less_eq_iface.induct) auto
  lemma less_eq_empty: "Iface [] \<le> q"
    by(induction "Iface []" q rule: less_eq_iface.induct) auto
  lemma iface_cons_less_eq_i:
    "Iface (b # bs) \<le> i \<Longrightarrow> \<exists> q qs. i=Iface (q#qs) \<and> (b < q \<or> (Iface bs) \<le> (Iface qs))"
    apply(induction "Iface (b # bs)" i rule: less_eq_iface.induct)
     apply(simp_all split: split_if_asm)
    apply(clarify)
    apply(simp)
    done

  function (sequential) less_iface :: "iface \<Rightarrow> iface \<Rightarrow> bool" where
    "(Iface []) < (Iface []) \<longleftrightarrow> False" |
    "(Iface []) < (Iface _) \<longleftrightarrow> True" |
    "(Iface _) < (Iface []) \<longleftrightarrow> False" |
    "(Iface (a#as)) < (Iface (b#bs)) \<longleftrightarrow> (if a = b then Iface as < Iface bs else a < b)"
   by(pat_completeness) auto
  termination "less :: iface \<Rightarrow> _ \<Rightarrow> bool"
    apply(relation "measure (\<lambda>is. size (iface_sel (fst is)) + size (iface_sel (snd is)))")
    apply(rule wf_measure, unfold in_measure comp_def)
    apply(simp)
    done
instance
  proof
    fix n m :: iface
    show "n < m \<longleftrightarrow> n \<le> m \<and> \<not> m \<le> n"
      proof(induction rule: less_iface.induct)
      case 4 thus ?case by simp fastforce
      qed(simp+)
  next
    fix n :: iface have "n = m \<Longrightarrow> n \<le> m" for m
      by(induction n m rule: less_eq_iface.induct) simp+
    thus "n \<le> n" by simp
  next
    fix n m :: iface
    show "n \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> n = m"
      proof(induction n m rule: less_eq_iface.induct)
      case 1 thus ?case using Iface_less_eq_empty by blast
      next
      case 3 thus ?case by (simp split: split_if_asm)
      qed(simp)+
  next
    fix n m q :: iface show "n \<le> m \<Longrightarrow> m \<le> q \<Longrightarrow> n \<le> q" 
      proof(induction n q arbitrary: m rule: less_eq_iface.induct)
      case 1 thus ?case by simp
      next
      case 2 thus ?case
        apply simp
        apply(drule iface_cons_less_eq_i)
        apply(elim exE conjE disjE)
         apply(simp; fail)
        by fastforce
      next
      case 3 thus ?case
        apply simp
        apply(frule iface_cons_less_eq_i)
         by(auto split: split_if_asm)
      qed
  next
    fix n m :: iface show "n \<le> m \<or> m \<le> n"
      apply(induction n m rule: less_eq_iface.induct)
        apply(simp_all)
      by fastforce
  qed
end

definition ifaceAny :: iface where
  "ifaceAny \<equiv> Iface ''+''"
(* there is no IfaceFalse, proof below *)

text\<open>If the interface name ends in a ``+'', then any interface which begins with this name will match.
  (man iptables)

Here is how iptables handles this wildcard on my system.
A packet for the loopback interface \texttt{lo} is matched by the following expressions
  \<^item> lo
  \<^item> lo+
  \<^item> l+
  \<^item> +

It is not matched by the following expressions
  \<^item> lo++
  \<^item> lo+++
  \<^item> lo1+
  \<^item> lo1

By the way: \texttt{Warning: weird characters in interface ` ' ('/' and ' ' are not allowed by the kernel).}
However, happy snowman and shell colors are fine.
\<close>


context
begin
  subsection\<open>Helpers for the interface name (@{typ string})\<close>
    (*Do not use outside this thy! Type is really misleading.*)
    text\<open>
      argument 1: interface as in firewall rule - Wildcard support
      argument 2: interface a packet came from - No wildcard support\<close>
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
      text\<open>The wildcard interface name\<close>
      lemma "internal_iface_name_match ''+'' ''''" by eval (*>*)
  
  
    fun iface_name_is_wildcard :: "string \<Rightarrow> bool" where
      "iface_name_is_wildcard [] \<longleftrightarrow> False" |
      "iface_name_is_wildcard [s] \<longleftrightarrow> s = CHR ''+''" |
      "iface_name_is_wildcard (_#ss) \<longleftrightarrow> iface_name_is_wildcard ss"
    private lemma iface_name_is_wildcard_alt: "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> last eth = CHR ''+''"
      proof(induction eth rule: iface_name_is_wildcard.induct)
      qed(simp_all)
    private lemma iface_name_is_wildcard_alt': "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> hd (rev eth) = CHR ''+''"
      unfolding iface_name_is_wildcard_alt using hd_rev by fastforce
    private lemma iface_name_is_wildcard_fst: "iface_name_is_wildcard (i # is) \<Longrightarrow> is \<noteq> [] \<Longrightarrow> iface_name_is_wildcard is"
      by(simp add: iface_name_is_wildcard_alt)
  
    private fun internal_iface_name_to_set :: "string \<Rightarrow> string set" where
      "internal_iface_name_to_set i = (if \<not> iface_name_is_wildcard i
        then
          {i}
        else
          {(butlast i)@cs | cs. True})"
    private lemma "{(butlast i)@cs | cs. True} = (\<lambda>s. (butlast i)@s) ` (UNIV::string set)" by fastforce
    private lemma internal_iface_name_to_set: "internal_iface_name_match i p_iface \<longleftrightarrow> p_iface \<in> internal_iface_name_to_set i"
      proof(induction i p_iface rule: internal_iface_name_match.induct)
      case 4 thus ?case
        apply(simp)
        apply(safe)
               apply(simp_all add: iface_name_is_wildcard_fst)
         apply (metis (full_types) iface_name_is_wildcard.simps(3) list.exhaust)
        by (metis append_butlast_last_id)
      qed(simp_all)
    private lemma internal_iface_name_to_set2: "internal_iface_name_to_set ifce = {i. internal_iface_name_match ifce i}"
      by (simp add: internal_iface_name_to_set)
      
  
    private lemma internal_iface_name_match_refl: "internal_iface_name_match i i"
     proof -
     { fix i j
       have "i=j \<Longrightarrow> internal_iface_name_match i j"
         by(induction i j rule: internal_iface_name_match.induct)(simp_all)
     } thus ?thesis by simp
     qed
  
  subsection\<open>Matching\<close>
    fun match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
      "match_iface (Iface i) p_iface \<longleftrightarrow> internal_iface_name_match i p_iface"
    
    --"Examples"
      lemma "  match_iface (Iface ''lo'')    ''lo''"
            "  match_iface (Iface ''lo+'')   ''lo''"
            "  match_iface (Iface ''l+'')    ''lo''"
            "  match_iface (Iface ''+'')     ''lo''"
            "\<not> match_iface (Iface ''lo++'')  ''lo''"
            "\<not> match_iface (Iface ''lo+++'') ''lo''"
            "\<not> match_iface (Iface ''lo1+'')  ''lo''"
            "\<not> match_iface (Iface ''lo1'')   ''lo''"
            "  match_iface (Iface ''+'')     ''eth0''"
            "  match_iface (Iface ''+'')     ''eth0''"
            "  match_iface (Iface ''eth+'')  ''eth0''"
            "\<not> match_iface (Iface ''lo+'')   ''eth0''"
            "  match_iface (Iface ''lo+'')   ''loX''"
            "\<not> match_iface (Iface '''')      ''loX''"
            (*<*)by eval+(*>*)
  
    lemma match_ifaceAny: "match_iface ifaceAny i"
      by(cases i, simp_all add: ifaceAny_def)
    lemma match_IfaceFalse: "\<not>(\<exists> IfaceFalse. (\<forall>i. \<not> match_iface IfaceFalse i))"
      apply(simp)
      apply(intro allI, rename_tac IfaceFalse)
      apply(case_tac IfaceFalse, rename_tac name)
      apply(rule_tac x="name" in exI)
      by(simp add: internal_iface_name_match_refl)
      

    --\<open>@{const match_iface} explained by the individual cases\<close>
    lemma match_iface_case_nowildcard: "\<not> iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface i) p_i \<longleftrightarrow> i = p_i"
      proof(induction i p_i rule: internal_iface_name_match.induct)
      qed(auto simp add: iface_name_is_wildcard_alt split: split_if_asm)
    lemma match_iface_case_wildcard_prefix:
      "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface i) p_i \<longleftrightarrow> butlast i = take (length i - 1) p_i"
      apply(induction i p_i rule: internal_iface_name_match.induct)
         apply(simp; fail)
        apply(simp add: iface_name_is_wildcard_alt split: split_if_asm; fail)
       apply(simp; fail)
      apply(simp)
      apply(intro conjI)
       apply(simp add: iface_name_is_wildcard_alt split: split_if_asm; fail)
      apply(simp add: iface_name_is_wildcard_fst)
      by (metis One_nat_def length_0_conv list.sel(1) list.sel(3) take_Cons')
    lemma match_iface_case_wildcard_length: "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface i) p_i \<Longrightarrow> length p_i \<ge> (length i - 1)"
      proof(induction i p_i rule: internal_iface_name_match.induct)
      qed(simp_all add: iface_name_is_wildcard_alt split: split_if_asm)
    corollary match_iface_case_wildcard:
      "iface_name_is_wildcard i \<Longrightarrow> match_iface (Iface i) p_i \<longleftrightarrow> butlast i = take (length i - 1) p_i \<and> length p_i \<ge> (length i - 1)"
      using match_iface_case_wildcard_length match_iface_case_wildcard_prefix by blast
  
  
    lemma match_iface_set: "match_iface (Iface i) p_iface \<longleftrightarrow> p_iface \<in> internal_iface_name_to_set i"
      using internal_iface_name_to_set by simp
  
    private definition internal_iface_name_wildcard_longest :: "string \<Rightarrow> string \<Rightarrow> string option" where
      "internal_iface_name_wildcard_longest i1 i2 = (
        if 
          take (min (length i1 - 1) (length i2 - 1)) i1 = take (min (length i1 - 1) (length i2 - 1)) i2
        then
          Some (if length i1 \<le> length i2 then i2 else i1)
        else
          None)"
    private lemma "internal_iface_name_wildcard_longest ''eth+'' ''eth3+'' = Some ''eth3+''" by eval
    private lemma "internal_iface_name_wildcard_longest ''eth+'' ''e+'' = Some ''eth+''" by eval
    private lemma "internal_iface_name_wildcard_longest ''eth+'' ''lo'' = None" by eval
  
    private  lemma internal_iface_name_wildcard_longest_commute: "iface_name_is_wildcard i1 \<Longrightarrow> iface_name_is_wildcard i2 \<Longrightarrow> 
      internal_iface_name_wildcard_longest i1 i2 = internal_iface_name_wildcard_longest i2 i1"
      apply(simp add: internal_iface_name_wildcard_longest_def)
      apply(safe)
        apply(simp_all add: iface_name_is_wildcard_alt)
        apply (metis One_nat_def append_butlast_last_id butlast_conv_take)
       by (metis min.commute)+
    private  lemma internal_iface_name_wildcard_longest_refl: "internal_iface_name_wildcard_longest i i = Some i"
      by(simp add: internal_iface_name_wildcard_longest_def)
  
  
    private lemma internal_iface_name_wildcard_longest_correct:
      "iface_name_is_wildcard i1 \<Longrightarrow> iface_name_is_wildcard i2 \<Longrightarrow> 
       match_iface (Iface i1) p_i \<and> match_iface (Iface i2) p_i \<longleftrightarrow>
       (case internal_iface_name_wildcard_longest i1 i2 of None \<Rightarrow> False | Some x \<Rightarrow> match_iface (Iface x) p_i)"
    proof -
      assume assm1: "iface_name_is_wildcard i1"
         and assm2: "iface_name_is_wildcard i2"
      { assume assm3: "internal_iface_name_wildcard_longest i1 i2 = None" 
        have "\<not> (internal_iface_name_match i1 p_i \<and> internal_iface_name_match i2 p_i)"
        proof -
          from match_iface_case_wildcard_prefix[OF assm1] have 1:
            "internal_iface_name_match i1 p_i = (take (length i1 - 1) i1 = take (length i1 - 1) p_i)" by(simp add: butlast_conv_take)
          from match_iface_case_wildcard_prefix[OF assm2] have 2:
            "internal_iface_name_match i2 p_i = (take (length i2 - 1) i2 = take (length i2 - 1) p_i)" by(simp add: butlast_conv_take)
          from assm3 have 3: "take (min (length i1 - 1) (length i2 - 1)) i1 \<noteq> take (min (length i1 - 1) (length i2 - 1)) i2"
           by(simp add: internal_iface_name_wildcard_longest_def split: split_if_asm)
          from 3 show ?thesis using 1 2 min.commute take_take by metis
        qed
      } note internal_iface_name_wildcard_longest_correct_None=this
    
      { fix X
        assume assm3: "internal_iface_name_wildcard_longest i1 i2 = Some X"
        have "(internal_iface_name_match i1 p_i \<and> internal_iface_name_match i2 p_i) \<longleftrightarrow> internal_iface_name_match X p_i"
        proof -
          from assm3 have assm3': "take (min (length i1 - 1) (length i2 - 1)) i1 = take (min (length i1 - 1) (length i2 - 1)) i2"
            unfolding internal_iface_name_wildcard_longest_def by(simp split: split_if_asm)
      
          { fix i1 i2
            assume iw1: "iface_name_is_wildcard i1" and iw2: "iface_name_is_wildcard i2" and len: "length i1 \<le> length i2" and
                   take_i1i2: "take (length i1 - 1) i1 = take (length i1 - 1) i2"
            from len have len': "length i1 - 1 \<le> length i2 - 1" by fastforce
            { fix x::string
             from len' have "take (length i1 - 1) x = take (length i1 - 1) (take (length i2 - 1) x)" by(simp add: min_def)
            } note takei1=this
        
            { fix m::nat and n::nat and a::string and b c
              have "m \<le> n \<Longrightarrow> take n a = take n b \<Longrightarrow> take m a = take m c \<Longrightarrow> take m c = take m b" by (metis min_absorb1 take_take)
            } note takesmaller=this
        
            from match_iface_case_wildcard_prefix[OF iw1, simplified] have 1:
                "internal_iface_name_match i1 p_i \<longleftrightarrow> take (length i1 - 1) i1 = take (length i1 - 1) p_i" by(simp add: butlast_conv_take)
            also have "\<dots> \<longleftrightarrow> take (length i1 - 1) (take (length i2 - 1) i1) = take (length i1 - 1) (take (length i2 - 1) p_i)" using takei1 by simp
            finally have  "internal_iface_name_match i1 p_i = (take (length i1 - 1) (take (length i2 - 1) i1) = take (length i1 - 1) (take (length i2 - 1) p_i))" .
            from match_iface_case_wildcard_prefix[OF iw2, simplified] have 2:
                "internal_iface_name_match i2 p_i \<longleftrightarrow> take (length i2 - 1) i2 = take (length i2 - 1) p_i" by(simp add: butlast_conv_take)
        
            have "internal_iface_name_match i2 p_i \<Longrightarrow> internal_iface_name_match i1 p_i"
              unfolding 1 2 
              apply(rule takesmaller[of "(length i1 - 1)" "(length i2 - 1)" i2 p_i])
                using len' apply (simp; fail)
               apply (simp; fail)
              using take_i1i2 by simp
          } note longer_iface_imp_shorter=this
        
         show ?thesis
          proof(cases "length i1 \<le> length i2")
          case True
            with assm3 have "X = i2" unfolding internal_iface_name_wildcard_longest_def by(simp split: split_if_asm)
            from True assm3' have take_i1i2: "take (length i1 - 1) i1 = take (length i1 - 1) i2" by linarith
            from longer_iface_imp_shorter[OF assm1 assm2 True take_i1i2] \<open>X = i2\<close>
            show "(internal_iface_name_match i1 p_i \<and> internal_iface_name_match i2 p_i) \<longleftrightarrow> internal_iface_name_match X p_i" by fastforce
          next
          case False
            with assm3 have "X = i1" unfolding internal_iface_name_wildcard_longest_def by(simp split: split_if_asm)
            from False assm3' have take_i1i2: "take (length i2 - 1) i2 = take (length i2 - 1) i1" by (metis min_def min_diff)
            from longer_iface_imp_shorter[OF assm2 assm1 _ take_i1i2] False \<open>X = i1\<close>
            show "(internal_iface_name_match i1 p_i \<and> internal_iface_name_match i2 p_i) \<longleftrightarrow> internal_iface_name_match X p_i" by auto
          qed
        qed
      } note internal_iface_name_wildcard_longest_correct_Some=this
    
      from internal_iface_name_wildcard_longest_correct_None internal_iface_name_wildcard_longest_correct_Some show ?thesis
        by(simp split:option.split)
    qed
  
    fun iface_conjunct :: "iface \<Rightarrow> iface \<Rightarrow> iface option" where
      "iface_conjunct (Iface i1) (Iface i2) = (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of
        (True,  True) \<Rightarrow> map_option Iface  (internal_iface_name_wildcard_longest i1 i2) |
        (True,  False) \<Rightarrow> (if match_iface (Iface i1) i2 then Some (Iface i2) else None) |
        (False, True) \<Rightarrow> (if match_iface (Iface i2) i1 then Some (Iface i1) else None) |
        (False, False) \<Rightarrow> (if i1 = i2 then Some (Iface i1) else None))"

    
    lemma iface_conjunct_Some: "iface_conjunct i1 i2 = Some x \<Longrightarrow> 
          match_iface x p_i \<longleftrightarrow> match_iface i1 p_i \<and> match_iface i2 p_i"
      apply(cases i1, cases i2, rename_tac i1name i2name)
      apply(simp)
      apply(case_tac "iface_name_is_wildcard i1name")
       apply(case_tac [!] "iface_name_is_wildcard i2name")
         apply(simp_all)
         using internal_iface_name_wildcard_longest_correct apply auto[1]
        apply (metis match_iface.simps match_iface_case_nowildcard option.distinct(1) option.sel)
       apply (metis match_iface.simps match_iface_case_nowildcard option.distinct(1) option.sel)
      by (metis match_iface.simps option.distinct(1) option.inject)
    lemma iface_conjunct_None: "iface_conjunct i1 i2 = None \<Longrightarrow> \<not> (match_iface i1 p_i \<and> match_iface i2 p_i)"
      apply(cases i1, cases i2, rename_tac i1name i2name)
      apply(simp split: bool.split_asm split_if_asm)
         using internal_iface_name_wildcard_longest_correct apply fastforce
        apply (metis match_iface.simps match_iface_case_nowildcard)+
      done
    lemma iface_conjunct: "match_iface i1 p_i \<and> match_iface i2 p_i \<longleftrightarrow>
           (case iface_conjunct i1 i2 of None \<Rightarrow> False | Some x \<Rightarrow> match_iface x p_i)"
    apply(simp split: option.split)
    by(blast dest: iface_conjunct_Some iface_conjunct_None)

    lemma match_iface_refl: "match_iface (Iface x) x" by (simp add: internal_iface_name_match_refl)
    lemma match_iface_eqI: assumes "x = Iface y" shows "match_iface x y"
      unfolding assms using match_iface_refl .


    lemma iface_conjunct_ifaceAny: "iface_conjunct ifaceAny i = Some i"
      apply(simp add: ifaceAny_def)
      apply(case_tac i, rename_tac iname)
      apply(simp)
      apply(case_tac "iface_name_is_wildcard iname")
       apply(simp add: internal_iface_name_wildcard_longest_def iface_name_is_wildcard_alt Suc_leI; fail)
      apply(simp)
      using internal_iface_name_match.elims(3) by fastforce
       
    lemma iface_conjunct_commute: "iface_conjunct i1 i2 = iface_conjunct i2 i1"
    apply(induction i1 i2 rule: iface_conjunct.induct)
    apply(rename_tac i1 i2, simp)
    apply(case_tac "iface_name_is_wildcard i1")
     apply(case_tac [!] "iface_name_is_wildcard i2")
       apply(simp_all)
    by (simp add: internal_iface_name_wildcard_longest_commute)


    private definition internal_iface_name_subset :: "string \<Rightarrow> string \<Rightarrow> bool" where
      "internal_iface_name_subset i1 i2 = (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of
        (True,  True) \<Rightarrow> length i1 \<ge> length i2 \<and> take ((length i2) - 1) i1 = butlast i2 |
        (True,  False) \<Rightarrow> False |
        (False, True) \<Rightarrow> take (length i2 - 1) i1 = butlast i2 |
        (False, False) \<Rightarrow> i1 = i2
        )"

    private lemma butlast_take_length_helper:
      fixes x ::"char list"
      assumes a1: "length i2 \<le> length i1"
      assumes a2: "take (length i2 - Suc 0) i1 = butlast i2"
      assumes a3: "butlast i1 = take (length i1 - Suc 0) x"
      shows "butlast i2 = take (length i2 - Suc 0) x"
    proof - (*sledgehammer spass Isar proof*)
      have f4: "List.gen_length 0 i2 \<le> List.gen_length 0 i1"
        using a1 by (simp add: length_code)
      have f5: "\<And>cs. List.gen_length 0 (cs::char list) - Suc 0 = List.gen_length 0 (tl cs)"
        by (metis (no_types) One_nat_def length_code length_tl)
      obtain nn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" where
        "\<And>f. \<not> f (nn f) \<le> f (Suc (nn f)) \<or> f (List.gen_length 0 i2) \<le> f (List.gen_length 0 i1)"
        using f4 by (meson lift_Suc_mono_le)
      hence "\<not> nn (\<lambda>n. n - Suc 0) - Suc 0 \<le> nn (\<lambda>n. n - Suc 0) \<or> List.gen_length 0 (tl i2) \<le> List.gen_length 0 (tl i1)"
        using f5 by (metis (lifting) diff_Suc_Suc diff_zero)
      hence f6: "min (List.gen_length 0 (tl i2)) (List.gen_length 0 (tl i1)) = List.gen_length 0 (tl i2)"
        using diff_le_self min.absorb1 by blast
      { assume "take (List.gen_length 0 (tl i2)) i1 \<noteq> take (List.gen_length 0 (tl i2)) x"
        have "List.gen_length 0 (tl i2) = 0 \<or> take (List.gen_length 0 (tl i2)) i1 = take (List.gen_length 0 (tl i2)) x"
          using f6 f5 a3 by (metis (lifting) One_nat_def butlast_conv_take length_code take_take)
        hence "take (List.gen_length 0 (tl i2)) i1 = take (List.gen_length 0 (tl i2)) x"
          by force }
      thus "butlast i2 = take (length i2 - Suc 0) x"
        using f5 a2 by (metis (full_types) length_code)
    qed

    private lemma internal_iface_name_subset: "internal_iface_name_subset i1 i2 \<longleftrightarrow> 
        {i. internal_iface_name_match i1 i} \<subseteq> {i. internal_iface_name_match i2 i}"
      unfolding internal_iface_name_subset_def
      proof(cases "iface_name_is_wildcard i1", case_tac [!] "iface_name_is_wildcard i2", simp_all)
        assume a1: "iface_name_is_wildcard i1"
        assume a2: "iface_name_is_wildcard i2"
        show "(length i2 \<le> length i1 \<and> take (length i2 - Suc 0) i1 = butlast i2) \<longleftrightarrow>
            ({i. internal_iface_name_match i1 i} \<subseteq> {i. internal_iface_name_match i2 i})" (is "?l \<longleftrightarrow> ?r")
          proof(rule iffI)
            assume ?l with a1 a2 show ?r
             apply(clarify, rename_tac x)
             apply(drule_tac p_i=x in match_iface_case_wildcard_prefix)+
             apply(simp)
             using butlast_take_length_helper by blast
          next
            assume ?r hence r': "internal_iface_name_to_set i1 \<subseteq> internal_iface_name_to_set i2 "
              apply -
              apply(subst(asm) internal_iface_name_to_set2[symmetric])+
              by assumption
            have hlp1: "\<And>i1 i2. {x. \<exists>cs. x = i1 @ cs} \<subseteq> {x. \<exists>cs. x = i2 @ cs} \<Longrightarrow> length i2 \<le> length i1"
              apply(simp add: Set.Collect_mono_iff)
              by force
            have hlp2: "\<And>i1 i2. {x. \<exists>cs. x = i1 @ cs} \<subseteq> {x. \<exists>cs. x = i2 @ cs} \<Longrightarrow> take (length i2) i1 = i2"
              apply(simp add: Set.Collect_mono_iff)
              by force
            from r' a1 a2 show ?l
              apply(simp add: internal_iface_name_to_set)
              apply(safe)
               apply(drule hlp1)
               apply(simp)
               apply (metis One_nat_def Suc_pred diff_Suc_eq_diff_pred diff_is_0_eq iface_name_is_wildcard.simps(1) length_greater_0_conv)
              apply(drule hlp2)
              apply(simp)
              by (metis One_nat_def butlast_conv_take length_butlast length_take take_take)
          qed
      next
      show "iface_name_is_wildcard i1 \<Longrightarrow> \<not> iface_name_is_wildcard i2 \<Longrightarrow>
            \<not> Collect (internal_iface_name_match i1) \<subseteq> Collect (internal_iface_name_match i2)"
        using internal_iface_name_match_refl match_iface_case_nowildcard by fastforce
      next
      show "\<not> iface_name_is_wildcard i1 \<Longrightarrow> iface_name_is_wildcard i2 \<Longrightarrow>
            (take (length i2 - Suc 0) i1 = butlast i2) \<longleftrightarrow> ({i. internal_iface_name_match i1 i} \<subseteq> {i. internal_iface_name_match i2 i})"
        using match_iface_case_nowildcard match_iface_case_wildcard_prefix by force
      next
      show " \<not> iface_name_is_wildcard i1 \<Longrightarrow> \<not> iface_name_is_wildcard i2 \<Longrightarrow>
           (i1 = i2) \<longleftrightarrow> ({i. internal_iface_name_match i1 i} \<subseteq> {i. internal_iface_name_match i2 i})"
        using match_iface_case_nowildcard  by force
      qed
      
       
    
    definition iface_subset :: "iface \<Rightarrow> iface \<Rightarrow> bool" where
      "iface_subset i1 i2 \<longleftrightarrow> internal_iface_name_subset (iface_sel i1) (iface_sel i2)"
    
    lemma iface_subset: "iface_subset i1 i2 \<longleftrightarrow> {i. match_iface i1 i} \<subseteq> {i. match_iface i2 i}"
      unfolding iface_subset_def
      apply(cases i1, cases i2)
      by(simp add: internal_iface_name_subset)


    definition iface_is_wildcard :: "iface \<Rightarrow> bool" where
      "iface_is_wildcard ifce \<equiv> iface_name_is_wildcard (iface_sel ifce)"
   
    lemma iface_is_wildcard_ifaceAny: "iface_is_wildcard ifaceAny"
      by(simp add: iface_is_wildcard_def ifaceAny_def)




  subsection\<open>Enumerating Interfaces\<close>
    private definition all_chars :: "char list" where
      "all_chars \<equiv> Enum.enum"
    private lemma all_chars: "set all_chars = (UNIV::char set)"
       by(simp add: all_chars_def enum_UNIV)
  
    text\<open>we can compute this, but its horribly inefficient!\<close>
    (*valid chars in an interface are NOT limited to the printable ones!*)
    private lemma strings_of_length_n: "set (List.n_lists n all_chars) = {s::string. length s = n}"
      apply(induction n)
       apply(simp; fail)
      apply(simp add: all_chars)
      apply(safe)
       apply(simp; fail)
      apply(simp)
      apply(rename_tac n x)
      apply(rule_tac x="drop 1 x" in exI)
      apply(simp)
      apply(case_tac x)
       apply(simp_all)
      done
  
    text\<open>Non-wildacrd interfaces of length @{term n}\<close>
    private definition non_wildcard_ifaces :: "nat \<Rightarrow> string list" where
     "non_wildcard_ifaces n \<equiv> filter (\<lambda>i. \<not> iface_name_is_wildcard i) (List.n_lists n all_chars)"

    text\<open>Example: (any number higher than zero are probably too inefficient)\<close>
    private lemma "non_wildcard_ifaces 0 = ['''']" by eval

    private lemma non_wildcard_ifaces: "set (non_wildcard_ifaces n) = {s::string. length s = n \<and> \<not> iface_name_is_wildcard s}"
      using strings_of_length_n non_wildcard_ifaces_def by auto
  
    private lemma "(\<Union> i \<in> set (non_wildcard_ifaces n). internal_iface_name_to_set i) = {s::string. length s = n \<and> \<not> iface_name_is_wildcard s}"
     by(simp add: non_wildcard_ifaces)
  
    text\<open>Non-wildacrd interfaces up to length @{term n}\<close>
    private fun non_wildcard_ifaces_upto :: "nat \<Rightarrow> string list" where
      "non_wildcard_ifaces_upto 0 = [[]]" |
      "non_wildcard_ifaces_upto (Suc n) = (non_wildcard_ifaces (Suc n)) @ non_wildcard_ifaces_upto n"
    private lemma non_wildcard_ifaces_upto: "set (non_wildcard_ifaces_upto n) = {s::string. length s \<le> n \<and> \<not> iface_name_is_wildcard s}"
      apply(induction n)
       apply fastforce
      using non_wildcard_ifaces by fastforce


  subsection\<open>Negating Interfaces\<close>
    private lemma inv_iface_name_set: "- (internal_iface_name_to_set i) = (
      if iface_name_is_wildcard i
      then
        {c |c. length c < length (butlast i)} \<union> {c @ cs |c cs. length c = length (butlast i) \<and> c \<noteq> butlast i}
      else
        {c | c. length c < length i} \<union> {c@cs | c cs. length c \<ge> length i \<and> c \<noteq> i}
    )"
    proof -
      { fix i::string
        have inv_i_wildcard: "- {i@cs | cs. True} = {c | c. length c < length i} \<union> {c@cs | c cs. length c = length i \<and> c \<noteq> i}"
          apply(rule Set.equalityI)
           prefer 2
           apply(safe)[1]
            apply(simp;fail)
           apply(simp;fail)
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
      } note inv_i_wildcard=this
      { fix i::string
        have inv_i_nowildcard: "- {i::string} = {c | c. length c < length i} \<union> {c@cs | c cs. length c \<ge> length i \<and> c \<noteq> i}"
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
      } note inv_i_nowildcard=this
    show ?thesis
      proof(cases "iface_name_is_wildcard i")
      case True with inv_i_wildcard show ?thesis by force
      next
      case False with inv_i_nowildcard show ?thesis by force
      qed
    qed

    text\<open>Negating is really not intuitive.
          The Interface @{term "''et''"} is in the negated set of @{term "''eth+''"}.
          And the Interface @{term "''et+''"} is also in this set! This is because @{term "''+''"}
          is a normal interface character and not a wildcard here!
          In contrast, the set described by @{term "''et+''"} (with @{term "''+''"} a wildcard)
          is not a subset of the previously negated set.\<close>
    lemma "''et'' \<in> - (internal_iface_name_to_set ''eth+'')" by(simp)
    lemma "''et+'' \<in> - (internal_iface_name_to_set ''eth+'')" by(simp)
    lemma "''+'' \<in> - (internal_iface_name_to_set ''eth+'')" by(simp)
    lemma "\<not> {i. match_iface (Iface ''et+'') i} \<subseteq> - (internal_iface_name_to_set ''eth+'')" by force

    text\<open>Because @{term "''+''"} can appear as interface wildcard and normal interface character,
          we cannot take negate an @{term "Iface i"} such that we get back @{typ "iface list"} which
          describe the negated interface.\<close>
    lemma "''+'' \<in> - (internal_iface_name_to_set ''eth+'')" by(simp)




  fun compress_pos_interfaces :: "iface list \<Rightarrow> iface option" where
    "compress_pos_interfaces [] = Some ifaceAny" |
    "compress_pos_interfaces [i] = Some i" |
    "compress_pos_interfaces (i1#i2#is) = (case iface_conjunct i1 i2 of None \<Rightarrow> None | Some i \<Rightarrow> compress_pos_interfaces (i#is))"

  lemma compress_pos_interfaces_Some: "compress_pos_interfaces ifces = Some ifce \<Longrightarrow> 
          match_iface ifce p_i \<longleftrightarrow> (\<forall> i\<in> set ifces. match_iface i p_i)"
  proof(induction ifces rule: compress_pos_interfaces.induct)
    case 1 thus ?case by (simp add: match_ifaceAny)
    next
    case 2 thus ?case by simp
    next
    case (3 i1 i2) thus ?case
    apply(simp)
    apply(case_tac "iface_conjunct i1 i2")
     apply(simp; fail)
    apply(simp)
    using iface_conjunct_Some by presburger
  qed

  lemma compress_pos_interfaces_None: "compress_pos_interfaces ifces = None \<Longrightarrow> 
          \<not> (\<forall> i\<in> set ifces. match_iface i p_i)"
  proof(induction ifces rule: compress_pos_interfaces.induct)
    case 1 thus ?case by (simp add: match_ifaceAny)
    next
    case 2 thus ?case by simp
    next
    case (3 i1 i2) thus ?case
      apply(cases "iface_conjunct i1 i2", simp_all)
       apply (blast dest: iface_conjunct_None)
      by (blast dest: iface_conjunct_Some)
  qed



  declare match_iface.simps[simp del]
  declare iface_name_is_wildcard.simps[simp del]
end

end
