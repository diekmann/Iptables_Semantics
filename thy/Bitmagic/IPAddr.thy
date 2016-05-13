(*  Title:      IPAddr.thy
    Authors:    Cornelius Diekmann
*)
theory IPAddr
imports Main
  NumberWang
  WordInterval_Lists
  "~~/src/HOL/Word/Word"
begin

section \<open>Modelling IP Adresses\<close>
  text\<open>An IP address is basically a unsigned integer.
    We model IP addresses of arbitrary lengths.

    We will write @{typ "'i::len word"} for IP addresses of length @{term "len_of TYPE('i::len)"}.
    We use the convention to write @{typ 'i} whenever we mean IP addresses instead of generic words.
    When we will have later theorems with several polymorphic types in it (e.g. arbitrarily
    extensible packets), this makes it easier to spot that type @{typ 'i} is for IP addresses.

    The files @{file "IPv4Addr.thy"} @{file "IPv6Addr.thy"} concrete this for IPv4 and IPv6.\<close>

  text\<open>The maximum IP addres\<close>
  definition max_ip_addr :: "'i::len word" where 
    "max_ip_addr \<equiv> of_nat ((2^(len_of(TYPE('i)))) - 1)"

  lemma max_ip_addr_max_word: "max_ip_addr = max_word"
    by(simp add: max_ip_addr_def max_word_def word_of_int_minus)
    
  lemma max_ipv4_addr_max: "\<forall>a. a \<le> max_ip_addr"
    by(simp add: max_ip_addr_max_word)
  lemma range_0_max_UNIV: "UNIV = {0 .. max_ip_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ip_addr_max_word) fastforce

  lemma size_ipaddr: "size (x::'i::len word) = len_of(TYPE('i))" by(simp add:word_size)

subsection\<open>Sets of IP addresses\<close>

  (*Warning, not executable!*)
  text\<open>192.168.0.0 255.255.255.0\<close>
  definition ipset_from_netmask::"'i::len word \<Rightarrow> 'i::len word \<Rightarrow> 'i::len word set" where
    "ipset_from_netmask addr netmask \<equiv> let network_prefix = (addr AND netmask) in {network_prefix .. network_prefix OR (NOT netmask)}"
  (*Example: ipset_from_netmask 192.168.1.129  255.255.255.0  = {192.168.1.0 .. 192.168.1.255}*)

  text\<open>192.168.0.0/24\<close>
  definition ipset_from_cidr ::"'i::len word \<Rightarrow> nat \<Rightarrow> 'i::len word set" where
    "ipset_from_cidr addr pflength \<equiv> ipset_from_netmask addr ((mask pflength) << (len_of(TYPE('i)) - pflength))"
  (*Example: ipset_from_cidr 192.168.1.129 24  = {192.168.1.0 .. 192.168.1.255}*)

  lemma ipset_from_cidr_0: "ipset_from_cidr foo 0 = UNIV"
    by(auto simp add: ipset_from_cidr_def ipset_from_netmask_def Let_def)

  lemma ipset_from_netmask_minusone: 
    "ipset_from_netmask foo (- 1) = {foo}" by (simp add: ipset_from_netmask_def) 
  
  lemma ipset_from_cidr_bl:
    fixes addr :: "'i::len word"
    shows "ipset_from_cidr addr pflength \<equiv> 
            ipset_from_netmask addr (of_bl ((replicate pflength True) @ (replicate ((len_of(TYPE('i))) - pflength)) False))"
    by(simp add: ipset_from_cidr_def mask_bl Word.shiftl_of_bl)


  (*TODO: obsoletes NOT_mask_len32, requires WordLemmaBucket.*)
  (*TODO: added to l4v, use lemma from there*)
  lemma NOT_mask_shifted_lenword: "NOT ((mask len << (len_of(TYPE('a)) - len))::'a::len word) = (mask (len_of(TYPE('a)) - len))"
    apply(rule Word.word_bool_alg.compl_unique)
     using WordLemmaBucket.mask_shift_and_negate apply(simp; fail)
    apply (rule word_eqI)
    apply (simp add: word_size nth_shiftl nth_shiftr)
    apply auto
    done

  lemma ipset_from_cidr_alt: 
    fixes pre :: "'i::len word"
    shows "ipset_from_cidr pre len = {(pre AND ((mask len) << (len_of(TYPE('i)) - len))) .. pre OR (mask (len_of(TYPE('i)) - len))}"
    apply(simp only: ipset_from_cidr_def ipset_from_netmask_def Let_def)
    apply(subst Word.word_oa_dist)
    apply(simp only: word_or_not)
    apply(simp only: Word.word_and_max)
    apply(simp add: NOT_mask_shifted_lenword)
    done


  lemma ipset_from_cidr_alt2:
    fixes base ::"'i::len word"
    shows "ipset_from_cidr base len = 
           ipset_from_netmask base (NOT mask (len_of (TYPE('i)) - len))"
    apply(simp add: ipset_from_cidr_def)
    using NOT_mask_shifted_lenword by (metis word_not_not) 

  lemma "ipset_from_cidr 0 0 = UNIV" using ipset_from_cidr_0 by blast

  lemma ipset_from_cidr_wordlength: 
    fixes foo :: "'i::len word"
    shows "ipset_from_cidr foo (len_of TYPE('i)) = {foo}"
    by(simp add: ipset_from_cidr_def ipset_from_netmask_def Let_def mask_def)


  lemma ipset_from_netmask_base_mask_consume:
    fixes base :: "'i::len word"
    shows "ipset_from_netmask (base AND NOT mask (len_of TYPE('i) - m)) (NOT mask (len_of TYPE('i) - m)) =
            ipset_from_netmask base (NOT mask (len_of TYPE('i) - m))"
    unfolding ipset_from_netmask_def
    by(simp add: AND_twice)


  text\<open>Another definition of CIDR notation: All IP addresse which are equal on the first @{text "len - n"} bits\<close>
  definition ip_cidr_set :: "'i::len word \<Rightarrow> nat \<Rightarrow> 'i word set" where
    "ip_cidr_set i r = {j . i AND NOT mask (len_of TYPE('i) - r) = j AND NOT mask (len_of TYPE('i) - r)}"

  (*TODO: equivalence lemma here!*)


  lemma ipset_from_cidr_base_wellforemd: fixes base:: "'i::len word"
    assumes "mask (len_of TYPE('i) - l) AND base = 0"
      shows "ipset_from_cidr base l = {base .. base || mask (len_of TYPE('i) - l)}"
  proof -
    have maskshift_eq_not_mask_generic:
      "((mask l << len_of TYPE('i) - l) :: 'i::len word) = NOT mask (len_of TYPE('i) - l)"
      using NOT_mask_shifted_lenword by (metis word_not_not) 
    
    have *: "base AND NOT  mask (len_of TYPE('i) - l) = base"
      unfolding mask_eq_0_eq_x[symmetric] using assms word_bw_comms(1)[of base] by simp
    hence **: "base AND NOT mask (len_of TYPE('i) - l) OR mask (len_of TYPE('i) - l) = base OR mask (len_of TYPE('i) - l)"
      by simp
  
    have "ipset_from_netmask base (NOT mask (len_of TYPE('i) - l)) = {base .. base || mask (len_of TYPE('i) - l)}"
      by(simp add: ipset_from_netmask_def Let_def ** *)
    thus ?thesis by(simp add: ipset_from_cidr_def maskshift_eq_not_mask_generic)
  qed


  lemma ipset_from_cidr_large_pfxlen:
    fixes ip:: "'i::len word"
    assumes "n \<ge> len_of TYPE('i)"
    shows "ipset_from_cidr ip n = {ip}"
  proof -
    have obviously: "mask (len_of TYPE('i) - n) = 0" by (simp add: assms)
    show ?thesis
      apply(subst ipset_from_cidr_base_wellforemd)
       subgoal using assms by simp
      by (simp add: obviously)
  qed



(*TODO: rename*)
lemma ipv4set_from_cidr_eq_ip_cidr_set:
  fixes base::"'i::len word"
  shows "ipset_from_cidr base len = ip_cidr_set base len"
proof -
  have maskshift_eq_not_mask_generic: "((mask len << len_of TYPE('a) - len) :: 'a::len word) = NOT mask (len_of TYPE('a) - len)"
    using NOT_mask_shifted_lenword by (metis word_not_not) 

  have 1: "mask (len - m) AND base AND NOT mask (len - m) = 0"
    for len m and base::"'i::len word"
    by(simp add: word_bw_lcs)

  have 2: "mask (len_of TYPE('i) - len) AND pfxm_p = 0 \<Longrightarrow>
         (a \<in> ipset_from_netmask pfxm_p (NOT mask (len_of TYPE('i) - len))) \<longleftrightarrow>
         (pfxm_p = NOT mask (len_of TYPE('i) - len) AND a)" for a::"'i::len word" and pfxm_p
  apply(subst ipset_from_cidr_alt2[symmetric])
  apply(subst zero_base_lsb_imp_set_eq_as_bit_operation)
   apply(simp; fail)
  apply(subst ipset_from_cidr_base_wellforemd)
   apply(simp; fail)
  apply(simp)
  done

  from 2[OF 1, of _ base] have
    "(x \<in> ipset_from_netmask base (~~ mask (len_of TYPE('i) - len))) \<longleftrightarrow>
     (base && ~~ mask (len_of TYPE('i) - len) = x && ~~ mask (len_of TYPE('i) - len))" for x
  apply(subst ipset_from_netmask_base_mask_consume[symmetric])
  unfolding word_bw_comms(1)[of _ " ~~ mask (len_of TYPE('i) - len)"] by simp
  then show ?thesis
    unfolding ip_cidr_set_def ipset_from_cidr_def
    by(auto simp add:  maskshift_eq_not_mask_generic)
qed



subsection\<open>IP Addresses as WordIntervals\<close>
  definition iprange_single :: "'i::len word \<Rightarrow> 'i wordinterval" where
    "iprange_single ip \<equiv> WordInterval ip ip"

  fun iprange_interval :: "('i::len word \<times> 'i::len word) \<Rightarrow> 'i wordinterval" where
    "iprange_interval (ip_start, ip_end) = WordInterval ip_start ip_end"
  declare iprange_interval.simps[simp del]


  lemma "wordinterval_to_set (iprange_single ip) = {ip}" by(simp add: iprange_single_def)
  lemma "wordinterval_to_set (iprange_interval (ip1, ip2)) = {ip1 .. ip2}" by(simp add: iprange_interval.simps)
  
  text\<open>Now we can use the set operations on @{typ "'i::len wordinterval"}s\<close>

  term wordinterval_to_set
  term wordinterval_element
  term wordinterval_union
  term wordinterval_empty
  term wordinterval_setminus
  term wordinterval_UNIV
  term wordinterval_invert
  term wordinterval_intersection
  term wordinterval_subset
  term wordinterval_eq


subsection\<open>IP Addresses in CIDR Notation\<close>

  fun ipcidr_to_interval_start :: "('i::len word \<times> nat) \<Rightarrow> 'i::len word" where
    "ipcidr_to_interval_start (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('i) - len);
          network_prefix = (pre AND netmask)
      in network_prefix)"
  fun ipcidr_to_interval_end :: "('i::len word \<times> nat) \<Rightarrow> 'i::len word" where
    "ipcidr_to_interval_end (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('i) - len);
          network_prefix = (pre AND netmask)
      in network_prefix OR (NOT netmask))"
  definition ipcidr_to_interval :: "('i::len word \<times> nat) \<Rightarrow> ('i::len word \<times> 'i::len word)" where
    "ipcidr_to_interval cidr = (ipcidr_to_interval_start cidr, ipcidr_to_interval_end cidr)"


  lemma ipset_from_cidr_ipcidr_to_interval:
    "ipset_from_cidr base len = {ipcidr_to_interval_start (base,len) .. ipcidr_to_interval_end (base,len)}"
    by(simp add: Let_def ipcidr_to_interval_def ipset_from_cidr_def ipset_from_netmask_def)
  declare ipcidr_to_interval_start.simps[simp del] ipcidr_to_interval_end.simps[simp del]


  definition ipcidr_tuple_to_wordinterval :: "('i::len word \<times> nat) \<Rightarrow> 'i wordinterval" where
    "ipcidr_tuple_to_wordinterval iprng = iprange_interval (ipcidr_to_interval iprng)"


  (*TODO: rename*)
  lemma wordinterval_to_set_ipcidr_tuple_to_wordinterval:
    "wordinterval_to_set (ipcidr_tuple_to_wordinterval (b, m)) = ipset_from_cidr b m"
    unfolding ipcidr_tuple_to_wordinterval_def ipset_from_cidr_ipcidr_to_interval ipcidr_to_interval_def
    by(simp add: iprange_interval.simps)   






  context
  begin
    (*contributed by Lars Noschinski*)
    private lemma ip_cidr_set_change_base: "j \<in> ip_cidr_set i r \<Longrightarrow> ip_cidr_set j r = ip_cidr_set i r"
      by (auto simp: ip_cidr_set_def)
    
    private lemma less_and_not_mask_eq:
      fixes i :: "('a :: len) word"
      assumes "r2 \<le> r1" "i && ~~ mask r2 = x && ~~ mask r2"
      shows "i && ~~ mask r1 = x && ~~ mask r1"
    proof -
      have "i AND NOT mask r1 = (i && ~~ mask r2) && ~~ mask r1" (is "_ = ?w && _")
        using \<open>r2 \<le> r1\<close> by (simp add: and_not_mask_twice max_def)
      also have "?w = x && ~~ mask r2" by fact
      also have "\<dots> && ~~ mask r1 = x && ~~ mask r1"
        using \<open>r2 \<le> r1\<close> by (simp add: and_not_mask_twice max_def)
      finally show ?thesis .
    qed
    
    lemma ip_cidr_set_less:
      fixes i :: "'i::len word"
      shows "r1 \<le> r2 \<Longrightarrow> ip_cidr_set i r2 \<subseteq> ip_cidr_set i r1"
      unfolding ip_cidr_set_def
      apply auto
      apply (rule less_and_not_mask_eq[where ?r2.0="len_of TYPE('i) - r2"])
      apply auto
      done
    
    
    private lemma ip_cidr_set_intersect_subset_helper:
      fixes i1 r1 i2 r2
      assumes disj: "ip_cidr_set i1 r1 \<inter> ip_cidr_set i2 r2 \<noteq> {}" and  "r1 \<le> r2"
      shows "ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1"
      proof -
      from disj obtain j where "j \<in> ip_cidr_set i1 r1" "j \<in> ip_cidr_set i2 r2" by auto
      with \<open>r1 \<le> r2\<close> have "j \<in> ip_cidr_set j r1" "j \<in> ip_cidr_set j r1"
        using ip_cidr_set_change_base ip_cidr_set_less by blast+
    
      show "ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1"
      proof
        fix i assume "i \<in> ip_cidr_set i2 r2"
        with \<open>j \<in> ip_cidr_set i2 r2\<close> have "i \<in> ip_cidr_set j r2" using ip_cidr_set_change_base by auto
        also have "ip_cidr_set j r2 \<subseteq> ip_cidr_set j r1" using \<open>r1 \<le> r2\<close> ip_cidr_set_less by blast
        also have "\<dots> = ip_cidr_set i1 r1" using \<open>j \<in> ip_cidr_set i1 r1\<close> ip_cidr_set_change_base by blast
        finally show "i \<in> ip_cidr_set i1 r1" .
      qed
    qed
    
    lemma ip_cidr_set_notsubset_empty_inter:
      "\<not> ip_cidr_set i1 r1 \<subseteq> ip_cidr_set i2 r2 \<Longrightarrow>
       \<not> ip_cidr_set i2 r2 \<subseteq> ip_cidr_set i1 r1 \<Longrightarrow>
       ip_cidr_set i1 r1 \<inter> ip_cidr_set i2 r2 = {}"
      apply(cases "r1 \<le> r2")
       using ip_cidr_set_intersect_subset_helper apply blast
      apply(cases "r2 \<le> r1")
       using ip_cidr_set_intersect_subset_helper apply blast
      apply(simp)
      done
  end


(*TODO: move to IpAddresses or somewhere*)
lemma ip_cidr_intersect: " \<not> ipset_from_cidr b2 m2 \<subseteq> ipset_from_cidr b1 m1 \<Longrightarrow>
       \<not> ipset_from_cidr b1 m1 \<subseteq> ipset_from_cidr b2 m2 \<Longrightarrow>
       ipset_from_cidr b1 m1 \<inter> ipset_from_cidr b2 m2 = {}"
apply(simp add: ipv4set_from_cidr_eq_ip_cidr_set)
using ip_cidr_set_notsubset_empty_inter by blast



fun ipcidr_conjunct :: "('i::len word \<times> nat) \<Rightarrow> ('i word \<times> nat) \<Rightarrow> ('i word \<times> nat) option" where 
  "ipcidr_conjunct (base1, m1) (base2, m2) = (if ipset_from_cidr base1 m1 \<inter> ipset_from_cidr base2 m2 = {}
     then
      None
     else if 
      ipset_from_cidr base1 m1 \<subseteq> ipset_from_cidr base2 m2
     then 
      Some (base1, m1)
     else
      Some (base2, m2)
    )"

lemma ipcidr_conjunct_any: "ipcidr_conjunct (0, 0) (0, 0) \<noteq> None"
  by(simp add: ipset_from_cidr_0)

lemma ipcidr_conjunct_correct: "(case ipcidr_conjunct (b1, m1) (b2, m2)
                                        of Some (bx, mx) \<Rightarrow> ipset_from_cidr bx mx
                                        |  None \<Rightarrow> {})
    = (ipset_from_cidr b1 m1) \<inter> (ipset_from_cidr b2 m2)"
  apply(simp split: split_if_asm)
  using ip_cidr_intersect by fast
declare ipcidr_conjunct.simps[simp del]


lemma [code_unfold]: 
"ipcidr_conjunct ips1 ips2 = (if wordinterval_empty (wordinterval_intersection (ipcidr_tuple_to_wordinterval ips1) (ipcidr_tuple_to_wordinterval ips2))
     then
      None
     else if 
      wordinterval_subset (ipcidr_tuple_to_wordinterval ips1) (ipcidr_tuple_to_wordinterval ips2)
     then 
      Some ips1
     else
      Some ips2
    )"
apply(simp)
apply(cases ips1, cases ips2, rename_tac b1 m1 b2 m2, simp)
apply(safe)
   apply(auto simp add: wordinterval_to_set_ipcidr_tuple_to_wordinterval ipcidr_conjunct.simps split:split_if_asm)
done
(*with the code_unfold lemma before, this works!*)
lemma "ipcidr_conjunct (0::32 word,0) (8,1) = Some (8, 1)" by eval





  text\<open>making element check executable\<close>
  lemma addr_in_ipset_from_netmask_code[code_unfold]: 
    "addr \<in> (ipset_from_netmask base netmask) \<longleftrightarrow> (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by(simp add: ipset_from_netmask_def Let_def)
  lemma addr_in_ipset_from_cidr_code[code_unfold]: "(addr::'i::len word) \<in> (ipset_from_cidr pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (len_of (TYPE('i)) - len))) \<le> addr \<and> addr \<le> pre OR (mask (len_of (TYPE('i)) - len))"
  unfolding ipset_from_cidr_alt by simp


  
    
end
