(*  Title:      IPAddr.thy
    Authors:    Cornelius Diekmann
*)
theory IPAddr
imports Main
  NumberWang
  WordInterval_Lists
  "~~/src/HOL/Word/Word"
  "./l4v/lib/WordLemmaBucket" (*will things break if I include this early?*)
begin

section {*Modelling IP Adresses*}
  text{*An IP address is basically a unsigned integer.
        We model IP addresses of arbitrary lengths.
        The files @{file "IPv4Addr.thy"} @{file "IPv6Addr.thy"} concrete this for IPv4 and IPv6.*}

  text{*The maximum IP addres*}
  definition max_ip_addr :: "'i::len word" where 
    "max_ip_addr \<equiv> of_nat ((2^(len_of(TYPE('i)))) - 1)"

  lemma max_ip_addr_max_word: "max_ip_addr = max_word"
    by(simp add: max_ip_addr_def max_word_def word_of_int_minus)
    
  lemma max_ipv4_addr_max: "\<forall>a. a \<le> max_ip_addr"
    by(simp add: max_ip_addr_max_word)
  lemma range_0_max_UNIV: "UNIV = {0 .. max_ip_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ip_addr_max_word) fastforce

  lemma size_ipaddr: "size (x::'i::len word) = len_of(TYPE('i))" by(simp add:word_size)

  text{*previous and next IP addresses, without wrap around*}
    definition ip_next :: "'i::len word \<Rightarrow> 'i word" where
      "ip_next a \<equiv> if a = max_ip_addr then max_ip_addr else a + 1"
    definition ip_prev :: "'i::len word \<Rightarrow> 'i word" where
      "ip_prev a \<equiv> if a = 0 then 0 else a - 1"
  
    lemma "ip_next (2::8 word) = 3" by eval
    lemma "ip_prev (2::8 word) = 1" by eval
    lemma "ip_prev (0::8 word) = 0" by eval

subsection{*Sets of IP addresses*}

  (*Warning, not executable!*)
  text{*192.168.0.0 255.255.255.0*}
  definition ipset_from_netmask::"'i::len word \<Rightarrow> 'i::len word \<Rightarrow> 'i::len word set" where
    "ipset_from_netmask addr netmask \<equiv> let network_prefix = (addr AND netmask) in {network_prefix .. network_prefix OR (NOT netmask)}"
  (*Example: ipset_from_netmask 192.168.1.129  255.255.255.0  = {192.168.1.0 .. 192.168.1.255}*)

  text{*192.168.0.0/24*}
  definition ipset_from_cidr ::"'i::len word \<Rightarrow> nat \<Rightarrow> 'i::len word set" where
    "ipset_from_cidr addr pflength \<equiv> ipset_from_netmask addr ((mask pflength) << (len_of(TYPE('i)) - pflength))"
  (*Example: ipset_from_cidr 192.168.1.129 24  = {192.168.1.0 .. 192.168.1.255}*)

  lemma ipset_from_cidr_0: "ipset_from_cidr foo 0 = UNIV"
    by(auto simp add: ipset_from_cidr_def ipset_from_netmask_def Let_def)

  
  (*alternate definition*)
  lemma ipset_from_cidr_alt1: fixes addr :: "'i::len word"
    shows "ipset_from_cidr addr pflength = ipset_from_netmask addr ((mask pflength) << (len_of(TYPE('i)) - pflength))"
    by(simp add: ipset_from_cidr_def)


  lemma ipset_from_cidr_alt2:
    fixes addr :: "'i::len word"
    shows "ipset_from_cidr addr pflength \<equiv> 
            ipset_from_netmask addr (of_bl ((replicate pflength True) @ (replicate ((len_of(TYPE('i))) - pflength)) False))"
    by(simp add: ipset_from_cidr_alt1 mask_bl Word.shiftl_of_bl)


  (*TODO: obsoletes NOT_mask_len32, requires WordLemmaBucket.*)
  (*TODO: add to l4v*)
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
    apply(simp only: ipset_from_cidr_alt1 ipset_from_netmask_def Let_def)
    apply(subst Word.word_oa_dist)
    apply(simp only: word_or_not)
    apply(simp only: Word.word_and_max)
    apply(simp add: NOT_mask_shifted_lenword)
    done

  lemma "ipset_from_cidr 0 0 = UNIV" using ipset_from_cidr_0 by blast

  lemma ipset_from_cidr_wordlength: 
    fixes foo :: "'i::len word"
    shows "ipset_from_cidr foo (len_of TYPE('i)) = {foo}"
    by(simp add: ipset_from_cidr_alt1 ipset_from_netmask_def Let_def mask_def)


  lemma ipset_from_netmask_base_mask_consume:
    fixes base :: "'a::len word"
    shows "ipset_from_netmask (base AND NOT mask (len_of TYPE('a) - m)) (NOT mask (len_of TYPE('a) - m)) =
            ipset_from_netmask base (NOT mask (len_of TYPE('a) - m))"
    unfolding ipset_from_netmask_def
    by(simp add: AND_twice)




  text{*Another definition of CIDR notation: All IP addresse which are equal on the first @{text "len - n"} bits*}
  definition ip_cidr_set :: "'i::len word \<Rightarrow> nat \<Rightarrow> 'i word set" where
    "ip_cidr_set i r = {j . i AND NOT mask (len_of TYPE('i) - r) = j AND NOT mask (len_of TYPE('i) - r)}"



  text{*making element check executable*}
  lemma addr_in_ipset_from_netmask_code[code_unfold]: 
    "addr \<in> (ipset_from_netmask base netmask) \<longleftrightarrow> (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by(simp add: ipset_from_netmask_def Let_def)
  lemma addr_in_ipset_from_cidr_code[code_unfold]: "(addr::'i::len word) \<in> (ipset_from_cidr pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (len_of (TYPE('i)) - len))) \<le> addr \<and> addr \<le> pre OR (mask (len_of (TYPE('i)) - len))"
  unfolding ipset_from_cidr_alt by simp


  definition iprange_single :: "'i::len word \<Rightarrow> 'i wordinterval" where
    "iprange_single ip \<equiv> WordInterval ip ip"

  fun iprange_interval :: "('i::len word \<times> 'i::len word) \<Rightarrow> 'i wordinterval" where
    "iprange_interval (ip_start, ip_end) = WordInterval ip_start ip_end"
  declare iprange_interval.simps[simp del]


  lemma "wordinterval_to_set (iprange_single ip) = {ip}" by(simp add: iprange_single_def)
  lemma "wordinterval_to_set (iprange_interval (ip1, ip2)) = {ip1 .. ip2}" by(simp add: iprange_interval.simps)
  
  text{*Now we can use the set operations on @{typ "'i::len wordinterval"}s*}

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

end
