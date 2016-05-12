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

  lemma "ipset_from_cidr 0 0 = UNIV" using ipset_from_cidr_0 by blast

  lemma ipset_from_cidr_wordlength: 
    fixes foo :: "'i::len word"
    shows "ipset_from_cidr foo (len_of TYPE('i)) = {foo}"
    by(simp add: ipset_from_cidr_def ipset_from_netmask_def Let_def mask_def)


  lemma ipset_from_netmask_base_mask_consume:
    fixes base :: "'a::len word"
    shows "ipset_from_netmask (base AND NOT mask (len_of TYPE('a) - m)) (NOT mask (len_of TYPE('a) - m)) =
            ipset_from_netmask base (NOT mask (len_of TYPE('a) - m))"
    unfolding ipset_from_netmask_def
    by(simp add: AND_twice)


  text{*Another definition of CIDR notation: All IP addresse which are equal on the first @{text "len - n"} bits*}
  definition ip_cidr_set :: "'i::len word \<Rightarrow> nat \<Rightarrow> 'i word set" where
    "ip_cidr_set i r = {j . i AND NOT mask (len_of TYPE('i) - r) = j AND NOT mask (len_of TYPE('i) - r)}"

  (*TODO: equivalence lemma here!*)


  lemma ipset_from_cidr_base_wellforemd: fixes base:: "'a::len word"
    assumes "mask (len_of TYPE('a) - l) AND base = 0"
      shows "ipset_from_cidr base l = {base .. base || mask (len_of TYPE('a) - l)}"
  proof -
    have maskshift_eq_not_mask_generic: "((mask m << len_of TYPE('a) - m) :: 'a::len word) = NOT mask (len_of TYPE('a) - m)" for m
      using NOT_mask_shifted_lenword by (metis word_not_not) 
    
    have *: "base AND NOT  mask (len_of TYPE('a) - l) = base"
      unfolding mask_eq_0_eq_x[symmetric] using assms word_bw_comms(1)[of base] by simp
    hence **: "base AND NOT mask (len_of TYPE('a) - l) OR mask (len_of TYPE('a) - l) = base OR mask (len_of TYPE('a) - l)"
      by simp
  
    have "ipset_from_netmask base (NOT mask (len_of TYPE('a) - l)) = {base .. base || mask (len_of TYPE('a) - l)}"
      by(simp add: ipset_from_netmask_def Let_def ** *)
    thus ?thesis by(simp add: ipset_from_cidr_def maskshift_eq_not_mask_generic)
  qed


  lemma ipset_from_cidr_large_pfxlen:
    fixes ip:: "'a::len word"
    assumes "n \<ge> len_of TYPE('a)"
    shows "ipset_from_cidr ip n = {ip}"
  proof -
    have obviously: "mask (len_of TYPE('a) - n) = 0" by (simp add: assms)
    show ?thesis
      apply(subst ipset_from_cidr_base_wellforemd)
       subgoal using assms by simp
      by (simp add: obviously)
  qed


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
      with `r1 \<le> r2` have "j \<in> ip_cidr_set j r1" "j \<in> ip_cidr_set j r1"
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



subsection{*IP Addresses in CIDR Notation*}

  fun ipcidr_to_interval_start :: "('a::len word \<times> nat) \<Rightarrow> 'a::len word" where
    "ipcidr_to_interval_start (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('a) - len);
          network_prefix = (pre AND netmask)
      in network_prefix)"
  fun ipcidr_to_interval_end :: "('a::len word \<times> nat) \<Rightarrow> 'a::len word" where
    "ipcidr_to_interval_end (pre, len) = (
      let netmask = (mask len) << (len_of TYPE('a) - len);
          network_prefix = (pre AND netmask)
      in network_prefix OR (NOT netmask))"
  definition ipcidr_to_interval :: "('a::len word \<times> nat) \<Rightarrow> ('a::len word \<times> 'a::len word)" where
    "ipcidr_to_interval cidr = (ipcidr_to_interval_start cidr, ipcidr_to_interval_end cidr)"


  lemma ipset_from_cidr_ipcidr_to_interval:
    "ipset_from_cidr base len = {ipcidr_to_interval_start (base,len) .. ipcidr_to_interval_end (base,len)}"
    by(simp add: Let_def ipcidr_to_interval_def ipset_from_cidr_def ipset_from_netmask_def)
  declare ipcidr_to_interval_start.simps[simp del] ipcidr_to_interval_end.simps[simp del]


     
    
end
