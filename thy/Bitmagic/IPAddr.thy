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

  lemma ipset_from_prefix_wordlength: 
    fixes foo :: "'i::len word"
    shows "ipset_from_cidr foo (len_of TYPE('i)) = {foo}"
    by(simp add: ipset_from_cidr_alt1 ipset_from_netmask_def Let_def mask_def)


(*
  text{*making element check executable*}
  lemma addr_in_ipv4range_set_from_netmask_code[code_unfold]: 
    "addr \<in> (ipv4range_set_from_netmask base netmask) \<longleftrightarrow> (base AND netmask) \<le> addr \<and> addr \<le> (base AND netmask) OR (NOT netmask)"
    by(simp add: ipv4range_set_from_netmask_def Let_def)
  lemma addr_in_ipv4range_set_from_prefix_code[code_unfold]: "addr \<in> (ipv4range_set_from_prefix pre len) \<longleftrightarrow> 
              (pre AND ((mask len) << (32 - len))) \<le> addr \<and> addr \<le> pre OR (mask (32 - len))"
  unfolding ipv4range_set_from_prefix_alt by simp

  value "ipv4addr_of_dotdecimal (192,168,4,8) \<in> (ipv4range_set_from_prefix (ipv4addr_of_dotdecimal (192,168,0,42)) 16)"

  


  definition ipv4range_single :: "ipv4addr \<Rightarrow> 32 wordinterval" where
    "ipv4range_single ip \<equiv> WordInterval ip ip"

  fun ipv4range_range :: "(ipv4addr \<times> ipv4addr) \<Rightarrow> 32 wordinterval" where
    "ipv4range_range (ip_start, ip_end) = WordInterval ip_start ip_end"
  declare ipv4range_range.simps[simp del]

  definition ipv4range_to_set :: "32 wordinterval \<Rightarrow> (ipv4addr) set" where
    "ipv4range_to_set rg = wordinterval_to_set rg"

  definition ipv4range_element :: "'a::len word \<Rightarrow> 'a::len wordinterval \<Rightarrow> bool" where
    "ipv4range_element el rg = wordinterval_element el rg"

  definition ipv4range_union :: "32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where 
    "ipv4range_union r1 r2 = wordinterval_union r1 r2"

  definition ipv4range_empty :: "32 wordinterval \<Rightarrow> bool" where
    "ipv4range_empty rg = wordinterval_empty rg"

  definition ipv4range_setminus :: "32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where
    "ipv4range_setminus r1 r2 = wordinterval_setminus r1 r2"

  definition ipv4range_UNIV :: "32 wordinterval" where "ipv4range_UNIV \<equiv> wordinterval_UNIV"
    
  definition ipv4range_invert :: "32 wordinterval \<Rightarrow> 32 wordinterval" where 
    "ipv4range_invert r = ipv4range_setminus ipv4range_UNIV r"

  definition ipv4range_intersection :: "32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where
    "ipv4range_intersection r1 r2 = wordinterval_intersection r1 r2"

  definition ipv4range_subset:: "32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> bool" where
    "ipv4range_subset r1 r2 \<equiv> wordinterval_subset r1 r2"

  definition ipv4range_eq :: "32 wordinterval \<Rightarrow> 32 wordinterval \<Rightarrow> bool" where 
    "ipv4range_eq r1 r2 = wordinterval_eq r1 r2"




  lemma ipv4range_single_set_eq: "ipv4range_to_set (ipv4range_single ip) = {ip}"
    by(simp add: ipv4range_single_def ipv4range_to_set_def)
  lemma ipv4range_range_set_eq: "ipv4range_to_set (ipv4range_range (ip1, ip2)) = {ip1 .. ip2}"
    by(simp add: ipv4range_range.simps ipv4range_to_set_def)
  
  lemma ipv4range_element_set_eq[simp]: "ipv4range_element el rg = (el \<in> ipv4range_to_set rg)"
    by(simp add: ipv4range_element_def ipv4range_to_set_def)
  lemma ipv4range_union_set_eq[simp]: "ipv4range_to_set (ipv4range_union r1 r2) = ipv4range_to_set r1 \<union> ipv4range_to_set r2"
    by(simp add: ipv4range_to_set_def ipv4range_union_def)
  lemma ipv4range_empty_set_eq[simp]: "ipv4range_empty r \<longleftrightarrow> ipv4range_to_set r = {}"
    by(simp add: ipv4range_to_set_def ipv4range_empty_def)
  lemma ipv4range_setminus_set_eq[simp]: "ipv4range_to_set (ipv4range_setminus r1 r2) = ipv4range_to_set r1 - ipv4range_to_set r2"
    by(simp add: ipv4range_setminus_def ipv4range_to_set_def)
  lemma ipv4range_UNIV_set_eq[simp]: "ipv4range_to_set ipv4range_UNIV = UNIV"
    by(simp only: ipv4range_UNIV_def ipv4range_to_set_def wordinterval_UNIV_set_eq)
  lemma ipv4range_invert_set_eq[simp]: "ipv4range_to_set (ipv4range_invert r) = UNIV - ipv4range_to_set r"
    by(simp add: ipv4range_invert_def)
  lemma ipv4range_intersection_set_eq[simp]: "ipv4range_to_set (ipv4range_intersection r1 r2) = ipv4range_to_set r1 \<inter> ipv4range_to_set r2"
    by(simp add: ipv4range_intersection_def ipv4range_to_set_def)
  lemma ipv4range_subset_set_eq[simp]: "ipv4range_subset r1 r2 = (ipv4range_to_set r1 \<subseteq> ipv4range_to_set r2)"
    by(simp add: ipv4range_subset_def ipv4range_to_set_def)
  lemma ipv4range_eq_set_eq: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_to_set r1 = ipv4range_to_set r2"
    unfolding ipv4range_eq_def ipv4range_to_set_def using wordinterval_eq_set_eq by blast

  declare ipv4range_range_set_eq[unfolded ipv4range_range.simps, simp]
  declare ipv4range_union_set_eq[unfolded ipv4range_union_def wordinterval_union_def, simp]


  thm iffD1[OF ipv4range_eq_set_eq]
  declare iffD1[OF ipv4range_eq_set_eq, cong]
  lemma ipv4range_eq_comm: "ipv4range_eq r1 r2 \<longleftrightarrow> ipv4range_eq r2 r1"
    unfolding ipv4range_eq_def wordinterval_eq_set_eq by blast
  lemma ipv4range_to_set_alt: "ipv4range_to_set r = {x. ipv4range_element x r}"
    unfolding ipv4range_element_set_eq by blast
 
  lemma ipv4range_un_empty: "ipv4range_empty r1 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r2"
    by(subst ipv4range_eq_set_eq, simp)
  lemma ipv4range_un_emty_b: "ipv4range_empty r2 \<Longrightarrow> ipv4range_eq (ipv4range_union r1 r2) r1"
    by(subst ipv4range_eq_set_eq, simp)
  
  lemma ipv4range_Diff_triv: "ipv4range_empty (ipv4range_intersection a b) \<Longrightarrow> ipv4range_eq (ipv4range_setminus a b) a"
    unfolding ipv4range_eq_set_eq by(simp add: Diff_triv )
    (*by(simp only: wordinterval_Diff_triv ipv4range_eq_def ipv4range_setminus_def ipv4range_intersection_def wordinterval_intersection_def ipv4range_empty_def)*)


  lemma 
  	fixes k :: "'a :: complete_lattice"
  	shows "is_lowest_element x S \<longleftrightarrow> (x::'a) = Inf S"
  oops (*Auto Quickcheck found a counterexample:*)
    
  fun ipv4range_lowest_element :: "32 wordinterval \<Rightarrow> ipv4addr option" where
    "ipv4range_lowest_element (WordInterval s e) = (if s \<le> e then Some s else None)" | 
    "ipv4range_lowest_element (RangeUnion A B) = (case (ipv4range_lowest_element A, ipv4range_lowest_element B) of
      (Some a, Some b) \<Rightarrow> Some (if a < b then a else b) |
      (None, Some b) \<Rightarrow> Some b |
      (Some a, None) \<Rightarrow> Some a |
      (None, None) \<Rightarrow> None)"

  lemma ipv4range_lowest_none_empty: "ipv4range_lowest_element r = None \<longleftrightarrow> ipv4range_empty r"
    proof(induction r)
    case WordInterval thus ?case by simp
    next
    case RangeUnion thus ?case by fastforce
    qed
    

  lemma ipv4range_lowest_element_correct_A: "ipv4range_lowest_element r = Some x \<Longrightarrow> is_lowest_element x (ipv4range_to_set r)"
    unfolding is_lowest_element_def
    apply(induction r arbitrary: x rule: ipv4range_lowest_element.induct)
     apply(rename_tac rs re x, case_tac "rs \<le> re", auto)[1]
    apply(subst(asm) ipv4range_lowest_element.simps(2))
    apply(rename_tac A B x)
    apply(case_tac     "ipv4range_lowest_element B")
     apply(case_tac[!] "ipv4range_lowest_element A")
       apply(simp_all add: ipv4range_lowest_none_empty)[3]
    apply fastforce
  done


  lemma ipv4range_lowest_element_set_eq: assumes "\<not> ipv4range_empty r"
    shows "(ipv4range_lowest_element r = Some x) = (is_lowest_element x (ipv4range_to_set r))"
    (*unfolding is_lowest_element_def*)
    proof(rule iffI)
      assume "ipv4range_lowest_element r = Some x"
      thus "is_lowest_element x (ipv4range_to_set r)"
     using ipv4range_lowest_element_correct_A ipv4range_lowest_none_empty by simp
    next
      assume "is_lowest_element x (ipv4range_to_set r)"
      with assms show "(ipv4range_lowest_element r = Some x)"
        proof(induction r arbitrary: x rule: ipv4range_lowest_element.induct)
        case 1 thus ?case by(simp add: is_lowest_element_def)
        next
        case (2 A B x)

        have is_lowest_RangeUnion: "is_lowest_element x (ipv4range_to_set A \<union> ipv4range_to_set B) \<Longrightarrow> 
          is_lowest_element x (ipv4range_to_set A) \<or> is_lowest_element x (ipv4range_to_set B)"
          by(simp add: is_lowest_element_def)
      
         (*why \<And> A B?*)
         have ipv4range_lowest_element_RangeUnion: "\<And>a b A B. ipv4range_lowest_element A = Some a \<Longrightarrow> ipv4range_lowest_element B = Some b \<Longrightarrow>
                  ipv4range_lowest_element (RangeUnion A B) = Some (min a b)"
           by(auto dest!: ipv4range_lowest_element_correct_A simp add: is_lowest_element_def min_def)
         
        from 2 show ?case
        apply(case_tac     "ipv4range_lowest_element B")
         apply(case_tac[!] "ipv4range_lowest_element A")
           apply(auto simp add: is_lowest_element_def)[3]
        apply(subgoal_tac "\<not> ipv4range_empty A \<and> \<not> ipv4range_empty B")
         prefer 2
         using arg_cong[where f = Not, OF ipv4range_lowest_none_empty] apply(simp, metis)
        apply(drule(1) ipv4range_lowest_element_RangeUnion)
        apply(simp split: option.split_asm add: min_def)
         apply(drule is_lowest_RangeUnion)
         apply(elim disjE)
          apply(simp add: is_lowest_element_def)
         apply(clarsimp simp add: ipv4range_lowest_none_empty)
        
        apply(simp add: is_lowest_element_def)
        apply(clarsimp simp add: ipv4range_lowest_none_empty)
        using ipv4range_lowest_element_correct_A[simplified is_lowest_element_def]
        by (metis Un_iff not_le)
      qed
    qed
*)
end
