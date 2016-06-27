(*  Title:      CIDR_Split.thy
    Authors:    Julius Michaelis, Cornelius Diekmann
*)
theory CIDR_Split
imports IP_Address
        Prefix_Match
        Hs_Compat
begin

section\<open>CIDR Split Motivation (Example for IPv4)\<close>
  text\<open>When talking about ranges of IP addresses, we can make the ranges explicit by listing their elements.\<close>
context
begin
  private lemma "map (of_nat \<circ> nat) [1 .. 4] = ([1, 2, 3, 4]:: 32 word list)" by eval
  private definition ipv4addr_upto :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word list" where
    "ipv4addr_upto i j \<equiv> map (of_nat \<circ> nat) [int (unat i) .. int (unat j)]"
  private lemma ipv4addr_upto: "set (ipv4addr_upto i j) = {i .. j}"
    proof -
    have helpX:"\<And>f (i::nat) (j::nat). (f \<circ> nat) ` {int i..int j} = f ` {i .. j}"
      apply(intro set_eqI)
      apply(safe)
       apply(force)
      by (metis Set_Interval.transfer_nat_int_set_functions(2) image_comp image_eqI)
    {   fix xa :: int
        assume a1: "int (unat i) \<le> xa \<and> xa \<le> int (unat j)"
        then have f2: "int (nat xa) = xa"
          by force
        then have "unat (of_int xa::32 word) = nat xa"
          using a1 by (metis (full_types) le_unat_uoi nat_int nat_mono of_int_of_nat_eq)
        then have "i \<le> of_int xa" and "of_int xa \<le> j"
          using f2 a1 by (metis (no_types) uint_nat word_le_def)+
    } note hlp=this
    show ?thesis
      unfolding ipv4addr_upto_def
      apply(intro set_eqI)
      apply(simp)
      apply(safe)
        apply(simp_all)
        using hlp apply blast
       using hlp apply blast
      apply(simp add: helpX)
      by (metis atLeastAtMost_iff image_eqI word_le_nat_alt word_unat.Rep_inverse)
    qed

  text\<open>The function @{const ipv4addr_upto} gives back a list of all the ips in the list.
        This list can be pretty huge! In the following, we will use CIDR notation (e.g. 192.168.0.0/24)
        to describe the list more compactly.\<close>
end



section\<open>CIDR Split\<close>

context
begin

private lemma find_SomeD: "find f x = Some y \<Longrightarrow> f y \<and> y \<in> set x" 
  by(induction x; simp split: if_splits)

(*pfxes needs a dummy parameter. The first parameter is a dummy that we have the 'a::len0 type and
  can refer to its length.*)
private definition pfxes :: "'a::len0 itself \<Rightarrow> nat list" where
  "pfxes _ = map nat [0..int(len_of TYPE ('a))]"
private lemma "pfxes TYPE(32) = map nat [0 .. 32]" by eval

private definition "largest_contained_prefix (a::('a :: len) word) r = (
  let cs = (map (\<lambda>s. PrefixMatch a s) (pfxes TYPE('a)));
      (* anything that is a subset should also be a valid prefix. but try proving that.*)
      cfs = find (\<lambda>s. valid_prefix s \<and> wordinterval_subset (prefix_to_wordinterval s) r) cs in
  cfs)
"
(* The joke is that it is always Some, given that a \<in> r. *)

text\<open>Split off one prefix:\<close>
private definition wordinterval_CIDR_split1
  :: "'a::len wordinterval \<Rightarrow> 'a prefix_match option \<times> 'a wordinterval" where
  "wordinterval_CIDR_split1 r \<equiv> (
   let ma = wordinterval_lowest_element r in
   case ma of 
      None \<Rightarrow> (None, r) |
      Some a \<Rightarrow> (case largest_contained_prefix a r of 
        None \<Rightarrow> (None, r) |
        Some m \<Rightarrow> (Some m, wordinterval_setminus r (prefix_to_wordinterval m))))"

private lemma wordinterval_CIDR_split1_innard_helper: fixes a::"'a::len word"
  shows "wordinterval_lowest_element r = Some a \<Longrightarrow> 
  largest_contained_prefix a r \<noteq> None"
proof -
  assume a: "wordinterval_lowest_element r = Some a"
  have b: "(a,len_of(TYPE('a))) \<in> set (map (Pair a) (pfxes TYPE('a)))"
    unfolding pfxes_def set_map set_upto
    using Set.image_iff atLeastAtMost_iff int_eq_iff order_refl by metis (*400ms*)
  have c: "valid_prefix (PrefixMatch a (len_of(TYPE('a))))" by(simp add: valid_prefix_def pfxm_mask_def)
  have "wordinterval_to_set (prefix_to_wordinterval (PrefixMatch a (len_of(TYPE('a))))) = {a}"
    unfolding prefix_to_wordinterval_def pfxm_mask_def by simp
  moreover have "a \<in> wordinterval_to_set r"
    using a wordinterval_lowest_element_set_eq wordinterval_lowest_none_empty
    by (metis is_lowest_element_def option.distinct(1))
  ultimately have d:
    "wordinterval_to_set (prefix_to_wordinterval (PrefixMatch a (len_of TYPE('a)))) \<subseteq> wordinterval_to_set r"
    by simp
  show ?thesis
    unfolding largest_contained_prefix_def Let_def
    using b c d by(auto simp add: find_None_iff)
qed

private lemma r_split1_not_none: fixes r:: "'a::len wordinterval"
  shows "\<not> wordinterval_empty r \<Longrightarrow> fst (wordinterval_CIDR_split1 r) \<noteq> None"
  unfolding wordinterval_CIDR_split1_def Let_def
  by(cases "wordinterval_lowest_element r")
    (auto simp add: wordinterval_lowest_none_empty 
          dest: wordinterval_CIDR_split1_innard_helper)

private lemma largest_contained_prefix_subset:
  "largest_contained_prefix a r = Some p \<Longrightarrow> wordinterval_to_set (prefix_to_wordinterval p) \<subseteq> wordinterval_to_set r"
unfolding largest_contained_prefix_def Let_def
by(drule find_SomeD) simp

private lemma wordinterval_CIDR_split1_snd: "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow> u = wordinterval_setminus r (prefix_to_wordinterval s)"
  unfolding wordinterval_CIDR_split1_def Let_def by(clarsimp split: option.splits)

private lemma largest_contained_prefix_subset_s1D:
  "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow> wordinterval_to_set (prefix_to_wordinterval s) \<subseteq> wordinterval_to_set r"
by(intro largest_contained_prefix_subset[where a = "the (wordinterval_lowest_element r)"])
  (simp add: wordinterval_CIDR_split1_def split: option.splits)

private theorem wordinterval_CIDR_split1_preserve: fixes r:: "'a::len wordinterval"
  shows "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow> wordinterval_eq (wordinterval_union (prefix_to_wordinterval s) u) r"
proof(unfold wordinterval_eq_set_eq)
  assume as: "wordinterval_CIDR_split1 r = (Some s, u)"
  have ud: "u = wordinterval_setminus r (prefix_to_wordinterval s)"
    using as[THEN wordinterval_CIDR_split1_snd] .
  with largest_contained_prefix_subset_s1D[OF as]
  show "wordinterval_to_set (wordinterval_union (prefix_to_wordinterval s) u) = wordinterval_to_set r"
    unfolding ud by auto
qed

private lemma wordinterval_CIDR_split1_some_r_ne:
  "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow> \<not> wordinterval_empty r"
proof(rule ccontr, goal_cases)
  case 1
  have "wordinterval_lowest_element r = None" unfolding wordinterval_lowest_none_empty using 1(2) unfolding not_not .
  then have "wordinterval_CIDR_split1 r = (None, r)" unfolding wordinterval_CIDR_split1_def Let_def by simp
  then show False using 1(1) by simp
qed

private lemma wordinterval_CIDR_split1_distinct: fixes r:: "'a::len wordinterval"
  shows "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow>
           wordinterval_empty (wordinterval_intersection (prefix_to_wordinterval s) u)"
proof(goal_cases)
  case 1
  have nn: "wordinterval_lowest_element r \<noteq> None"
    using wordinterval_CIDR_split1_some_r_ne 1 wordinterval_lowest_none_empty by metis
  from 1 have "u = wordinterval_setminus r (prefix_to_wordinterval s)"
    by(elim wordinterval_CIDR_split1_snd)
  then show ?thesis by simp
qed

private lemma wordinterval_CIDR_split1_distinct2: fixes r:: "'a::len wordinterval"
  shows "wordinterval_CIDR_split1 r = (Some s, u) \<Longrightarrow>
          wordinterval_empty (wordinterval_intersection (prefix_to_wordinterval s) u)"
by(rule wordinterval_CIDR_split1_distinct[where r = r]) simp

function wordinterval_CIDR_split_prefixmatch
  :: "'a::len wordinterval \<Rightarrow> 'a prefix_match list" where
  "wordinterval_CIDR_split_prefixmatch rs = (
      if
        \<not> wordinterval_empty rs
      then case wordinterval_CIDR_split1 rs
                      of (Some s, u) \<Rightarrow> s # wordinterval_CIDR_split_prefixmatch u
                      |   _ \<Rightarrow> []
      else
        []
      )"
  by pat_completeness simp

termination wordinterval_CIDR_split_prefixmatch
proof(relation "measure (card \<circ> wordinterval_to_set)", rule wf_measure, unfold in_measure comp_def, goal_cases)
  note vernichter = wordinterval_empty_set_eq wordinterval_intersection_set_eq wordinterval_union_set_eq wordinterval_eq_set_eq
  case (1 rs x y x2)
  note some = 1(2)[unfolded 1(3), symmetric]
  from prefix_never_empty have "wordinterval_to_set (prefix_to_wordinterval x2) \<noteq> {}" unfolding vernichter .
  thus ?case
    unfolding wordinterval_CIDR_split1_preserve[OF some, unfolded vernichter, symmetric]
    unfolding card_Un_disjoint[OF finite finite wordinterval_CIDR_split1_distinct[OF some, unfolded vernichter]]
    by auto
qed

private lemma unfold_rsplit_case:
  assumes su: "(Some s, u) = wordinterval_CIDR_split1 rs"
  shows "(case wordinterval_CIDR_split1 rs of (None, u) \<Rightarrow> []
                                            | (Some s, u) \<Rightarrow> s # wordinterval_CIDR_split_prefixmatch u) = s # wordinterval_CIDR_split_prefixmatch u"
using su by (metis option.simps(5) split_conv)

lemma "wordinterval_CIDR_split_prefixmatch
          (RangeUnion (WordInterval (0x40000000) 0x5FEFBBCC) (WordInterval 0x5FEEBB1C 0x7FFFFFFF))
       = [PrefixMatch (0x40000000::32 word) 2]" by eval
lemma "length (wordinterval_CIDR_split_prefixmatch (WordInterval 0 (0xFFFFFFFE::32 word))) = 32" by eval


declare wordinterval_CIDR_split_prefixmatch.simps[simp del]

theorem wordinterval_CIDR_split_prefixmatch:
  "wordinterval_to_set r = (\<Union>x\<in>set (wordinterval_CIDR_split_prefixmatch r). prefix_to_wordset x)"
proof(induction r rule: wordinterval_CIDR_split_prefixmatch.induct)
  case (1 rs)
  show ?case proof(cases "wordinterval_empty rs")
    case True
    thus ?thesis by(simp add: wordinterval_CIDR_split_prefixmatch.simps)
  next
    case False
    obtain x y where s1: "wordinterval_CIDR_split1 rs = (Some x, y)"
      using r_split1_not_none[OF False] by(auto simp add: fst_def split: prod.splits)
    have mIH: "wordinterval_to_set y = (\<Union>x\<in>set (wordinterval_CIDR_split_prefixmatch y). prefix_to_wordset x)"
      using 1[OF False s1[symmetric] refl] .
    have *: "wordinterval_to_set rs = prefix_to_wordset x \<union> (\<Union>x\<in>set (wordinterval_CIDR_split_prefixmatch y). prefix_to_wordset x)"  
      unfolding mIH[symmetric]
    proof -
      have ud: "y = wordinterval_setminus rs (prefix_to_wordinterval x)"
        using wordinterval_CIDR_split1_snd[OF s1] .
      have ss: "prefix_to_wordset x \<subseteq> wordinterval_to_set rs"
        using largest_contained_prefix_subset_s1D[OF s1] by simp
      show "wordinterval_to_set rs = prefix_to_wordset x \<union> wordinterval_to_set y" 
        unfolding ud using ss by simp blast
    qed
    show ?thesis
      apply(subst wordinterval_CIDR_split_prefixmatch.simps)
      apply(unfold if_P[OF False] s1 prod.simps option.simps *) (* WOOOOO simplifier bug (* try making this a simp add: *) *)
      apply(simp)
    done
  qed
qed

lemma wordinterval_CIDR_split_prefixmatch_all_valid_Ball: fixes r:: "'a::len wordinterval"
  shows "\<forall>e\<in>set (wordinterval_CIDR_split_prefixmatch r). valid_prefix e \<and> pfxm_length e \<le> len_of TYPE('a)"
(* The induction is somewhat verbose, so it is less annoying to write the two down at once *)
proof(induction r rule: wordinterval_CIDR_split_prefixmatch.induct)
  case 1
  case (1 rs)
  show ?case proof(cases "wordinterval_empty rs")
    case False
    obtain x y where s1: "wordinterval_CIDR_split1 rs = (Some x, y)" 
      using r_split1_not_none[OF False] by(auto simp add: fst_def split: prod.splits)
    hence i1: "valid_prefix x"
      unfolding wordinterval_CIDR_split1_def Let_def largest_contained_prefix_def
      by(auto dest: find_SomeD split: option.splits)
    have i2: "pfxm_length x \<le> len_of TYPE('a)" 
      using s1 unfolding wordinterval_CIDR_split1_def Let_def largest_contained_prefix_def pfxes_def
      by(force split: option.splits dest: find_SomeD simp: nat_le_iff)
    have mIH: "\<forall>a\<in>set (wordinterval_CIDR_split_prefixmatch y). valid_prefix a \<and> pfxm_length a \<le> len_of TYPE('a)"
      using 1[OF False s1[symmetric] refl] .
    with i1 i2 show ?thesis
      apply(subst wordinterval_CIDR_split_prefixmatch.simps)
      apply(unfold if_P[OF False] s1 prod.simps option.simps)
      apply(simp)
    done
  qed (simp add: wordinterval_CIDR_split_prefixmatch.simps)
qed


private lemma wordinterval_CIDR_split_prefixmatch_all_valid_less_Ball_hlp:
	"x \<in> set [s\<leftarrow>map (PrefixMatch x2) (pfxes TYPE('a::len0)) . valid_prefix s \<and> wordinterval_to_set (prefix_to_wordinterval s) \<subseteq> wordinterval_to_set rs] \<Longrightarrow> pfxm_length x \<le> len_of TYPE('a)"
by(clarsimp simp: pfxes_def) presburger


text\<open>Since @{const wordinterval_CIDR_split_prefixmatch} only returns valid prefixes, we can safely convert it to CIDR lists\<close>
(* actually, just valid_prefix doesn't mean that the prefix length is sane. Fortunately, wordinterval_CIDR_split_prefixmatch_all_valid_Ball does entail that *)
lemma "valid_prefix (PrefixMatch (0::16 word) 20)" by(simp add: valid_prefix_def)

lemma wordinterval_CIDR_split_disjunct: "a \<in> set (wordinterval_CIDR_split_prefixmatch i) \<Longrightarrow>
  b \<in> set (wordinterval_CIDR_split_prefixmatch i) \<Longrightarrow> a \<noteq> b \<Longrightarrow>
  prefix_to_wordset a \<inter> prefix_to_wordset b = {}"
proof(induction i rule: wordinterval_CIDR_split_prefixmatch.induct)
  case (1 rs)
  note IH = 1(1)
  have prema: "a \<in> set (wordinterval_CIDR_split_prefixmatch rs)" (is "a \<in> ?os") using 1 by simp
  have premb: "b \<in> ?os" using 1 by simp
  show ?case proof(cases "wordinterval_empty rs")
    case False
    obtain x y where s1: "wordinterval_CIDR_split1 rs = (Some x, y)" 
      using r_split1_not_none[OF False] by(auto simp add: fst_def split: prod.splits)
    have mi: "k \<in> set (wordinterval_CIDR_split_prefixmatch y)" (is "k \<in> ?rs") 
      if p: "k \<noteq> x" "k \<in> ?os" for k using p s1 
      by(subst (asm) wordinterval_CIDR_split_prefixmatch.simps) (simp only: if_P[OF False] split: prod.splits option.splits; simp)
    have a: "k \<in> ?rs \<Longrightarrow> prefix_to_wordset k \<subseteq> wordinterval_to_set y" for k 
      (* this is actually a quite general statement, might make a lemma out of it *)
      unfolding wordinterval_CIDR_split_prefixmatch by blast
    have b: "prefix_to_wordset x \<inter> wordinterval_to_set y = {}"
      using wordinterval_CIDR_split1_snd[OF s1] by simp
    show ?thesis
    proof(cases "a = x"; cases "b = x")
      assume as: "a = x" "b \<noteq> x"
      with a[OF mi[OF as(2) premb]] b
      show ?thesis by blast
    next
      assume as: "a \<noteq> x" "b = x"
      with a[OF mi[OF as(1) prema]] b
      show ?thesis by blast
    next
      assume as: "a \<noteq> x" "b \<noteq> x" (* Nothing to do case *)
      have i: "a \<in> ?rs" "b \<in> ?rs"
        using as mi prema premb by blast+
      show "prefix_to_wordset a \<inter> prefix_to_wordset b = {}"
        by(rule IH[OF False s1[symmetric] refl i]) (fact 1)
    next
      assume as: "a = x" "b = x" (* impossible case *)
      with 1 have False by simp
      thus ?thesis ..
    qed
  next
    case True
    hence "wordinterval_CIDR_split_prefixmatch rs = []" by(simp add: wordinterval_CIDR_split_prefixmatch.simps)
    thus ?thesis using prema by simp
  qed
qed

lemma wordinterval_CIDR_split_distinct: "distinct (wordinterval_CIDR_split_prefixmatch i)"
(* wish this was a corollary *)
proof(induction i rule: wordinterval_CIDR_split_prefixmatch.induct)
  case (1 rs)
  show ?case proof(cases "wordinterval_empty rs")
    case False
    obtain x y where s1: "wordinterval_CIDR_split1 rs = (Some x, y)" 
      using r_split1_not_none[OF False] by(auto simp add: fst_def split: prod.splits)
    have mIH: "distinct (wordinterval_CIDR_split_prefixmatch y)"
      using 1[OF False s1[symmetric] refl] .
    have "prefix_to_wordset x \<inter> wordinterval_to_set y = {}"
      using wordinterval_CIDR_split1_snd[OF s1] by simp
    hence i1: "x \<notin> set (wordinterval_CIDR_split_prefixmatch y)"
      unfolding wordinterval_CIDR_split_prefixmatch using prefix_never_empty[of x, simplified] by blast
    show ?thesis
      using s1
      by(subst wordinterval_CIDR_split_prefixmatch.simps)
        (simp add: if_P[OF False] mIH i1 split: option.splits prod.splits)
  qed (simp add: wordinterval_CIDR_split_prefixmatch.simps)
qed

lemma wordinterval_CIDR_split_existential:
	"x \<in> wordinterval_to_set w \<Longrightarrow> \<exists>s. s \<in> set (wordinterval_CIDR_split_prefixmatch w) \<and> x \<in> prefix_to_wordset s"
using wordinterval_CIDR_split_prefixmatch[symmetric] by fastforce

subsection\<open>Versions for @{const ipset_from_cidr}\<close>

definition cidr_split :: "'i::len wordinterval \<Rightarrow> ('i word \<times> nat) list" where
  "cidr_split rs \<equiv> map prefix_match_to_CIDR (wordinterval_CIDR_split_prefixmatch rs)"
                                        
corollary cidr_split_prefix: 
  fixes r :: "'i::len wordinterval"
  shows "(\<Union>x\<in>set (cidr_split r). uncurry ipset_from_cidr x) = wordinterval_to_set r"
    unfolding wordinterval_CIDR_split_prefixmatch[symmetric] cidr_split_def
    apply(simp add: prefix_match_to_CIDR_def2 wordinterval_CIDR_split_prefixmatch)
    using prefix_to_wordset_ipset_from_cidr wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast

corollary cidr_split_prefix_single: 
  fixes start :: "'i::len word"
  shows "(\<Union>x\<in>set (cidr_split (iprange_interval (start, end))). uncurry ipset_from_cidr x) = {start..end}"
  unfolding wordinterval_to_set.simps[symmetric]
  using cidr_split_prefix iprange_interval.simps by metis

private lemma interval_in_splitD: "xa \<in> foo \<Longrightarrow> prefix_to_wordset xa \<subseteq> \<Union>(prefix_to_wordset ` foo)" by auto

lemma cidrsplit_no_overlaps: "\<lbrakk>
        x \<in> set (wordinterval_CIDR_split_prefixmatch wi);
        xa \<in> set (wordinterval_CIDR_split_prefixmatch wi); 
        pt && ~~ pfxm_mask x = pfxm_prefix x;
        pt && ~~ pfxm_mask xa = pfxm_prefix xa
        \<rbrakk>
       \<Longrightarrow> x = xa"
proof(rule ccontr, goal_cases)
	case 1
	hence "prefix_match_semantics x pt" "prefix_match_semantics xa pt" unfolding prefix_match_semantics_def by (simp_all add: word_bw_comms(1))
	moreover have "valid_prefix x" "valid_prefix xa" using 1(1-2) wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast+
	ultimately have "pt \<in> prefix_to_wordset x" "pt \<in> prefix_to_wordset xa"
	  using prefix_match_semantics_wordset by blast+
	with wordinterval_CIDR_split_disjunct[OF 1(1,2) 1(5)] show False by blast
qed

end



end
