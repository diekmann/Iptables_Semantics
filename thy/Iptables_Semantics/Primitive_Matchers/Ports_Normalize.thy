theory Ports_Normalize
imports Common_Primitive_Lemmas
begin


section\<open>Normalizing L4 Ports\<close>
subsection\<open>Defining Normalized Ports\<close>
  
  fun normalized_src_ports :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ports MatchAny = True" |
    "normalized_src_ports (Match (Src_Ports (L4Ports _ []))) = True" |
    "normalized_src_ports (Match (Src_Ports (L4Ports _ [_]))) = True" |
    "normalized_src_ports (Match (Src_Ports _)) = False" |
    "normalized_src_ports (Match _) = True" |
    "normalized_src_ports (MatchNot (Match (Src_Ports _))) = False" |
    "normalized_src_ports (MatchNot (Match _)) = True" |
    "normalized_src_ports (MatchAnd m1 m2) = (normalized_src_ports m1 \<and> normalized_src_ports m2)" |
    "normalized_src_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_src_ports (MatchNot (MatchNot _)) = False" |
    "normalized_src_ports (MatchNot MatchAny) = True"
  
  fun normalized_dst_ports :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_dst_ports MatchAny = True" |
    "normalized_dst_ports (Match (Dst_Ports (L4Ports _ []))) = True" |
    "normalized_dst_ports (Match (Dst_Ports (L4Ports _ [_]))) = True" |
    "normalized_dst_ports (Match (Dst_Ports _)) = False" |
    "normalized_dst_ports (Match _) = True" |
    "normalized_dst_ports (MatchNot (Match (Dst_Ports _))) = False" |
    "normalized_dst_ports (MatchNot (Match _)) = True" |
    "normalized_dst_ports (MatchAnd m1 m2) = (normalized_dst_ports m1 \<and> normalized_dst_ports m2)" |
    "normalized_dst_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ports (MatchNot (MatchNot _)) = False" |
    "normalized_dst_ports (MatchNot MatchAny) = True" 

  lemma normalized_src_ports_def2: "normalized_src_ports ms = normalized_n_primitive (is_Src_Ports, src_ports_sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) ms"
    by(induction ms rule: normalized_src_ports.induct, simp_all)
  lemma normalized_dst_ports_def2: "normalized_dst_ports ms = normalized_n_primitive (is_Dst_Ports, dst_ports_sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) ms"
    by(induction ms rule: normalized_dst_ports.induct, simp_all)



text\<open>Idea: first, remove all negated matches, then @{const normalize_match},
  then only work with @{const primitive_extractor} on @{const Pos} ones.
  They only need an intersect and split later on. 

  This is not very efficient because normalizing nnf will blow up a lot.
  but we can tune performance later on go for correctness first!
  Anything with @{const MatchOr} and @{const normalize_match} later is a bit inefficient.
\<close>




subsection\<open>Compressing Positive Matches on Ports into a Single Match\<close>
(*compressing positive matches on ports into a single match*)

  fun l4_ports_compress :: "ipt_l4_ports list \<Rightarrow> ipt_l4_ports match_compress" where
    "l4_ports_compress [] = MatchesAll" | 
    "l4_ports_compress [L4Ports proto ps] = MatchExpr (L4Ports proto (wi2l (wordinterval_compress (l2wi ps))))" |
    "l4_ports_compress (L4Ports proto1 ps1 # L4Ports proto2 ps2 # pss) =
      (if
          proto1 \<noteq> proto2
       then
         CannotMatch
       else
         l4_ports_compress (L4Ports proto1 (wi2l (wordinterval_intersection (l2wi ps1) (l2wi ps2))) # pss)
      )"

  value[code] "l4_ports_compress [L4Ports TCP [(22,22), (23,23)]]"
  
  (*only for src*)
  lemma raw_ports_compress_src_CannotMatch:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  and c: "l4_ports_compress pss = CannotMatch"
  shows "\<not> matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Src_Ports) pss)) a p"
  using c apply(induction pss rule: l4_ports_compress.induct)
    apply(simp; fail)
   apply(simp; fail)
  apply(simp add: primitive_matcher_generic.Ports_single[OF generic] bunch_of_lemmata_about_matches split: split_if_asm)
   apply meson
  by(simp add: l2wi_wi2l ports_to_set_wordinterval)

  lemma raw_ports_compress_dst_CannotMatch:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  and c: "l4_ports_compress pss = CannotMatch"
  shows "\<not> matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Dst_Ports) pss)) a p"
  using c apply(induction pss rule: l4_ports_compress.induct)
    apply(simp; fail)
   apply(simp; fail)
  apply(simp add: primitive_matcher_generic.Ports_single[OF generic] bunch_of_lemmata_about_matches split: split_if_asm)
   apply meson
  by(simp add: l2wi_wi2l ports_to_set_wordinterval)

  lemma l4_ports_compress_length_Matchall: "length pss > 0 \<Longrightarrow> l4_ports_compress pss \<noteq> MatchesAll"
    by(induction pss rule: l4_ports_compress.induct) simp+

  lemma raw_ports_compress_MatchesAll:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  and c: "l4_ports_compress pss = MatchesAll"
  shows "matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Src_Ports) pss)) a p"
  and "matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Dst_Ports) pss)) a p"
  using c apply(induction pss rule: l4_ports_compress.induct)
  by(simp add: l4_ports_compress_length_Matchall bunch_of_lemmata_about_matches split: split_if_asm)+

  lemma raw_ports_compress_src_MatchExpr:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  and c: "l4_ports_compress pss = MatchExpr m"
  shows "matches (\<beta>, \<alpha>) (Match (Src_Ports m)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Src_Ports) pss)) a p"
  using c apply(induction pss arbitrary: m rule: l4_ports_compress.induct)
    apply(simp add: bunch_of_lemmata_about_matches; fail)
   subgoal
   apply(simp add: bunch_of_lemmata_about_matches)
   apply(drule sym, simp)
   by(simp add: primitive_matcher_generic.Ports_single[OF generic] wordinterval_compress l2wi_wi2l ports_to_set_wordinterval)
  apply(case_tac m)
  apply(simp add: bunch_of_lemmata_about_matches split: split_if_asm)
  apply(simp add: primitive_matcher_generic.Ports_single[OF generic])
  apply(simp add: l2wi_wi2l ports_to_set_wordinterval)
  by fastforce
  
  lemma raw_ports_compress_dst_MatchExpr:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  and c: "l4_ports_compress pss = MatchExpr m"
  shows "matches (\<beta>, \<alpha>) (Match (Dst_Ports m)) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) (alist_and (map (Pos \<circ> Dst_Ports) pss)) a p"
  using c apply(induction pss arbitrary: m rule: l4_ports_compress.induct)
    apply(simp add: bunch_of_lemmata_about_matches; fail)
   subgoal
   apply(simp add: bunch_of_lemmata_about_matches)
   apply(drule sym, simp)
   by(simp add: primitive_matcher_generic.Ports_single[OF generic] wordinterval_compress l2wi_wi2l ports_to_set_wordinterval)
  apply(case_tac m)
  apply(simp add: bunch_of_lemmata_about_matches split: split_if_asm)
  apply(simp add: primitive_matcher_generic.Ports_single[OF generic])
  apply(simp add: l2wi_wi2l ports_to_set_wordinterval)
  by fastforce


subsection\<open>Rewriting Negated Matches on Ports\<close>

  fun l4_ports_negate_one
    :: "(ipt_l4_ports \<Rightarrow> 'i common_primitive) \<Rightarrow> ipt_l4_ports \<Rightarrow> ('i::len common_primitive) match_expr"
  where
    "l4_ports_negate_one C (L4Ports proto pts) = MatchOr
           (MatchNot (Match (Prot (Proto proto))))
            (Match (C (L4Ports proto (raw_ports_invert pts))))"

  lemma l4_ports_negate_one:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (l4_ports_negate_one Src_Ports ports) a p \<longleftrightarrow>
          matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports ports))) a p"
  and "matches (\<beta>, \<alpha>) (l4_ports_negate_one Dst_Ports ports) a p \<longleftrightarrow>
          matches (\<beta>, \<alpha>) (MatchNot (Match (Dst_Ports ports))) a p"
    apply(case_tac [!] ports)
    by(auto simp add: primitive_matcher_generic.Ports_single_not[OF generic]
                    MatchOr bunch_of_lemmata_about_matches
                    primitive_matcher_generic.Prot_single_not[OF generic]
                    primitive_matcher_generic.Ports_single[OF generic]
                    raw_ports_invert)

  lemma l4_ports_negate_one_nodisc:
    "\<forall>a. \<not> disc (C a) \<Longrightarrow> \<forall>a. \<not> disc (Prot a) \<Longrightarrow> \<not> has_disc disc (l4_ports_negate_one C pt)"
      apply(cases pt)
      by(simp add: MatchOr_def)

  lemma l4_ports_negate_one_not_has_disc_negated_generic:
    assumes noProt: "\<forall>a. \<not> disc (Prot a)"
    shows "\<not> has_disc_negated disc False (l4_ports_negate_one C ports)"
    apply(cases ports, rename_tac proto pts)
    by(simp add: MatchOr_def noProt)

  lemma l4_ports_negate_one_not_has_disc_negated:
    "\<not> has_disc_negated is_Src_Ports False (l4_ports_negate_one Src_Ports ports)"
    "\<not> has_disc_negated is_Dst_Ports False (l4_ports_negate_one Dst_Ports ports)"
    by(simp add: l4_ports_negate_one_not_has_disc_negated_generic)+
    
  lemma negated_normalized_folded_ports_nodisc:
    "\<forall>a. \<not> disc (C a) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<or> pts = [] \<Longrightarrow>
     m \<in> set (normalize_match (andfold_MatchExp (map (l4_ports_negate_one C) pts))) \<Longrightarrow>
      \<not> has_disc disc m"
    apply(subgoal_tac "\<not> has_disc disc (andfold_MatchExp (map (l4_ports_negate_one C) pts))")
     prefer 2
     apply(rule andfold_MatchExp_not_discI)
     apply(simp)
     apply(elim disjE)
      using l4_ports_negate_one_nodisc apply blast
     apply(simp; fail)
    using normalize_match_preserves_nodisc by blast
  
  lemma negated_normalized_folded_ports_normalized_n_primitive:
    "\<forall>a. \<not> disc (C a) \<Longrightarrow> (\<forall>a. \<not> disc (Prot a)) \<or> pts = [] \<Longrightarrow>
     x \<in> set (normalize_match (andfold_MatchExp (map (l4_ports_negate_one C) pts))) \<Longrightarrow>
      normalized_n_primitive (disc, sel) f x"
    apply(rule normalized_n_primitive_if_no_primitive)
     using normalized_nnf_match_normalize_match apply blast
    apply(rule negated_normalized_folded_ports_nodisc)
    by simp_all


  text\<open>beware, the result is not nnf normalized!\<close>
  lemma "\<not> normalized_nnf_match (l4_ports_negate_one C ports)"
    by(cases ports) (simp add: MatchOr_def)
  
  text\<open>Warning: does not preserve negated primitive property in general.
       Might be violated for @{const Prot}. We will nnf normalize after applying the function.\<close>
  lemma "\<forall>a. \<not> disc (C a) \<Longrightarrow> \<not> normalized_n_primitive (disc, sel) f (l4_ports_negate_one C a)"
    by(cases a)(simp add: MatchOr_def)

  declare l4_ports_negate_one.simps[simp del]

    
  lemma "((normalize_match (l4_ports_negate_one Src_Ports (L4Ports TCP [(22,22),(80,90)]))):: 32 common_primitive match_expr list)
    =
    [ MatchNot (Match (Prot (Proto TCP)))
    , Match (Src_Ports (L4Ports 6 [(0, 21), (23, 79), (91, 0xFFFF)]))]" by eval

  definition rewrite_negated_primitives
    :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> (*disc_sel C*)
        (('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a match_expr) \<Rightarrow> (*negate_one function*)
        'a match_expr \<Rightarrow> 'a match_expr" where
    "rewrite_negated_primitives disc_sel C negate m \<equiv>
        let (spts, rst) = primitive_extractor disc_sel m
        in if getNeg spts = [] then m else 
          MatchAnd
            (andfold_MatchExp (map (negate C) (getNeg spts)))
            (MatchAnd
              (andfold_MatchExp (map (Match \<circ> C) (getPos spts))) (*TODO: compress all the positive ports into one?*)
            rst)"

  text\<open>It does nothing of there is not even a negated primitive in it\<close>
  lemma rewrite_negated_primitives_unchanged_if_not_has_disc_negated:
  assumes n: "normalized_nnf_match m"
  and wf_disc_sel: "wf_disc_sel (disc,sel) C"
  and noDisc: "\<not> has_disc_negated disc False m"
  shows "rewrite_negated_primitives (disc,sel) C negate_f m = m"
    apply(simp add: rewrite_negated_primitives_def)
    apply(case_tac "primitive_extractor (disc,sel) m", rename_tac spts rst)
    apply(simp)
    apply(frule primitive_extractor_correct(8)[OF n wf_disc_sel])
    using noDisc by blast  

  lemma rewrite_negated_primitives_normalized_no_modification:
    assumes wf_disc_sel: "wf_disc_sel (disc, sel) C"
    and disc_p: "\<not> has_disc_negated disc False m"
    and n: "normalized_nnf_match m"
    and a: "a \<in> set (normalize_match (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m))"
    shows "a = m"
    proof -
      from rewrite_negated_primitives_unchanged_if_not_has_disc_negated[OF n wf_disc_sel disc_p]
      have m: "rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m = m" by simp
      from a show ?thesis
        apply(subst(asm) m)
        using normalize_match_already_normalized[OF n] by fastforce
    qed

  lemma rewrite_negated_primitives_preserves_not_has_disc:
  assumes n: "normalized_nnf_match m"
  and wf_disc_sel: "wf_disc_sel (disc, sel) C"
  and nodisc: "\<not> has_disc disc2 m"
  and noNeg: "\<not> has_disc_negated disc False m"
  and disc2_noC: "\<forall>a. \<not> disc2 (C a)"
  shows "\<not> has_disc disc2 (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m)"
    apply(subst rewrite_negated_primitives_unchanged_if_not_has_disc_negated)
    using n wf_disc_sel noNeg nodisc by(simp)+

  lemma rewrite_negated_primitives:
  assumes n: "normalized_nnf_match m" and wf_disc_sel: "wf_disc_sel disc_sel C"
  and negate_f: "\<forall>pts. matches \<gamma> (negate_f C pts) a p \<longleftrightarrow> matches \<gamma> (MatchNot (Match (C pts))) a p"
  shows "matches \<gamma> (rewrite_negated_primitives disc_sel C negate_f m) a p \<longleftrightarrow> matches \<gamma> m a p"
  proof -
    obtain spts rst where pext: "primitive_extractor disc_sel m = (spts, rst)"
      by(cases "primitive_extractor disc_sel m") simp
    obtain disc sel where disc_sel: "disc_sel = (disc, sel)" by(cases disc_sel) simp
    with wf_disc_sel have wf_disc_sel': "wf_disc_sel (disc, sel) C" by simp
    from disc_sel pext have pext': "primitive_extractor (disc, sel) m = (spts, rst)" by simp
      
    have "matches \<gamma> (andfold_MatchExp (map (negate_f C) (getNeg spts))) a p \<and>
          matches \<gamma> (andfold_MatchExp (map (Match \<circ> C) (getPos spts))) a p \<and> matches \<gamma> rst a p \<longleftrightarrow>
       matches \<gamma> m a p"
      apply(subst primitive_extractor_correct(1)[OF n wf_disc_sel' pext', symmetric])
      apply(simp add: andfold_MatchExp_matches)
      apply(simp add: negate_f)
      using alist_and_NegPos_map_getNeg_getPos_matches by fast
    thus ?thesis by(simp add: rewrite_negated_primitives_def pext bunch_of_lemmata_about_matches)
  qed
 

  (*TODO: isar proof*)
  lemma rewrite_negated_primitives_not_has_disc:
  assumes n: "normalized_nnf_match m" and wf_disc_sel: "wf_disc_sel (disc,sel) C"
  and nodisc: "\<not> has_disc disc2 m"
  (*only need a condition for negate_f if it is actually applied*)
  and negate_f: "has_disc_negated disc False m \<Longrightarrow> \<forall>pts. \<not> has_disc disc2 (negate_f C pts)"
  and no_disc: "\<forall>a. \<not> disc2 (C a)"
  shows  "\<not> has_disc disc2 (rewrite_negated_primitives (disc,sel) C negate_f m)"
    apply(simp add: rewrite_negated_primitives_def)
    apply(case_tac "primitive_extractor (disc,sel) m", rename_tac spts rst)
    apply(simp)
    apply(frule primitive_extractor_correct(4)[OF n wf_disc_sel])
    apply(frule primitive_extractor_correct(8)[OF n wf_disc_sel])
    apply(intro conjI impI)
       using nodisc apply(simp; fail)
      apply(rule andfold_MatchExp_not_discI)
      apply(simp add: negate_f; fail)
     using andfold_MatchExp_not_disc_mapMatch no_disc apply blast
     using nodisc by blast

  lemma rewrite_negated_primitives_not_has_disc_negated:
  assumes n: "normalized_nnf_match m" and wf_disc_sel: "wf_disc_sel (disc,sel) C"
  and negate_f: "has_disc_negated disc False m \<Longrightarrow> \<forall>pts. \<not> has_disc_negated disc False (negate_f C pts)"
  shows  "\<not> has_disc_negated disc False (rewrite_negated_primitives (disc,sel) C negate_f m)"
    apply(simp add: rewrite_negated_primitives_def)
    apply(case_tac "primitive_extractor (disc,sel) m", rename_tac spts rst)
    apply(simp)
    apply(frule primitive_extractor_correct(3)[OF n wf_disc_sel])
    apply(frule primitive_extractor_correct(8)[OF n wf_disc_sel])
    apply(intro conjI impI)
       apply blast
      apply(rule andfold_MatchExp_not_disc_negatedI)
      apply(simp add: negate_f; fail)
     using andfold_MatchExp_not_disc_negated_mapMatch apply blast
    using has_disc_negated_has_disc by blast


  lemma rewrite_negated_primitives_preserves_not_has_disc_negated:
  assumes n: "normalized_nnf_match m" and wf_disc_sel: "wf_disc_sel (disc,sel) C"
  and negate_f: "has_disc_negated disc False m \<Longrightarrow> \<forall>pts. \<not> has_disc_negated disc2 False (negate_f C pts)"
  and no_disc: "\<not> has_disc_negated disc2 False m"
  shows  "\<not> has_disc_negated disc2 False (rewrite_negated_primitives (disc,sel) C negate_f m)"
    apply(simp add: rewrite_negated_primitives_def)
    apply(case_tac "primitive_extractor (disc,sel) m", rename_tac spts rst)
    apply(simp)
    apply(frule primitive_extractor_correct(3)[OF n wf_disc_sel])
    apply(frule primitive_extractor_correct(8)[OF n wf_disc_sel])
    apply(intro conjI impI)
       using no_disc apply blast
      apply(rule andfold_MatchExp_not_disc_negatedI)
      apply(simp add: negate_f; fail)
     using andfold_MatchExp_not_disc_negated_mapMatch apply blast
    apply(drule primitive_extractor_correct(6)[OF n wf_disc_sel, where neg=False])
    using no_disc by blast

  lemma rewrite_negated_primitives_normalized_preserves_unrelated_helper:
    assumes wf_disc_sel: "wf_disc_sel (disc, sel) C"
    and disc: "\<forall>a. \<not> disc2 (C a)"
    and disc_p: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated disc False m" (*either we do not disc on protocol or the is no negated port*)
    shows "normalized_nnf_match m \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
         a \<in> set (normalize_match (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m)) \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f  a"
    proof -
      have helper_a_normalized: "a \<in> MatchAnd x ` (\<Union>x\<in>set spts. MatchAnd x ` set (normalize_match rst)) \<Longrightarrow>
        normalized_n_primitive (disc, sel) f x \<Longrightarrow>
        (\<forall>s \<in> set spts. normalized_n_primitive (disc, sel) f s) \<Longrightarrow>
        normalized_n_primitive (disc, sel) f rst \<Longrightarrow>
             normalized_n_primitive (disc, sel) f a"
        for a x spts rst f disc and sel::"'a common_primitive \<Rightarrow> 'b"
        apply(subgoal_tac "\<exists> s r. a = MatchAnd x (MatchAnd s r) \<and> s \<in> set spts \<and> r \<in> set (normalize_match rst)")
         prefer 2
         apply blast
        apply(elim exE conjE, rename_tac s r)
        apply(simp)
        using normalize_match_preserves_normalized_n_primitive by blast

    show "normalized_nnf_match m \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
         a \<in> set (normalize_match (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m)) \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f  a" 
    apply(case_tac "\<not> has_disc_negated disc False m")
     subgoal
     using rewrite_negated_primitives_normalized_no_modification[OF wf_disc_sel] by blast
    apply(simp add: rewrite_negated_primitives_def)
    apply(case_tac "primitive_extractor (disc, sel) m", rename_tac spts rst)
    apply(simp)
    apply(subgoal_tac "normalized_n_primitive (disc2, sel2) f rst")
     prefer 2 subgoal for spts rst
     thm primitive_extractor_correct(5)[OF _ wf_disc_sel]
     apply(drule primitive_extractor_correct(5)[OF _ wf_disc_sel, where P="f"])
      apply blast
     by(simp)
    apply(insert disc_p, simp)
    apply(drule(1) primitive_extractor_correct(8)[OF _ wf_disc_sel])
    apply(simp)
    apply(elim bexE)
    apply(erule helper_a_normalized)
      subgoal for spts
      apply(rule_tac pts="(getNeg spts)" in negated_normalized_folded_ports_normalized_n_primitive[where C=C])
        using disc apply(simp; fail)
       using disc_p primitive_extractor_correct(8)[OF _ wf_disc_sel] apply blast
      by simp
     subgoal for x
     apply(intro ballI)
     apply(rule andfold_MatchExp_normalized_normalized_n_primitive_single[where C=C])
       using disc disc_p by(simp)+
    by blast
  qed


  definition rewrite_negated_src_ports
    :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr" where
    "rewrite_negated_src_ports m \<equiv>
          rewrite_negated_primitives (is_Src_Ports, src_ports_sel) Src_Ports l4_ports_negate_one m"

  definition rewrite_negated_dst_ports
    :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr" where
    "rewrite_negated_dst_ports m \<equiv>
          rewrite_negated_primitives (is_Dst_Ports, dst_ports_sel) Dst_Ports l4_ports_negate_one m"

  value "rewrite_negated_src_ports (MatchAnd (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                   (MatchAnd (Match (Prot (Proto TCP)))
                        (MatchNot (Match (Src_Ports (L4Ports UDP [(80,80)]))))
                 ))"
  value "rewrite_negated_src_ports (MatchAnd (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                   (MatchAnd (Match (Prot (Proto TCP)))
                        (MatchNot (Match (Extra ''foobar'')))
                 ))"

  lemma rewrite_negated_src_ports:
  assumes generic: "primitive_matcher_generic \<beta>"  and n: "normalized_nnf_match m"
  shows "matches (\<beta>, \<alpha>) (rewrite_negated_src_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
  apply(simp add: rewrite_negated_src_ports_def)
  apply(rule rewrite_negated_primitives)
    by(simp add: l4_ports_negate_one[OF generic] n wf_disc_sel_common_primitive(1))+
 
  lemma rewrite_negated_dst_ports:
  assumes generic: "primitive_matcher_generic \<beta>"  and n: "normalized_nnf_match m"
  shows "matches (\<beta>, \<alpha>) (rewrite_negated_dst_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
  apply(simp add: rewrite_negated_dst_ports_def)
  apply(rule rewrite_negated_primitives)
    by(simp add: l4_ports_negate_one[OF generic] n wf_disc_sel_common_primitive(2))+


  lemma rewrite_negated_src_ports_not_has_disc_negated:
  assumes n: "normalized_nnf_match m"
  shows  "\<not> has_disc_negated is_Src_Ports False (rewrite_negated_src_ports m)"
    apply(simp add: rewrite_negated_src_ports_def)
    apply(rule rewrite_negated_primitives_not_has_disc_negated)
      by(simp add: n wf_disc_sel_common_primitive(1) l4_ports_negate_one_not_has_disc_negated)+
    
  lemma rewrite_negated_dst_ports_not_has_disc_negated:
  assumes n: "normalized_nnf_match m"
  shows  "\<not> has_disc_negated is_Dst_Ports False (rewrite_negated_dst_ports m)"
    apply(simp add: rewrite_negated_dst_ports_def)
    apply(rule rewrite_negated_primitives_not_has_disc_negated)
      by(simp add: n wf_disc_sel_common_primitive(2) l4_ports_negate_one_not_has_disc_negated)+
    

  lemma "\<not> has_disc_negated disc t m \<Longrightarrow> \<forall>m' \<in> set (normalize_match m). \<not> has_disc_negated disc t m'"
    by(fact i_m_giving_this_a_funny_name_so_i_can_thank_my_future_me_when_sledgehammer_will_find_this_one_day)

  corollary normalize_rewrite_negated_src_ports_not_has_disc_negated:
  assumes n: "normalized_nnf_match m"
  shows "\<forall>m' \<in> set (normalize_match (rewrite_negated_src_ports m)). \<not> has_disc_negated is_Src_Ports False m'"
    apply(rule i_m_giving_this_a_funny_name_so_i_can_thank_my_future_me_when_sledgehammer_will_find_this_one_day)
    apply(rule rewrite_negated_src_ports_not_has_disc_negated)
    using n by simp



subsection\<open>Normalizing Positive Matches on Ports\<close>
(*now normalizing the match expression which does not have negated ports*)

(*creates a disjunction where all interval lists only have one element*)
  fun singletonize_L4Ports :: "ipt_l4_ports \<Rightarrow> ipt_l4_ports list" where
    "singletonize_L4Ports (L4Ports proto pts) = map (\<lambda>p. L4Ports proto [p]) pts"

  lemma singletonize_L4Ports_src: assumes generic: "primitive_matcher_generic \<beta>"
   shows "match_list (\<beta>, \<alpha>) (map (Match \<circ> Src_Ports) (singletonize_L4Ports pts)) a p \<longleftrightarrow> 
    matches (\<beta>, \<alpha>) (Match (Src_Ports pts)) a p"
    apply(cases pts)
    apply(simp add: match_list_matches primitive_matcher_generic.Ports_single[OF generic])
    apply(simp add: ports_to_set)
    by auto

  lemma singletonize_L4Ports_dst: assumes generic: "primitive_matcher_generic \<beta>"
   shows "match_list (\<beta>, \<alpha>) (map (Match \<circ> Dst_Ports) (singletonize_L4Ports pts)) a p \<longleftrightarrow> 
    matches (\<beta>, \<alpha>) (Match (Dst_Ports pts)) a p"
    apply(cases pts)
    apply(simp add: match_list_matches primitive_matcher_generic.Ports_single[OF generic])
    apply(simp add: ports_to_set)
    by auto

  lemma singletonize_L4Ports_normalized_generic:
    assumes wf_disc_sel: "wf_disc_sel (disc,sel) C"
    and "m' \<in> (\<lambda>spt. Match (C spt)) ` set (singletonize_L4Ports pt)"
    shows "normalized_n_primitive (disc, sel) (case_ipt_l4_ports (\<lambda>x pts. length pts \<le> 1))  m'"
    using assms
    apply(case_tac pt)
    apply(simp)
    apply(induction m')
        by(auto simp: wf_disc_sel.simps)

  lemma singletonize_L4Ports_normalized_src_ports:
    "m' \<in> (\<lambda>spt. Match (Src_Ports spt)) ` set (singletonize_L4Ports pt) \<Longrightarrow> normalized_src_ports m'"
    apply(simp add: normalized_src_ports_def2)
    using singletonize_L4Ports_normalized_generic[OF wf_disc_sel_common_primitive(1)] by blast

  lemma singletonize_L4Ports_normalized_dst_ports:
    "m' \<in> (\<lambda>spt. Match (Dst_Ports spt)) ` set (singletonize_L4Ports pt) \<Longrightarrow> normalized_dst_ports m'"
    apply(simp add: normalized_dst_ports_def2)
    using singletonize_L4Ports_normalized_generic[OF wf_disc_sel_common_primitive(2)] by blast

  declare singletonize_L4Ports.simps[simp del]


  lemma normalized_ports_singletonize_combine_rst:
    assumes wf_disc_sel: "wf_disc_sel (disc,sel) C"
    shows "normalized_n_primitive (disc, sel) (case_ipt_l4_ports (\<lambda>x pts. length pts \<le> 1)) rst \<Longrightarrow>
    m' \<in> (\<lambda>spt. MatchAnd (Match (C spt)) rst) ` set (singletonize_L4Ports pt) \<Longrightarrow>
    normalized_n_primitive (disc, sel) (case_ipt_l4_ports (\<lambda>x pts. length pts \<le> 1)) m'"
   apply simp
   apply(rule normalized_n_primitive_MatchAnd_combine_map)
     apply(simp_all)
   using singletonize_L4Ports_normalized_generic[OF wf_disc_sel] by fastforce


  text\<open>Normalizing match expressions such that at most one port will exist in it.
       Returns a list of match expressions (splits one firewall rule into several rules).\<close>
  definition normalize_positive_ports_step
    :: "(('i::len common_primitive \<Rightarrow> bool) \<times> ('i common_primitive \<Rightarrow> ipt_l4_ports)) \<Rightarrow> 
       (ipt_l4_ports \<Rightarrow> 'i common_primitive) \<Rightarrow>
       'i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where 
    "normalize_positive_ports_step disc_sel C m \<equiv>
        let (spts, rst) = primitive_extractor disc_sel m in
        case (getPos spts, getNeg spts)
          of (pspts, []) \<Rightarrow> (case l4_ports_compress pspts of CannotMatch \<Rightarrow> []
                                                          |  MatchesAll \<Rightarrow> [rst]
                                                          |  MatchExpr m \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match (C spt)) rst)) (singletonize_L4Ports m)
                            )
          |  (_, _) \<Rightarrow> undefined"


  lemma normalize_positive_ports_step_nnf:
    assumes n: "normalized_nnf_match m" and wf_disc_sel: "wf_disc_sel (disc,sel) C"
    and noneg: "\<not> has_disc_negated disc False m"
    shows "m' \<in> set (normalize_positive_ports_step (disc,sel) C m) \<Longrightarrow> normalized_nnf_match m'"
    apply(simp add: normalize_positive_ports_step_def)
    apply(elim exE conjE, rename_tac rst spts)
    apply(drule sym) (*switch primitive_extrartor = *)
    apply(frule primitive_extractor_correct(2)[OF n wf_disc_sel])
    apply(subgoal_tac "getNeg spts = []") (*duplication above*)
     prefer 2 subgoal
     apply(drule primitive_extractor_correct(8)[OF n wf_disc_sel])
      using noneg by simp+
    apply(simp split: match_compress.split_asm)
    by fastforce

  lemma normalize_positive_ports_step_normalized_n_primitive: 
    assumes n: "normalized_nnf_match m"  and wf_disc_sel: "wf_disc_sel (disc,sel) C"
    and noneg: "\<not> has_disc_negated disc False m"
    shows "\<forall>m' \<in> set (normalize_positive_ports_step (disc,sel) C m). 
            normalized_n_primitive (disc,sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) m'"
  unfolding normalize_positive_ports_step_def
    apply(intro ballI, rename_tac m')
    apply(simp)
    apply(elim exE conjE, rename_tac rst spts)
    apply(drule sym) (*switch primitive_extrartor = *)
    apply(frule primitive_extractor_correct(2)[OF n wf_disc_sel])
    apply(frule primitive_extractor_correct(3)[OF n wf_disc_sel])
    apply(subgoal_tac "getNeg spts = []") (*duplication above*)
     prefer 2 subgoal
     apply(drule primitive_extractor_correct(8)[OF n wf_disc_sel])
      using noneg by simp+
    apply(subgoal_tac "normalized_n_primitive (disc,sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) rst")
     prefer 2 subgoal
     by(drule(2) normalized_n_primitive_if_no_primitive)
    apply(simp split: match_compress.split_asm)
    using normalized_ports_singletonize_combine_rst[OF wf_disc_sel] by blast

  definition normalize_positive_src_ports :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_positive_src_ports = normalize_positive_ports_step (is_Src_Ports, src_ports_sel) Src_Ports"  
  definition normalize_positive_dst_ports :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_positive_dst_ports = normalize_positive_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports"

  (*TODO: into next lemmas?*)
  lemma noNeg_mapNegPos_helper: "getNeg ls = [] \<Longrightarrow>
           map (Pos \<circ> C) (getPos ls) = NegPos_map C ls"
    by(induction ls rule: getPos.induct) simp+

  lemma normalize_positive_src_ports:
    assumes generic: "primitive_matcher_generic \<beta>"
    and n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Src_Ports False m"
    shows
        "match_list (\<beta>, \<alpha>) (normalize_positive_src_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    apply(simp add: normalize_positive_src_ports_def normalize_positive_ports_step_def)
    apply(case_tac "primitive_extractor (is_Src_Ports, src_ports_sel) m", rename_tac spts rst)
    apply(simp)
    apply(subgoal_tac "getNeg spts = []") (*needs assumption for this step *)
     prefer 2 subgoal
     apply(drule primitive_extractor_correct(8)[OF n wf_disc_sel_common_primitive(1)])
      using noneg by simp+
    apply(simp)
    apply(drule primitive_extractor_correct(1)[OF n wf_disc_sel_common_primitive(1), where \<gamma>="(\<beta>, \<alpha>)" and a=a and p=p])
    apply(case_tac "l4_ports_compress (getPos spts)")
       apply(simp)
       apply(drule raw_ports_compress_src_CannotMatch[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
       apply(simp add: noNeg_mapNegPos_helper; fail)
      apply(simp)
      apply(drule raw_ports_compress_MatchesAll[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
      apply(simp add: noNeg_mapNegPos_helper; fail)
     apply(simp add: bunch_of_lemmata_about_matches)
     apply(drule raw_ports_compress_src_MatchExpr[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
     apply(insert singletonize_L4Ports_src[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
     apply(simp add: match_list_matches)
     apply(simp add: bunch_of_lemmata_about_matches)
     apply(simp add: noNeg_mapNegPos_helper; fail)
    done

  (*copy & paste, TODO generalize*)
  lemma normalize_positive_dst_ports:
    assumes generic: "primitive_matcher_generic \<beta>"
    and n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Dst_Ports False m"
    shows "match_list (\<beta>, \<alpha>) (normalize_positive_dst_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    apply(simp add: normalize_positive_dst_ports_def normalize_positive_ports_step_def)
    apply(case_tac "primitive_extractor (is_Dst_Ports, dst_ports_sel) m", rename_tac spts rst)
    apply(simp)
    apply(subgoal_tac "getNeg spts = []") (*needs assumption for this step *)
     prefer 2 subgoal
     apply(drule primitive_extractor_correct(8)[OF n wf_disc_sel_common_primitive(2)])
      using noneg by simp+
    apply(simp)
    apply(drule primitive_extractor_correct(1)[OF n wf_disc_sel_common_primitive(2), where \<gamma>="(\<beta>, \<alpha>)" and a=a and p=p])
    apply(case_tac "l4_ports_compress (getPos spts)")
       apply(simp)
       apply(drule raw_ports_compress_dst_CannotMatch[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
       apply(simp add: noNeg_mapNegPos_helper; fail)
      apply(simp)
      apply(drule raw_ports_compress_MatchesAll(2)[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
      apply(simp add: noNeg_mapNegPos_helper; fail)
     apply(simp add: bunch_of_lemmata_about_matches)
     apply(drule raw_ports_compress_dst_MatchExpr[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
     apply(insert singletonize_L4Ports_dst[OF generic, where \<alpha>=\<alpha> and a=a and p=p])
     apply(simp add: match_list_matches)
     apply(simp add: bunch_of_lemmata_about_matches)
     apply(simp add: noNeg_mapNegPos_helper; fail)
    done    

  lemma normalize_positive_src_ports_nnf:
    assumes n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Src_Ports False m"
    shows "m' \<in> set (normalize_positive_src_ports m) \<Longrightarrow> normalized_nnf_match m'"
    apply(rule normalize_positive_ports_step_nnf[OF n wf_disc_sel_common_primitive(1) noneg])
    by(simp add: normalize_positive_src_ports_def)
  lemma normalize_positive_dst_ports_nnf:
    assumes n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Dst_Ports False m"
    shows "m' \<in> set (normalize_positive_dst_ports m) \<Longrightarrow> normalized_nnf_match m'"
    apply(rule normalize_positive_ports_step_nnf[OF n wf_disc_sel_common_primitive(2) noneg])
    by(simp add: normalize_positive_dst_ports_def)


  lemma normalize_positive_src_ports_normalized_n_primitive: 
    assumes n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Src_Ports False m"
    shows "\<forall>m' \<in> set (normalize_positive_src_ports m). normalized_src_ports m'"
    unfolding normalized_src_ports_def2
    unfolding normalize_positive_src_ports_def
    using normalize_positive_ports_step_normalized_n_primitive[OF n wf_disc_sel_common_primitive(1) noneg] by blast

  lemma normalize_positive_dst_ports_normalized_n_primitive: 
    assumes n: "normalized_nnf_match m"
    and noneg: "\<not> has_disc_negated is_Dst_Ports False m"
    shows "\<forall>m' \<in> set (normalize_positive_dst_ports m). normalized_dst_ports m'"
    unfolding normalized_dst_ports_def2
    unfolding normalize_positive_dst_ports_def
    using normalize_positive_ports_step_normalized_n_primitive[OF n wf_disc_sel_common_primitive(2) noneg] by blast
   


subsection\<open>Complete Normalization\<close>


  definition normalize_ports_generic
    :: "('i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list) \<Rightarrow>
        ('i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr) \<Rightarrow>
       'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list"
  where
    "normalize_ports_generic normalize_pos rewrite_neg m = concat (map normalize_pos (normalize_match (rewrite_neg m)))"  



  lemma normalize_ports_generic_nnf:
    assumes n: "normalized_nnf_match m"
    and inset: "m' \<in> set (normalize_ports_generic normalize_pos rewrite_neg m)"
    and noNeg: "\<not> has_disc_negated disc False (rewrite_neg m)"
    and normalize_nnf_pos: "\<And>m m'.
        normalized_nnf_match  m \<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow>
          m' \<in> set (normalize_pos m) \<Longrightarrow> normalized_nnf_match m'"
    shows "normalized_nnf_match m'"
    using inset apply(simp add: normalize_ports_generic_def)
    apply(elim bexE, rename_tac a)
    apply(subgoal_tac "normalized_nnf_match a")
     prefer 2
     using normalized_nnf_match_normalize_match apply blast
    apply(erule normalize_nnf_pos, simp_all)
    apply(rule not_has_disc_normalize_match)
     using noNeg n by blast+

  lemma normalize_ports_generic:
    assumes n: "normalized_nnf_match m"
    and normalize_pos: "\<And>m. normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow>
                          match_list \<gamma> (normalize_pos m) a p \<longleftrightarrow> matches \<gamma> m a p"
    and rewrite_neg: "\<And>m. normalized_nnf_match m \<Longrightarrow>
                          matches \<gamma> (rewrite_neg m) a p = matches \<gamma> m a p"
    and noNeg: "\<And>m. normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc False (rewrite_neg m)"
    shows
        "match_list \<gamma> (normalize_ports_generic normalize_pos rewrite_neg m) a p \<longleftrightarrow> matches \<gamma> m a p"
    unfolding normalize_ports_generic_def
    proof
      have 1: "ls \<in> set (normalize_match (rewrite_neg m)) \<Longrightarrow>
          match_list \<gamma> (normalize_pos ls) a p \<Longrightarrow> normalized_nnf_match ls \<Longrightarrow> matches \<gamma> m a p"
      for ls
      apply(subst(asm) normalize_pos)
        subgoal using normalized_nnf_match_normalize_match by blast
       subgoal apply(rule_tac m="rewrite_neg m" in not_has_disc_normalize_match)
        using noNeg n apply blast
       by blast
      apply(subgoal_tac "matches \<gamma> (rewrite_neg m) a p")
       using rewrite_neg[OF n] apply blast
      using in_normalized_matches[where \<gamma>=\<gamma> and a=a and p=p] by blast

      show "match_list \<gamma> (concat (map normalize_pos (normalize_match (rewrite_neg m)))) a p \<Longrightarrow> matches \<gamma> m a p"
      apply(simp add: match_list_concat)
      apply(clarify, rename_tac ls)
      apply(subgoal_tac "normalized_nnf_match ls")
       using 1 apply(simp; fail)
      using normalized_nnf_match_normalize_match by blast
    next
      have 1: "ls \<in> set (normalize_match (rewrite_neg m)) \<Longrightarrow>
          matches \<gamma> ls a p \<Longrightarrow>
          normalized_nnf_match ls \<Longrightarrow>
          match_list \<gamma> (concat (map normalize_pos (normalize_match (rewrite_neg m)))) a p" for ls
       apply(simp add: match_list_concat)
       apply(rule_tac x=ls in bexI)
        prefer 2 apply(simp; fail)
       apply(subst normalize_pos)
         apply(simp_all)
       apply(rule_tac m="rewrite_neg m" in not_has_disc_normalize_match)
        using noNeg n apply blast
       by blast
      show "matches \<gamma> m a p \<Longrightarrow> match_list \<gamma> (concat (map normalize_pos (normalize_match (rewrite_neg m)))) a p"
       apply(subst(asm) rewrite_neg[OF n, symmetric])
       apply(subst(asm) matches_to_match_list_normalize)
       apply(subst(asm) match_list_matches)
       apply(elim bexE, rename_tac ls)
       apply(subgoal_tac "normalized_nnf_match ls")
        using 1 apply blast
       using normalized_nnf_match_normalize_match by blast
    qed


  lemma normalize_ports_generic_normalized_n_primitive:
    assumes n: "normalized_nnf_match m"  and wf_disc_sel: "wf_disc_sel (disc,sel) C"
    and noNeg: "\<And>m. normalized_nnf_match m \<Longrightarrow> \<not> has_disc_negated disc False (rewrite_neg m)"
    and normalize_nnf_pos: "\<And>m m'.
        normalized_nnf_match  m \<Longrightarrow> \<not> has_disc_negated disc False m \<Longrightarrow>
          m' \<in> set (normalize_pos m) \<Longrightarrow> normalized_nnf_match m'"
    and normalize_pos: "\<And>m m'.
        normalized_nnf_match m \<Longrightarrow>  \<not> has_disc_negated disc False m \<Longrightarrow> 
          \<forall>m'\<in>set (normalize_pos m).
                 normalized_n_primitive (disc,sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) m'"
    shows "\<forall>m' \<in> set (normalize_ports_generic normalize_pos rewrite_neg m). 
             normalized_n_primitive (disc,sel) (\<lambda>ps. case ps of L4Ports _ pts \<Rightarrow> length pts \<le> 1) m'"
  unfolding normalize_ports_generic_def
  apply(intro ballI, rename_tac m')
  apply(simp)
  apply(elim bexE, rename_tac a)
  apply(subgoal_tac "normalized_nnf_match a")
   prefer 2
   using normalized_nnf_match_normalize_match apply blast
  apply(subgoal_tac "\<not> has_disc_negated disc False a")
   prefer 2
   subgoal for ls (*TODO: same is already above!*)
    apply(rule_tac m="rewrite_neg m" in not_has_disc_normalize_match)
     using noNeg n apply blast
    by blast
  apply(subgoal_tac "normalized_nnf_match m'")
   prefer 2
   using normalize_nnf_pos apply blast
  using normalize_pos by blast

  lemma normalize_ports_generic_normalize_positive_ports_step_erule:
    assumes n: "normalized_nnf_match m"
      and wf_disc_sel: "wf_disc_sel (disc, sel) C"
      and noProt: "\<forall>a. \<not> disc (Prot a)" (*disc is src_ports or dst_ports anyway*)
      and P: "P (disc2, sel2) m"
      and P1: "\<And>a. normalized_nnf_match a \<Longrightarrow> 
                a \<in> set (normalize_match (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m)) \<Longrightarrow>
                P (disc2, sel2) a"
      and P2: "\<And>a dpts rst. normalized_nnf_match a \<Longrightarrow> 
                    primitive_extractor (disc, sel) a = (dpts, rst) \<Longrightarrow>
                    getNeg dpts = [] \<Longrightarrow> P (disc2, sel2) a \<Longrightarrow> P (disc2, sel2) rst"
      and P3: "\<And> a spt rst. P (disc2, sel2) rst \<Longrightarrow> P (disc2, sel2) (MatchAnd (Match (C spt)) rst)"
    shows "m' \<in> set (normalize_ports_generic (normalize_positive_ports_step (disc, sel) C) (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one) m) \<Longrightarrow>
          P (disc2, sel2) m'"
    using P apply(simp add: normalize_ports_generic_def)
    apply(elim bexE, rename_tac a)
    apply(subgoal_tac "normalized_nnf_match a")
     prefer 2 using normalized_nnf_match_normalize_match apply blast
    apply(simp add: normalize_positive_ports_step_def)
    apply(elim exE conjE, rename_tac rst dpts)
    apply(drule sym) (*primitive extractor*)
    apply(subgoal_tac "getNeg dpts = []")
     prefer 2 subgoal for a rst dpts
     apply(erule iffD1[OF primitive_extractor_correct(8)[OF _ wf_disc_sel]])
      apply(simp; fail)
     apply(rule not_has_disc_normalize_match)
      apply(simp_all)
     apply(rule rewrite_negated_primitives_not_has_disc_negated[OF n wf_disc_sel])
     apply(intro allI)
     apply(rule l4_ports_negate_one_not_has_disc_negated_generic)
     by(simp add: noProt)
    apply(subgoal_tac "P (disc2, sel2) a")
     prefer 2 subgoal
     apply(rule P1)
     by(simp)
    apply(frule_tac a=a in P2)
      apply blast+
    apply(simp split: match_compress.split_asm)
    using P3 by auto
  
  (*disc is is_Src_Ports or is_Dst_Ports*)
  lemma normalize_ports_generic_preserves_normalized_n_primitive:
    assumes n: "normalized_nnf_match m"
      and wf_disc_sel: "wf_disc_sel (disc, sel) C"
      and noProt: "\<forall>a. \<not> disc (Prot a)" (*disc is src_ports or dst_ports anyway*)
      and disc2_noC: "\<forall>a. \<not> disc2 (C a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated disc False m"
    shows "m' \<in> set (normalize_ports_generic (normalize_positive_ports_step (disc, sel) C) (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one) m) \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f m \<Longrightarrow>
          normalized_n_primitive (disc2, sel2) f m'"
    thm normalize_ports_generic_normalize_positive_ports_step_erule
    apply(rule normalize_ports_generic_normalize_positive_ports_step_erule[OF n wf_disc_sel noProt])
        apply(simp_all add: disc2_noC disc2_noProt)
     apply(rule rewrite_negated_primitives_normalized_preserves_unrelated_helper[OF wf_disc_sel _ _ n])
        apply(simp_all add: disc2_noC disc2_noProt)
    thm primitive_extractor_correct(5)[OF _ wf_disc_sel, where P=f]
    apply(frule_tac m=a in primitive_extractor_correct(5)[OF _ wf_disc_sel, where P=f])
     by blast+
  
  lemma normalize_ports_generic_preserves_normalized_not_has_disc:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc disc2 m"
      and wf_disc_sel: "wf_disc_sel (disc, sel) C"
      and noProt: "\<forall>a. \<not> disc (Prot a)" (*disc is src_ports or dst_ports anyway*)
      and disc2_noC: "\<forall>a. \<not> disc2 (C a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated disc False m"
     shows "m'\<in> set (normalize_ports_generic (normalize_positive_ports_step (disc, sel) C) (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one) m)
      \<Longrightarrow> \<not> has_disc disc2 m'"
    apply(rule normalize_ports_generic_normalize_positive_ports_step_erule[OF n wf_disc_sel noProt])
        apply(simp_all add: disc2_noC disc2_noProt nodisc)
     subgoal for a
     thm normalize_match_preserves_nodisc
     apply(rule_tac m="rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m" in normalize_match_preserves_nodisc)
      apply(simp_all)
     apply(insert disc2_noProt)
     apply(elim disjE)
      thm rewrite_negated_primitives_not_has_disc[of _ disc2]
      subgoal apply(rule rewrite_negated_primitives_not_has_disc[OF n wf_disc_sel nodisc _ disc2_noC])
      using l4_ports_negate_one_nodisc[OF disc2_noC] by blast
     using rewrite_negated_primitives_preserves_not_has_disc[OF n wf_disc_sel nodisc _ disc2_noC] by blast
    apply(frule_tac m=a in primitive_extractor_correct(4)[OF _ wf_disc_sel])
     by blast+

  lemma normalize_ports_generic_preserves_normalized_not_has_disc_negated:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc_negated disc2 False m"
      and wf_disc_sel: "wf_disc_sel (disc, sel) C"
      and noProt: "\<forall>a. \<not> disc (Prot a)" (*disc is src_ports or dst_ports anyway*)
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated disc False m"
     shows "m'\<in> set (normalize_ports_generic (normalize_positive_ports_step (disc, sel) C) (rewrite_negated_primitives (disc, sel) C l4_ports_negate_one) m)
      \<Longrightarrow> \<not> has_disc_negated disc2 False m'"
    apply(rule normalize_ports_generic_normalize_positive_ports_step_erule[OF n wf_disc_sel noProt])
        apply(simp_all add: disc2_noProt nodisc)
     subgoal for a
     apply(rule_tac m="rewrite_negated_primitives (disc, sel) C l4_ports_negate_one m" in not_has_disc_normalize_match)
      apply(simp_all)
     thm rewrite_negated_primitives_preserves_not_has_disc_negated[OF n wf_disc_sel ]
     apply(rule rewrite_negated_primitives_preserves_not_has_disc_negated[OF n wf_disc_sel ])
      using disc2_noProt l4_ports_negate_one_not_has_disc_negated_generic apply blast
     using nodisc by blast
    subgoal for a dpts rst
    apply(frule_tac m=a and as=dpts and ms=rst and neg=False in primitive_extractor_correct(6)[OF _ wf_disc_sel])
     by blast+
   done

  definition normalize_src_ports
    :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list"
  where
    "normalize_src_ports m = normalize_ports_generic normalize_positive_src_ports rewrite_negated_src_ports m" 

  definition normalize_dst_ports
    :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list"
  where
    "normalize_dst_ports m = normalize_ports_generic normalize_positive_dst_ports rewrite_negated_dst_ports m"

  lemma normalize_src_ports:
    assumes generic: "primitive_matcher_generic \<beta>"
    and n: "normalized_nnf_match m"
    shows "match_list (\<beta>, \<alpha>) (normalize_src_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
     apply(simp add: normalize_src_ports_def)
     apply(rule normalize_ports_generic[OF n])
       using normalize_positive_src_ports[OF generic]
             rewrite_negated_src_ports[OF generic, where \<alpha>=\<alpha> and a=a and p=p]
             rewrite_negated_src_ports_not_has_disc_negated by blast+

  lemma normalize_dst_ports:
    assumes generic: "primitive_matcher_generic \<beta>"
    and n: "normalized_nnf_match m"
    shows "match_list (\<beta>, \<alpha>) (normalize_dst_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
     apply(simp add: normalize_dst_ports_def)
     apply(rule normalize_ports_generic[OF n])
       using normalize_positive_dst_ports[OF generic]
             rewrite_negated_dst_ports[OF generic, where \<alpha>=\<alpha> and a=a and p=p]
             rewrite_negated_dst_ports_not_has_disc_negated by blast+

  lemma normalize_src_ports_normalized_n_primitive:
    assumes n:"normalized_nnf_match m"
    shows "\<forall>m' \<in> set (normalize_src_ports m). normalized_src_ports m'"
  unfolding normalize_src_ports_def normalized_src_ports_def2
  apply(rule normalize_ports_generic_normalized_n_primitive[OF n wf_disc_sel_common_primitive(1)])
    using rewrite_negated_src_ports_not_has_disc_negated apply blast
   using normalize_positive_src_ports_nnf apply blast
  unfolding normalized_src_ports_def2[symmetric]
  using normalize_positive_src_ports_normalized_n_primitive by blast

  lemma normalize_dst_ports_normalized_n_primitive:
    assumes n: "normalized_nnf_match m"
    shows "\<forall>m' \<in> set (normalize_dst_ports m). normalized_dst_ports m'"
  unfolding normalize_dst_ports_def normalized_dst_ports_def2
  apply(rule normalize_ports_generic_normalized_n_primitive[OF n wf_disc_sel_common_primitive(2)])
    using rewrite_negated_dst_ports_not_has_disc_negated apply blast
   using normalize_positive_dst_ports_nnf apply blast
  unfolding normalized_dst_ports_def2[symmetric]
  using normalize_positive_dst_ports_normalized_n_primitive by blast

  lemma normalize_src_ports_nnf:
    assumes n: "normalized_nnf_match m"
    shows "m' \<in> set (normalize_src_ports m) \<Longrightarrow> normalized_nnf_match m'"
    apply(simp add: normalize_src_ports_def)
    apply(erule normalize_ports_generic_nnf[OF n])
     using n rewrite_negated_src_ports_not_has_disc_negated apply blast
    using normalize_positive_src_ports_nnf by blast

  lemma normalize_dst_ports_nnf:
    assumes n: "normalized_nnf_match m"
    shows "m' \<in> set (normalize_dst_ports m) \<Longrightarrow> normalized_nnf_match m'"
    apply(simp add: normalize_dst_ports_def)
    apply(erule normalize_ports_generic_nnf[OF n])
     using n rewrite_negated_dst_ports_not_has_disc_negated apply blast
    using normalize_positive_dst_ports_nnf by blast


  lemma normalize_src_ports_preserves_normalized_n_primitive:
    assumes n: "normalized_nnf_match m"
      and disc2_noC: "\<forall>a. \<not> disc2 (Src_Ports a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Src_Ports False m"
    shows "m' \<in> set (normalize_src_ports m) \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f  m \<Longrightarrow>
          normalized_n_primitive (disc2, sel2) f m'"
      apply(rule normalize_ports_generic_preserves_normalized_n_primitive[OF n wf_disc_sel_common_primitive(1)])
      by(simp_all add: disc2_noC disc2_noProt normalize_src_ports_def normalize_ports_generic_def
                normalize_positive_src_ports_def rewrite_negated_src_ports_def)
  
  lemma normalize_dst_ports_preserves_normalized_n_primitive:
    assumes n: "normalized_nnf_match m"
      and disc2_noC: "\<forall>a. \<not> disc2 (Dst_Ports a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Dst_Ports False m"
    shows "m' \<in> set (normalize_dst_ports m) \<Longrightarrow>
         normalized_n_primitive (disc2, sel2) f  m \<Longrightarrow>
          normalized_n_primitive (disc2, sel2) f m'"
      apply(rule normalize_ports_generic_preserves_normalized_n_primitive[OF n wf_disc_sel_common_primitive(2)])
      by(simp_all add: disc2_noC disc2_noProt normalize_dst_ports_def normalize_ports_generic_def
                normalize_positive_dst_ports_def rewrite_negated_dst_ports_def)
  
  lemma normalize_src_ports_preserves_normalized_not_has_disc:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc disc2 m"
      and disc2_noC: "\<forall>a. \<not> disc2 (Src_Ports a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Src_Ports False m"
     shows "m'\<in> set (normalize_src_ports m)
      \<Longrightarrow> \<not> has_disc disc2 m'"
  apply(rule normalize_ports_generic_preserves_normalized_not_has_disc[OF n nodisc wf_disc_sel_common_primitive(1)])
      apply(simp add: disc2_noC disc2_noProt)+
  by (simp add: normalize_ports_generic_def normalize_positive_src_ports_def normalize_src_ports_def rewrite_negated_src_ports_def)
  
  lemma normalize_dst_ports_preserves_normalized_not_has_disc:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc disc2 m"
      and disc2_noC: "\<forall>a. \<not> disc2 (Dst_Ports a)"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Dst_Ports False m"
     shows "m'\<in> set (normalize_dst_ports m)
      \<Longrightarrow> \<not> has_disc disc2 m'"
  apply(rule normalize_ports_generic_preserves_normalized_not_has_disc[OF n nodisc wf_disc_sel_common_primitive(2)])
      apply(simp add: disc2_noC disc2_noProt)+
  by (simp add: normalize_ports_generic_def normalize_positive_dst_ports_def normalize_dst_ports_def rewrite_negated_dst_ports_def)
  
  lemma normalize_src_ports_preserves_normalized_not_has_disc_negated:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc_negated disc2 False m"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Src_Ports False m"
     shows "m'\<in> set (normalize_src_ports m)
      \<Longrightarrow> \<not> has_disc_negated disc2 False m'"
  apply(rule normalize_ports_generic_preserves_normalized_not_has_disc_negated[OF n nodisc wf_disc_sel_common_primitive(1)])
      apply(simp add: disc2_noProt)+
  by (simp add: normalize_ports_generic_def normalize_positive_src_ports_def normalize_src_ports_def rewrite_negated_src_ports_def)
  
  lemma normalize_dst_ports_preserves_normalized_not_has_disc_negated:
    assumes n: "normalized_nnf_match m" and nodisc: "\<not> has_disc_negated disc2 False m"
      and disc2_noProt: "(\<forall>a. \<not> disc2 (Prot a)) \<or> \<not> has_disc_negated is_Dst_Ports False m"
     shows "m'\<in> set (normalize_dst_ports m)
      \<Longrightarrow> \<not> has_disc_negated disc2 False m'"
  apply(rule normalize_ports_generic_preserves_normalized_not_has_disc_negated[OF n nodisc wf_disc_sel_common_primitive(2)])
      apply(simp add: disc2_noProt)+
  by (simp add: normalize_ports_generic_def normalize_positive_dst_ports_def normalize_dst_ports_def rewrite_negated_dst_ports_def)

value[code] "normalize_src_ports
                (MatchAnd (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                   (MatchAnd (Match (Prot (Proto TCP)))
                        (MatchNot (Match (Src_Ports (L4Ports UDP [(80,80)]))))
                 ))"


lemma "map opt_MatchAny_match_expr (normalize_src_ports
                (MatchAnd (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                   (MatchAnd (Match (Prot (Proto TCP)))
                        (MatchNot (Match (Src_Ports (L4Ports UDP [(80,80)]))))
                 ))) =
 [MatchAnd (MatchNot (Match (Prot (Proto UDP)))) (MatchAnd (Match (Dst (IpAddrNetmask 0x7F000000 8))) (Match (Prot (Proto TCP)))),
  MatchAnd (Match (Src_Ports (L4Ports UDP [(0, 79)]))) (MatchAnd (Match (Dst (IpAddrNetmask 0x7F000000 8))) (Match (Prot (Proto TCP)))),
  MatchAnd (Match (Src_Ports (L4Ports UDP [(81, 0xFFFF)]))) (MatchAnd (Match (Dst (IpAddrNetmask 0x7F000000 8))) (Match (Prot (Proto TCP))))]" by eval

lemma "map opt_MatchAny_match_expr (normalize_src_ports
                (MatchAnd (Match (Dst (IpAddrNetmask (ipv4addr_of_dotdecimal (127, 0, 0, 0)) 8)))
                   (MatchAnd (Match (Prot (Proto ICMP)))
                     (MatchAnd (Match (Src_Ports (L4Ports TCP [(22,22)])))
                        (MatchNot (Match (Src_Ports (L4Ports UDP [(80,80)]))))
                 ))))
 =
[MatchAnd (Match (Src_Ports (L4Ports TCP [(22, 22)])))
   (MatchAnd (MatchNot (Match (Prot (Proto UDP)))) (MatchAnd (Match (Dst (IpAddrNetmask 0x7F000000 8))) (Match (Prot (Proto ICMP)))))]" by eval


lemma "map opt_MatchAny_match_expr (normalize_src_ports
                (MatchAnd (Match ((Src_Ports (L4Ports UDP [(21,21), (22,22)])) :: 32 common_primitive))
                  (Match (Prot (Proto UDP)))))
  =
[MatchAnd (Match (Src_Ports (L4Ports UDP [(21, 22)]))) (Match (Prot (Proto UDP)))]" by eval


lemma "normalize_match (andfold_MatchExp (map (l4_ports_negate_one C) [])) = [MatchAny]" by(simp)


end
