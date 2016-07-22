theory Ports_Normalize
imports Common_Primitive_Lemmas
begin


 definition singletonize_L4Ports :: "primitive_protocol \<Rightarrow> raw_ports \<Rightarrow> ipt_l4_ports list" where
    "singletonize_L4Ports proto pts \<equiv> map (\<lambda>p. L4Ports proto [p]) pts"

  lemma singletonize_L4Ports: assumes generic: "primitive_matcher_generic \<beta>"
   shows "match_list (\<beta>, \<alpha>) (map (Match \<circ> Src_Ports) (singletonize_L4Ports proto pts)) a p \<longleftrightarrow> 
    matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto pts))) a p"
    apply(simp add: singletonize_L4Ports_def)
    apply(induction pts)
     apply(simp add: bunch_of_lemmata_about_matches primitive_matcher_generic.Ports_single[OF generic]; fail)
    apply(simp add: match_list_matches bunch_of_lemmata_about_matches primitive_matcher_generic.Ports_single[OF generic])
    by auto


(*just another attempt, same stuff below*)
  fun l4_src_ports_normalize_negate :: "ipt_l4_ports \<Rightarrow> (('i::len common_primitive) match_expr \<times> ipt_l4_ports list)" where
    "l4_src_ports_normalize_negate (L4Ports proto pts) =
          (
            MatchNot (Match (Prot (Proto proto))),
            (singletonize_L4Ports proto (raw_ports_invert pts))
          )"


  lemma l4_src_ports_normalize_negate:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
      and sports: "(protocol, ports) = (l4_src_ports_normalize_negate src_ports)"
  shows "match_list (\<beta>, \<alpha>) (map (Match \<circ> Src_Ports) ports) a p \<or> matches (\<beta>, \<alpha>) protocol a p \<longleftrightarrow>
          matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports src_ports))) a p"
    (*apply(simp add: match_list_matches)*)
    apply(cases src_ports, rename_tac proto pts)
    apply(simp)
    apply(insert sports)
    apply(simp)
    apply(subst singletonize_L4Ports[OF generic])
    apply(simp add: bunch_of_lemmata_about_matches primitive_matcher_generic.Prot_single_not[OF generic] primitive_matcher_generic.Ports_single[OF generic])
    apply(simp add: primitive_matcher_generic.Ports_single_not[OF generic])
    apply(simp add: raw_ports_invert)
    by blast


(*TODO: move oder ich hab das schon irgendwo*)
(*
fun andfold_MatchExp :: "'a list \<Rightarrow> 'a match_expr" where
  "andfold_MatchExp [] = MatchAny" |
  "andfold_MatchExp (e#es) = MatchAnd (Match e) (andfold_MatchExp es)"

(*TODO: this must be somewhere, deduplicate! look for fold and MatchAnd*)
lemma andfold_MatchExp_alist_and: "alist_and (map Pos ls) = andfold_MatchExp ls"
  apply(induction ls)
   apply(simp)+
  done
*)

fun andfold_MatchExp :: "'a match_expr list \<Rightarrow> 'a match_expr" where
  "andfold_MatchExp [] = MatchAny" |
  "andfold_MatchExp (e#es) = MatchAnd e (andfold_MatchExp es)"

(*TODO: this must be somewhere, deduplicate! look for fold and MatchAnd*)
lemma andfold_MatchExp_alist_and: "alist_and (map Pos ls) = andfold_MatchExp (map Match ls)"
  apply(induction ls)
   apply(simp)+
  done

lemma andfold_MatchExp_matches: "matches (\<beta>, \<alpha>) (andfold_MatchExp ms) a p \<longleftrightarrow> (\<forall>m \<in> set ms. matches (\<beta>, \<alpha>) m a p)"
  apply(induction ms)
   apply(simp add: bunch_of_lemmata_about_matches)+
  done

lemma andfold_MatchExp_not_disc_negated_mapMatch:
  "\<not> has_disc_negated disc False (andfold_MatchExp (map (Match \<circ> C) ls))"
  by(induction ls)(simp)+


lemma andfold_MatchExp_not_disc_negatedI:
  "\<forall>m \<in> set ms. \<not> has_disc_negated disc False m \<Longrightarrow> \<not> has_disc_negated disc False (andfold_MatchExp ms)"
  apply(induction ms)
   apply(simp)+
  done

subsection\<open>Normalizing ports\<close>

  (*TODO: new*)
context
begin
(*TODO: probably return just one match expression? rely on nnf normalization later*)
  (*
  fun l4_src_ports_negate_one :: "ipt_l4_ports \<Rightarrow> ('i::len common_primitive) match_expr list" where
    "l4_src_ports_negate_one (L4Ports proto pts) =
          [ MatchNot (Match (Prot (Proto proto))),
            Match (Src_Ports (L4Ports proto (raw_ports_invert pts)))]"
  

  lemma l4_src_ports_negate_one:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports src_ports))) a p \<longleftrightarrow> 
         match_list (\<beta>, \<alpha>) (l4_src_ports_negate_one src_ports) a p"
    apply(cases src_ports, rename_tac proto pts)
    apply(simp add: primitive_matcher_generic.Ports_single_not[OF generic])
    apply(simp add: bunch_of_lemmata_about_matches primitive_matcher_generic.Prot_single_not[OF generic] primitive_matcher_generic.Ports_single[OF generic])
    by(simp add: raw_ports_invert)

  declare l4_src_ports_negate_one.simps[simp del]*)

(*version two: only one match_expr not normalized returned*)
  fun l4_src_ports_negate_one :: "ipt_l4_ports \<Rightarrow> ('i::len common_primitive) match_expr" where
    "l4_src_ports_negate_one (L4Ports proto pts) = MatchOr
           (MatchNot (Match (Prot (Proto proto))))
            (Match (Src_Ports (L4Ports proto (raw_ports_invert pts))))"


  lemma l4_src_ports_negate_one:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (l4_src_ports_negate_one src_ports) a p \<longleftrightarrow>
          matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports src_ports))) a p"
    apply(cases src_ports, rename_tac proto pts)
    apply(simp add: primitive_matcher_generic.Ports_single_not[OF generic])
    apply(simp add: MatchOr bunch_of_lemmata_about_matches primitive_matcher_generic.Prot_single_not[OF generic] primitive_matcher_generic.Ports_single[OF generic])
    apply(simp add: raw_ports_invert)
    by blast

  lemma l4_src_ports_negate_one_not_has_disc_negated:
    "\<not> has_disc_negated is_Src_Ports False (l4_src_ports_negate_one src_ports)"
    apply(cases src_ports, rename_tac proto pts)
    by(simp add: MatchOr_def)
    

  text\<open>beware, the result is not nnf normalized!\<close>
  lemma "\<not> normalized_nnf_match (l4_src_ports_negate_one src_ports)"
    by(cases src_ports) (simp add: MatchOr_def)
  
  declare l4_src_ports_negate_one.simps[simp del]

  definition singletonize_L4Ports :: "primitive_protocol \<Rightarrow> raw_ports \<Rightarrow> ipt_l4_ports list" where
    "singletonize_L4Ports proto pts \<equiv> map (\<lambda>p. L4Ports proto [p]) pts"

  (*Probably tune as follows:*)
  lemma  assumes generic: "primitive_matcher_generic \<beta>"
   shows "matches (\<beta>, \<alpha>) (andfold_MatchExp (map (Match \<circ> Src_Ports) (singletonize_L4Ports proto pts))) a p \<longleftrightarrow> 
    matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto pts))) a p"
    apply(simp add: singletonize_L4Ports_def)
    apply(induction pts)
     apply(simp add: bunch_of_lemmata_about_matches primitive_matcher_generic.Ports_single[OF generic])
    oops
    (*TODO: yeah, need a big MatchOr or return a list or do the whole thing with normalize_primitive_extract
      probably not using MatchOr but returning a list directly will give better code

     \<And>  \<And> \<And> even better: generalize normalize_primitive_extract that it takes a function which returns a tuple:
      a match expression (here, the match on the protocol) and a common primitive list (the normalized ports)

     does:
      map (MatchAnd rest)  ([first_thing]@(map (\<lambda>port. (Match (Src_Ports port))))

      returns a 'a match_expr list just like normalize_primitive_extract

     call it normalize_primitive_extract_aux (normalize_primitive_extract with an auxilliary match expression)

    bonus: the things are probably all in NNF form and we don't  need to expand MatchOr in code!
      and we can hopefully get rid of the andfold_MatchExp
    *)

  (*TODO move as internal to next proof*)
  lemma spts: 
    "(\<forall>m\<in>set (getNeg spts). matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports m))) a p) \<and> (\<forall>m\<in>set (getPos spts). matches (\<beta>, \<alpha>) (Match (Src_Ports m)) a p)
      \<longleftrightarrow>
      matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports spts)) a p"
    apply(induction spts rule: alist_and.induct)
      apply(simp add: bunch_of_lemmata_about_matches; fail)
     by(auto simp add: bunch_of_lemmata_about_matches)


  (*TODO: write primitive_extractor with "let" instead of "case" more often?*)
  definition rewrite_negated_src_ports :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr" where
    "rewrite_negated_src_ports m \<equiv>
        let (spts, rst) = primitive_extractor (is_Src_Ports, src_ports_sel) m
        in MatchAnd
            (andfold_MatchExp (map l4_src_ports_negate_one (getNeg spts)))
            (MatchAnd (andfold_MatchExp (map (Match \<circ> Src_Ports) (getPos spts))) rst)"
  
  lemma
  assumes generic: "primitive_matcher_generic \<beta>"  and n: "normalized_nnf_match m"
  shows "matches (\<beta>, \<alpha>) m a p \<longleftrightarrow> matches (\<beta>, \<alpha>) (rewrite_negated_src_ports m) a p"
  apply(simp add: rewrite_negated_src_ports_def)
  apply(case_tac "primitive_extractor (is_Src_Ports, src_ports_sel) m", rename_tac spts rst)
  apply(simp)
  apply(simp add: bunch_of_lemmata_about_matches)
  apply(subst primitive_extractor_correct(1)[OF n wf_disc_sel_common_primitive(1), where \<gamma>="(\<beta>, \<alpha>)" and a=a and p=p, symmetric])
   apply(simp; fail)
  apply(simp add: andfold_MatchExp_matches)
  apply(simp add: l4_src_ports_negate_one[OF generic])
  apply(subgoal_tac "matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports spts)) a p \<longleftrightarrow>
          (\<forall>m\<in>set (getNeg spts). matches (\<beta>, \<alpha>) (MatchNot (Match (Src_Ports m))) a p) \<and> (\<forall>m\<in>set (getPos spts). matches (\<beta>, \<alpha>) (Match (Src_Ports m)) a p)")
   apply(simp; fail)
  apply(simp add: spts)
  done


  lemma rewrite_negated_src_ports_not_has_disc_negated:
  assumes n: "normalized_nnf_match m"
  shows  "\<not> has_disc_negated is_Src_Ports False (rewrite_negated_src_ports m)"
    apply(simp add: rewrite_negated_src_ports_def)
    apply(case_tac "primitive_extractor (is_Src_Ports, src_ports_sel) m", rename_tac spts rst)
    apply(simp)
    apply(frule primitive_extractor_correct(3)[OF n wf_disc_sel_common_primitive(1)])
    apply(intro conjI)
      apply(rule andfold_MatchExp_not_disc_negatedI)
      apply(simp add: l4_src_ports_negate_one_not_has_disc_negated; fail)
     using andfold_MatchExp_not_disc_negated_mapMatch apply blast
    using has_disc_negated_has_disc by blast
    
end

(*Old stuff from here*)

context
begin

  private fun raw_ports_negation_type_normalize :: "raw_ports negation_type \<Rightarrow> raw_ports" where
    "raw_ports_negation_type_normalize (Pos ps) = ps" |
    "raw_ports_negation_type_normalize (Neg ps) = raw_ports_invert ps"  
  
  
  private lemma "raw_ports_negation_type_normalize (Neg [(0,65535)]) = []" by eval

  declare raw_ports_negation_type_normalize.simps[simp del]
  
  (*
  private lemma raw_ports_negation_type_normalize_correct:
        "primitive_matcher_generic \<beta> \<Longrightarrow> 
         matches (\<beta>, \<alpha>) (negation_type_to_match_expr_f (Src_Ports) ps) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Src_Ports (raw_ports_negation_type_normalize ps))) a p"
        "primitive_matcher_generic \<beta> \<Longrightarrow> 
         matches (\<beta>, \<alpha>) (negation_type_to_match_expr_f (Dst_Ports) ps) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Dst_Ports (raw_ports_negation_type_normalize ps))) a p"
  apply(case_tac [!] ps)
  apply(simp_all add: primitive_matcher_generic.Ports_single primitive_matcher_generic.Ports_single_not)
  apply(simp_all add: raw_ports_negation_type_normalize.simps raw_ports_invert split: ternaryvalue.split)
  done
  *)
  
  (* [ [(1,2) \<or> (3,4)]  \<and>  [] ]*)
  text\<open>@{typ "raw_ports list \<Rightarrow> raw_ports"}\<close>
  private definition raw_ports_andlist_compress :: "('a::len word \<times> 'a::len word) list list \<Rightarrow> ('a::len word \<times> 'a::len word) list" where
    "raw_ports_andlist_compress pss = wi2l (fold (\<lambda>ps accu. (wordinterval_intersection (l2wi ps) accu)) pss wordinterval_UNIV)"
  
  private lemma raw_ports_andlist_compress_correct: "ports_to_set (raw_ports_andlist_compress pss) = \<Inter> set (map ports_to_set pss)"
    proof -
      { fix accu
        have "ports_to_set (wi2l (fold (\<lambda>ps accu. (wordinterval_intersection (l2wi ps) accu)) pss accu)) = (\<Inter> set (map ports_to_set pss)) \<inter> (ports_to_set (wi2l accu))"
          apply(induction pss arbitrary: accu)
           apply(simp_all add: ports_to_set_wordinterval l2wi_wi2l)
          by fast
      }
      from this[of wordinterval_UNIV] show ?thesis
        unfolding raw_ports_andlist_compress_def by(simp add: ports_to_set_wordinterval l2wi_wi2l)
    qed
  
  
  definition raw_ports_compress :: "raw_ports negation_type list \<Rightarrow> raw_ports" where
    "raw_ports_compress pss = raw_ports_andlist_compress (map raw_ports_negation_type_normalize pss)"

  (*
  definition l4_ports_compress :: "ipt_l4_ports negation_type list \<Rightarrow> ipt_l4_ports" where
    "l4_ports_compress pss = raw_ports_andlist_compress (map raw_ports_negation_type_normalize pss)"
  *)
  
  (*only for src*)
  private lemma raw_ports_compress_src_correct:
  fixes p :: "('i::len, 'a) tagged_packet_scheme"
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports ms)) a p \<longleftrightarrow> 
         matches (\<beta>, \<alpha>) (Match (Src_Ports (L4Ports proto (raw_ports_compress ms)))) a p"
  proof(induction ms)
    case Nil with generic show ?case
      unfolding primitive_matcher_generic.Ports_single[OF generic]
      by(simp add: raw_ports_compress_def bunch_of_lemmata_about_matches raw_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case
      proof(cases m)
        case Pos thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic]
          by(simp add: raw_ports_compress_def raw_ports_andlist_compress_correct bunch_of_lemmata_about_matches
                raw_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?thesis using Cons.IH generic primitive_matcher_generic.Ports_single_not[where p = p] primitive_matcher_generic.Ports_single[where p = p]
          apply(simp add: raw_ports_compress_def raw_ports_andlist_compress_correct
                          bunch_of_lemmata_about_matches[where p = p])
          apply(simp add: raw_ports_invert raw_ports_negation_type_normalize.simps)
          done
        qed
  qed
  (*only for dst*)
  private lemma raw_ports_compress_dst_correct:
  assumes generic: "primitive_matcher_generic \<beta>"
  shows "matches (\<beta>, \<alpha>) (alist_and (NegPos_map Dst_Ports ms)) a p \<longleftrightarrow>
         matches (\<beta>, \<alpha>) (Match (Dst_Ports (raw_ports_compress ms))) a p"
  proof(induction ms)
    case Nil thus ?case
      unfolding primitive_matcher_generic.Ports_single[OF generic]
      by(simp add: raw_ports_compress_def bunch_of_lemmata_about_matches raw_ports_andlist_compress_correct)
    next
    case (Cons m ms)
      thus ?case
      proof(cases m)
        case Pos thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic]
          by(simp add: raw_ports_compress_def raw_ports_andlist_compress_correct bunch_of_lemmata_about_matches
                raw_ports_negation_type_normalize.simps)
        next
        case (Neg a)
          thus ?thesis using Cons.IH primitive_matcher_generic.Ports_single[OF generic] primitive_matcher_generic.Ports_single_not[OF generic]
          apply(simp add: raw_ports_compress_def raw_ports_andlist_compress_correct
                          bunch_of_lemmata_about_matches)
          apply(simp add: raw_ports_invert raw_ports_negation_type_normalize.simps)
          done
        qed
  qed
  
  (*
  private lemma raw_ports_compress_matches_set: "primitive_matcher_generic \<beta> \<Longrightarrow>
         matches (\<beta>, \<alpha>) (Match (Src_Ports (raw_ports_compress ips))) a p \<longleftrightarrow>
         p_sport p \<in> \<Inter> set (map (ports_to_set \<circ> raw_ports_negation_type_normalize) ips)"
  apply(simp add: raw_ports_compress_def)
  apply(induction ips)
   apply(simp)
   apply(simp add: raw_ports_compress_def bunch_of_lemmata_about_matches
                   raw_ports_andlist_compress_correct primitive_matcher_generic_def; fail)
  apply(rename_tac m ms)
  apply(case_tac m)
   apply(simp add: primitive_matcher_generic.Ports_single raw_ports_andlist_compress_correct; fail)
  apply(simp add: primitive_matcher_generic.Ports_single raw_ports_andlist_compress_correct; fail)
  done
  *)
  (*
  (*spliting the primitives: multiport list (a list of disjunction!)*)
  private lemma singletonize_SrcDst_Ports:
      "(*primitive_matcher_generic \<beta> \<Longrightarrow>  multiports_disjuction TODO *)
       match_list (common_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Src_Ports [spt]))) ms) (spts)) a p \<longleftrightarrow>
       matches (common_matcher, \<alpha>) (MatchAnd (Match (Src_Ports spts)) ms) a p"
      "match_list (common_matcher, \<alpha>) (map (\<lambda>spt. (MatchAnd (Match (Dst_Ports [spt]))) ms) (dpts)) a p \<longleftrightarrow>
       matches (common_matcher, \<alpha>) (MatchAnd (Match (Dst_Ports dpts)) ms) a p"
    apply(simp_all add: match_list_matches bunch_of_lemmata_about_matches(1) multiports_disjuction)
  done
  *)
  
  
  (*idea:*)
  value "case primitive_extractor (is_Src_Ports, src_ports_sel) m 
          of (spts, rst) \<Rightarrow> map (\<lambda>spt. (MatchAnd (Match ((Src_Ports [spt]) :: 32 common_primitive))) rst) (raw_ports_compress spts)"
  
  
  text\<open>Normalizing match expressions such that at most one port will exist in it. Returns a list of match expressions (splits one firewall rule into several rules).\<close>
  definition normalize_ports_step :: "(('i::len common_primitive \<Rightarrow> bool) \<times> ('i common_primitive \<Rightarrow> raw_ports)) \<Rightarrow> 
                               (raw_ports \<Rightarrow> 'i common_primitive) \<Rightarrow>
                               'i common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where 
    "normalize_ports_step (disc_sel) C = normalize_primitive_extract disc_sel C (\<lambda>me. map (\<lambda>pt. [pt]) (raw_ports_compress me))"

  definition normalize_src_ports :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_src_ports = normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports"  
  definition normalize_dst_ports :: "'i::len common_primitive match_expr \<Rightarrow> 'i common_primitive match_expr list" where
    "normalize_dst_ports = normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports"

  lemma normalize_src_ports: assumes generic: "primitive_matcher_generic \<beta>" and n: "normalized_nnf_match m" shows
        "match_list (\<beta>, \<alpha>) (normalize_src_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    proof -
      { fix ml
        have "match_list (\<beta>, \<alpha>) (map (Match \<circ> Src_Ports) (map (\<lambda>pt. [pt]) (raw_ports_compress ml))) a p =
         matches (\<beta>, \<alpha>) (alist_and (NegPos_map Src_Ports ml)) a p"
         using raw_ports_compress_src_correct[OF generic] primitive_matcher_generic.multiports_disjuction[OF generic]
         by(simp add: match_list_matches)
      } with normalize_primitive_extract[OF n wf_disc_sel_common_primitive(1), where \<gamma>="(\<beta>, \<alpha>)"]
      show ?thesis
        unfolding normalize_src_ports_def normalize_ports_step_def by simp
    qed

    lemma normalize_dst_ports: assumes generic: "primitive_matcher_generic \<beta>" and n: "normalized_nnf_match m" shows
        "match_list (\<beta>, \<alpha>) (normalize_dst_ports m) a p \<longleftrightarrow> matches (\<beta>, \<alpha>) m a p"
    proof -
      { fix ml
        have "match_list (\<beta>, \<alpha>) (map (Match \<circ> Dst_Ports) (map (\<lambda>pt. [pt]) (raw_ports_compress ml))) a p =
         matches (\<beta>, \<alpha>) (alist_and (NegPos_map Dst_Ports ml)) a p"
         using raw_ports_compress_dst_correct[OF generic] primitive_matcher_generic.multiports_disjuction[OF generic]
         by(simp add: match_list_matches)
      } with normalize_primitive_extract[OF n wf_disc_sel_common_primitive(2), where \<gamma>="(\<beta>, \<alpha>)"]
      show ?thesis
        unfolding normalize_dst_ports_def normalize_ports_step_def by simp
    qed


  value "normalized_nnf_match (MatchAnd (MatchNot (Match (Src_Ports [(1,2)]))) (Match (Src_Ports [(1,2)])))"
  value "normalize_src_ports (MatchAnd (MatchNot (Match (Src_Ports [(5,9)]))) (Match (Src_Ports [(1,2)])))"

  (*probably we should optimize away the (Match (Src_Ports [(0, 65535)]))*)
  value "normalize_src_ports (MatchAnd (MatchNot (Match (Prot (Proto TCP)))) (Match (Prot (ProtoAny))))"
  
  fun normalized_src_ports :: "'i::len common_primitive match_expr \<Rightarrow> bool" where
    "normalized_src_ports MatchAny = True" |
    "normalized_src_ports (Match (Src_Ports [])) = True" |
    "normalized_src_ports (Match (Src_Ports [_])) = True" |
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
    "normalized_dst_ports (Match (Dst_Ports [])) = True" |
    "normalized_dst_ports (Match (Dst_Ports [_])) = True" |
    "normalized_dst_ports (Match (Dst_Ports _)) = False" |
    "normalized_dst_ports (Match _) = True" |
    "normalized_dst_ports (MatchNot (Match (Dst_Ports _))) = False" |
    "normalized_dst_ports (MatchNot (Match _)) = True" |
    "normalized_dst_ports (MatchAnd m1 m2) = (normalized_dst_ports m1 \<and> normalized_dst_ports m2)" |
    "normalized_dst_ports (MatchNot (MatchAnd _ _)) = False" |
    "normalized_dst_ports (MatchNot (MatchNot _)) = False" |
    "normalized_dst_ports (MatchNot MatchAny) = True" 

  lemma normalized_src_ports_def2: "normalized_src_ports ms = normalized_n_primitive (is_Src_Ports, src_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_src_ports.induct, simp_all)
  lemma normalized_dst_ports_def2: "normalized_dst_ports ms = normalized_n_primitive (is_Dst_Ports, dst_ports_sel) (\<lambda>pts. length pts \<le> 1) ms"
    by(induction ms rule: normalized_dst_ports.induct, simp_all)
  
  
  private lemma "\<forall>spt \<in> set (raw_ports_compress spts). normalized_src_ports (Match (Src_Ports [spt]))" by(simp)
  

  lemma normalize_src_ports_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_src_ports m). normalized_src_ports m'"
  unfolding normalize_src_ports_def normalize_ports_step_def
  unfolding normalized_src_ports_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(1)])
   by(simp_all)


  lemma "normalized_nnf_match m \<Longrightarrow>
      \<forall>m' \<in> set (normalize_src_ports m). normalized_src_ports m' \<and> normalized_nnf_match m'"
  apply(intro ballI, rename_tac mn)
  apply(rule conjI)
   apply(simp add: normalize_src_ports_normalized_n_primitive)
  unfolding normalize_src_ports_def normalize_ports_step_def
  unfolding normalized_dst_ports_def2
   by(auto dest: normalize_primitive_extract_preserves_nnf_normalized[OF _ wf_disc_sel_common_primitive(1)])

  lemma normalize_dst_ports_normalized_n_primitive: "normalized_nnf_match m \<Longrightarrow> 
      \<forall>m' \<in> set (normalize_dst_ports m). normalized_dst_ports m'"
  unfolding normalize_dst_ports_def normalize_ports_step_def
  unfolding normalized_dst_ports_def2
  apply(rule normalize_primitive_extract_normalizes_n_primitive[OF _ wf_disc_sel_common_primitive(2)])
   by(simp_all)

  (*using the generalized version, we can push through normalized conditions*)
  lemma "normalized_nnf_match m \<Longrightarrow> normalized_dst_ports m \<Longrightarrow>
    \<forall>mn \<in> set (normalize_src_ports m). normalized_dst_ports mn"
  unfolding normalized_dst_ports_def2 normalize_src_ports_def normalize_ports_step_def
  apply(frule(1) normalize_primitive_extract_preserves_unrelated_normalized_n_primitive[OF _ _ wf_disc_sel_common_primitive(1), where f="(\<lambda>me. map (\<lambda>pt. [pt]) (raw_ports_compress me))"])
   apply(simp_all)
  done

end
end
