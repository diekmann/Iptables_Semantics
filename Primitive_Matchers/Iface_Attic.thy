theory Iface_Attic
imports String "../Output_Format/Negation_Type"
begin



  (*we might need this in the following lemma*)
  lemma xxx: "(\<lambda>s. i@s) ` (UNIV::string set) = {i@cs | cs. True}"
    by auto
  lemma xxx2: "{s@cs | s cs. P s} = (\<Union> s \<in> {s | s. P s}. (\<lambda>cs. s@cs) ` (UNIV::string set))"
    by auto
  lemma xxx3: "length i = n \<Longrightarrow> {s@cs | s cs. length s = n \<and> s \<noteq> (i::string)} = {s@cs | s cs. length s = n} - {s@cs | s cs. s = i}"
    thm xxx2[of "\<lambda>s::string. length s = n \<and> s \<noteq> i"]
    by auto
  (*also works with i - 1*)
  lemma xxx3': "n\<le>length i \<Longrightarrow> {s @ cs |s cs. length s = n \<and> s \<noteq> take n (i::string)} = {s@cs | s cs. length s = n} - {s@cs | s cs. s = take n i}"
    apply(subst xxx3)
     apply(simp)
    by blast

  lemma "- range (op @ (butlast i)) = UNIV - (op @ (butlast i)) ` UNIV"
  by fast

  lemma notprefix: "c \<noteq> take (length c) i \<longleftrightarrow> (\<forall>cs. c@cs \<noteq> i)"
    apply(safe)
    apply(simp)
    by (metis append_take_drop_id)

  definition common_prefix :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "common_prefix i c \<equiv> take (min (length c) (length i)) c = take (min (length c) (length i)) i"
  lemma common_prefix_alt: "common_prefix i c \<longleftrightarrow> (\<exists>cs1 cs2. i@cs1 = c@cs2)"
    unfolding common_prefix_def
    apply(safe)
     apply (metis append_take_drop_id min_def order_refl take_all)
    by (metis min.commute notprefix order_refl take_all take_take)
  lemma no_common_prefix: "\<not> common_prefix i c \<longleftrightarrow> (\<forall>cs1 cs2. i@cs1 \<noteq> c@cs2)"
    using common_prefix_alt by presburger
  lemma common_prefix_commute: "common_prefix a b \<longleftrightarrow> common_prefix b a"
    unfolding common_prefix_alt by metis
  lemma common_prefix_append_longer: "length c \<ge> length i \<Longrightarrow> common_prefix i c \<longleftrightarrow> common_prefix i (c@cs)"
    by(simp add: common_prefix_def min_def)

  lemma xxxxx: "length c \<ge> length i \<Longrightarrow> (\<forall>csa. (i::string) @ csa \<noteq> c @ cs) \<longleftrightarrow> \<not> common_prefix i c"
    apply(rule)
     prefer 2
     apply (simp add: no_common_prefix)
    apply(subst(asm) notprefix[symmetric])
    apply(cases "(length c) > (length i)")
     apply(simp add: min_def common_prefix_def)
    apply(simp add: min_def common_prefix_def)
    done

  lemma no_prefix_set_split: "{c@cs | c cs. \<not> common_prefix (i::string) c} = 
          {c@cs | c cs. length c \<ge> length i \<and> take (length i) (c@cs) \<noteq> i} \<union>
          {c@cs | c cs. length c \<le> length i \<and> take (length c) i \<noteq> c}" (is "?A = ?B1 \<union> ?B2")
    proof -
      have srule: "\<And> P Q. P = Q \<Longrightarrow> {c @ cs |c cs. P c cs} = {c @ cs |c cs. Q c cs}" by simp

      have a: "?A = {c@cs |c cs. (\<forall>cs1 cs2. i@cs1 \<noteq> c@cs2)}"
        using no_common_prefix by presburger

      have b1: "?B1 = {c@cs | c cs. length c \<ge> length i \<and>  \<not> common_prefix i c}"
        by (metis (full_types) notprefix xxxxx)
      have b2: "?B2 = {c@cs | c cs. length c \<le> length i \<and>  \<not> common_prefix i c}"
        apply(rule srule)
        apply(simp add: fun_eq_iff)
        apply(intro allI iffI)
         apply(simp_all)
         apply(elim conjE)
         apply(subst(asm) neq_commute)
         apply(subst(asm) notprefix)
         apply(drule xxxxx[where cs="[]"])
         apply(simp add: common_prefix_commute)
        apply(elim conjE)
        apply(subst neq_commute)
        apply(subst notprefix)
        apply(drule xxxxx[where cs="[]"])
        apply(simp add: common_prefix_commute)
        done

      have "?A \<subseteq> ?B1 \<union> ?B2" 
        apply(subst b1)
        apply(subst b2)
        apply(rule)
        apply(simp)
        apply(elim exE conjE)
        apply(case_tac "length x \<le> length i")
         apply(auto)[1]
        by (metis nat_le_linear)
      have "?B1 \<union> ?B2 \<subseteq> ?A"
        apply(subst b1)
        apply(subst b2)
        by blast
      from `?A \<subseteq> ?B1 \<union> ?B2` `?B1 \<union> ?B2 \<subseteq> ?A` show ?thesis by blast
    qed

  lemma other_char: "a \<noteq> (char_of_nat (Suc (nat_of_char a)))"
    apply(cases a)
    apply(simp add: nat_of_char_def char_of_nat_def)
    oops (*should hold but not needed now*)


  thm Set.full_SetCompr_eq
  lemma "\<not> (range f) = {u. \<forall>x. u \<noteq> f x}" by blast
  lemma all_empty_string_False: "(\<forall>cs::string. cs \<noteq> []) \<longleftrightarrow> False" by simp


  text{*some @{term common_prefix} sets*}
  lemma "{c | c. common_prefix i c} \<subseteq> {c@cs| c cs. common_prefix i c}"
    apply(safe)
    apply(simp add: common_prefix_alt)
    apply (metis append_Nil)
    done
  lemma "{c@cs| c cs. length i \<le> length c \<and> common_prefix i c} \<subseteq> {c | c. common_prefix i c}"
    apply(safe)
    apply(rule_tac x="c@cs" in exI)
    apply(simp)
    apply(subst common_prefix_append_longer[symmetric])
    apply(simp_all)
    done
  lemma "{c | c. common_prefix i c} \<subseteq> {c@cs| c cs. length i \<ge> length c \<and> common_prefix i c}"
    apply(safe)
    apply(subst(asm) common_prefix_def)
    apply(case_tac "length c \<le> length i")
     apply(simp_all add: min_def split: split_if_asm)
     apply(rule_tac x=c in exI)
     apply(simp)
     apply(simp add: common_prefix_def min_def)
    apply(rule_tac x="take (length i) c" in exI)
    apply(simp)
    apply(simp add: common_prefix_def min_def)
    by (metis notprefix)


  lemma "- {c | c . \<not> common_prefix i c} = {c | c. common_prefix i c}"
    apply(safe)
    apply(simp add: common_prefix_alt)
    done
  lemma inv_neg_commonprefixset:"- {c@cs| c cs. \<not> common_prefix i c} = {c | c. common_prefix i c}"
    apply(safe)
     apply blast
    apply(simp add: common_prefix_alt)
    done
  lemma "- {c@cs | c cs. length c \<le> length i \<and> \<not> common_prefix i c} \<subseteq> {i@cs | cs. True}"
    apply(safe)
    apply(subst(asm) common_prefix_def)
    apply(simp add: min_def)
    oops

  (*TODO: what is this set: {c@cs | c cs. \<not> common_prefix i c} \<union> \<dots>?
    test: {c | c. length c < length i} \<union> {c@cs | c cs. length c = length i \<and> c \<noteq> i}*)
  (*TODO: see version below!*)
  lemma "- {i@cs | cs. True} = {c@cs | c cs. \<not> common_prefix i c} \<union> {c | c. length c < length i}"
    apply(rule)
     prefer 2
     apply(safe)[1]
     apply(simp add: no_common_prefix)
     apply(simp add: no_common_prefix)
    apply(simp)
    thm Compl_anti_mono[where B="{i @ cs |cs. True}" and A="- {c @ cs |c cs. length c \<le> length i \<and> \<not> common_prefix i c}", simplified]
    apply(rule Compl_anti_mono[where B="{i @ cs |cs. True}" and A="- ({c@cs | c cs. \<not> common_prefix i c} \<union> {c | c. length c < length i})", simplified])
    apply(safe)
    apply(simp)
    apply(case_tac "(length i) \<le> length x")
     apply(erule_tac x=x in allE, simp)
     apply(simp add: common_prefix_alt)
     (*TODO redoo this proof, this was an old metis run, why does it even prove this?*)
     apply (metis append_eq_append_conv_if notprefix)
    apply(simp)
    done


    
  
  lemma xxx4: "{s@cs | s cs. length s \<le> length i - 1 \<and> s \<noteq> take (length s) (i::string)} = 
        (\<Union> n \<in> {.. length i - 1}. {s@cs | s cs. length s = n \<and> s \<noteq> take (n) i})" (is "?A = ?B")
   proof -
    have a: "?A = (\<Union>s\<in>{s |s. length s \<le> length i - 1 \<and> s \<noteq> take (length s) i}. range (op @ s))" (is "?A=?A'")
    by blast
    have "\<And>n. {s@cs | s cs. length s = n \<and> s \<noteq> take (n) i} = (\<Union>s\<in>{s |s. length s = n \<and> s \<noteq> take (n) i}. range (op @ s))" by auto
    hence b: "?B = (\<Union> n \<in> {.. length i - 1}. (\<Union>s\<in>{s |s. length s = n \<and> s \<noteq> take (n) i}. range (op @ s)))" (is "?B=?B'") by presburger
    {
      fix N::nat and P::"string \<Rightarrow> nat \<Rightarrow> bool"
      have "(\<Union>s\<in>{s |s. length s \<le> N \<and> P s N}. range (op @ s)) = (\<Union> n \<in> {.. N}. (\<Union>s\<in>{s |s. length s = n \<and> P s N}. range (op @ s)))"
        by auto
    } from this[of "length i - 1" "\<lambda>s n. s \<noteq> take (length s) i"]
    have "?A' = (\<Union> n\<le>length i - 1. \<Union>s\<in>{s |s. length s = n \<and> s \<noteq> take (length s) i}. range (op @ s))" by simp
    also have "\<dots> = ?B'" by blast
    with a b show ?thesis by blast
   qed


end
