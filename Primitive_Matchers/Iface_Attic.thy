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

(*
(* Old stuff below *)
    (*TODO TODO TODO: a packet has a fixed string as interface, there is no wildcard in it! TODO*)
    (*TODO: this must be redone! see below*)

fun iface_name_eq :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "iface_name_eq [] [] \<longleftrightarrow> True" |
  "iface_name_eq [i1] [] \<longleftrightarrow> (i1 = CHR ''+'')" |
  "iface_name_eq [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
  "iface_name_eq [i1] [i2] \<longleftrightarrow> (i1 = CHR ''+'' \<or> i2 = CHR ''+'' \<or> i1 = i2)" |
  "iface_name_eq (i1#i1s) (i2#i2s) \<longleftrightarrow> (i1 = CHR ''+'' \<and> i1s = [] \<or> i2 = CHR ''+'' \<and> i2s = []) \<or> (i1 = i2 \<and> iface_name_eq i1s i2s)" |
  "iface_name_eq _ _ \<longleftrightarrow> False"


  lemma "iface_name_eq ''lo'' ''lo''" by eval
  lemma "iface_name_eq ''lo'' ''lo+''" by eval
  lemma "iface_name_eq ''lo'' ''l+''" by eval
  lemma "iface_name_eq ''lo'' ''+''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo++''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo+++''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo1+''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo1''" by eval
  text{*The wildcard interface name*}
  lemma "iface_name_eq '''' ''+''" by eval

fun iface_name_is_wildcard :: "string \<Rightarrow> bool" where
  "iface_name_is_wildcard [] \<longleftrightarrow> False" |
  "iface_name_is_wildcard [s] \<longleftrightarrow> s = CHR ''+''" |
  "iface_name_is_wildcard (_#ss) \<longleftrightarrow> iface_name_is_wildcard ss"
lemma iface_name_is_wildcard_alt: "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> hd (rev eth) = CHR ''+''"
  apply(induction eth rule: iface_name_is_wildcard.induct)
   apply(simp_all)
  apply(rename_tac s s' ss)
  apply(case_tac "rev ss")
   apply(simp_all)
  done
(*lemma iface_name_is_wildcard_cases: "iface_name_is_wildcard eth \<longleftrightarrow> (case rev eth of [] \<Rightarrow> False | s#ss \<Rightarrow> s = CHR ''+'')"
  apply(induction eth rule: iface_name_is_wildcard.induct)
   apply(simp_all)
  apply(rename_tac s s' ss)
  apply(case_tac "rev ss")
   apply(simp_all)
  done*)

definition iface_name_prefix :: "string \<Rightarrow> string" where
  "iface_name_prefix i \<equiv> (if iface_name_is_wildcard i then butlast i else i)"
lemma "iface_name_prefix ''eth4'' = ''eth4''" by eval
lemma "iface_name_prefix ''eth+'' = ''eth''" by eval
lemma "iface_name_prefix ''eth++'' = ''eth+''" by eval --"the trailing plus is a constant and not a wildcard!"
lemma "iface_name_prefix '''' = ''''" by eval

lemma "take (length i - 1) i = butlast i" by (metis butlast_conv_take) 

lemma iface_name_eq_alt: "iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2 \<or>
      iface_name_is_wildcard i1 \<and> take ((length i1) - 1) i1 = take ((length i1) - 1) i2 \<or>
      iface_name_is_wildcard i2 \<and> take ((length i2) - 1) i2 = take ((length i2) - 1) i1"
apply(induction i1 i2 rule: iface_name_eq.induct)
       apply(simp_all)
  apply(simp_all add: iface_name_is_wildcard_alt take_Cons' split:split_if_asm)
        apply(safe)
done

lemma iface_name_eq_refl: "iface_name_eq is is" by(simp add: iface_name_eq_alt)
lemma iface_name_eq_sym: "iface_name_eq i1 i2 \<Longrightarrow> iface_name_eq i2 i1" by(auto simp add: iface_name_eq_alt)
lemma iface_name_eq_not_trans: "\<lbrakk>i1 = ''eth0''; i2 = ''eth+''; i3 = ''eth1''\<rbrakk> \<Longrightarrow> 
    iface_name_eq i1 i2 \<Longrightarrow> iface_name_eq i2 i3 \<Longrightarrow> \<not> iface_name_eq i1 i3" by(simp)

lemma "iface_name_eq (i2 # i2s) [] \<Longrightarrow> i2 = CHR ''+'' \<and> i2s = []" by(auto simp add: iface_name_eq_alt)



text{*Examples*}
  lemma "iface_name_eq ''eth+'' ''eth3''" by eval
  lemma "iface_name_eq ''eth+'' ''e+''" by eval
  lemma "iface_name_eq ''eth+'' ''eth_tun_foobar''" by eval
  lemma "iface_name_eq ''eth+'' ''eth_tun+++''" by eval
  lemma "\<not> iface_name_eq ''eth+'' ''wlan+''" by eval
  lemma "iface_name_eq ''eth1'' ''eth1''" by eval
  lemma "\<not> iface_name_eq ''eth1'' ''eth2''" by eval
  lemma "iface_name_eq ''eth+'' ''eth''" by eval
  lemma "\<not> iface_name_eq ''a'' ''b+''" by eval
  lemma "iface_name_eq ''+'' ''''" by eval
  lemma "iface_name_eq ''++++'' ''++''" by eval
  lemma "\<not> iface_name_eq '''' ''++''" by eval
  lemma "iface_name_eq ''+'' ''++''" by eval
  lemma "\<not> iface_name_eq ''ethA+'' ''ethB+''" by eval

  text{*If the interfaces don't end in a wildcard, then @{const iface_name_eq} is just simple equality*}
  lemma iface_name_eq_case_nowildcard: "\<lbrakk>\<not> iface_name_is_wildcard i1; \<not> iface_name_is_wildcard i2 \<rbrakk> \<Longrightarrow> iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2"
    apply(simp add: iface_name_is_wildcard_alt iface_name_eq_alt)
    by blast
  text{*If there is exactly one wildcard, both interface strings are equal for the length of the wildcard minus one (called @{const iface_name_prefix}}*}
  lemma iface_name_eq_case_onewildcard: "\<lbrakk>iface_name_is_wildcard i1; \<not> iface_name_is_wildcard i2 \<rbrakk> \<Longrightarrow> iface_name_eq i1 i2 \<longleftrightarrow> 
      iface_name_prefix i1 = take (length (iface_name_prefix i1)) i2"
    apply(simp add: iface_name_eq_alt iface_name_prefix_def butlast_conv_take)
  by (metis diff_le_self min.commute min_def)

  text{*If both are wildcards, then they are equal in their wildcard prefix*}
  lemma iface_name_eq_case_twowildcard: "\<lbrakk>iface_name_is_wildcard i1; iface_name_is_wildcard i2 \<rbrakk> \<Longrightarrow> iface_name_eq i1 i2 \<longleftrightarrow> 
    take (min (length (iface_name_prefix i1)) (length (iface_name_prefix i2))) i1 = take (min (length (iface_name_prefix i1)) (length (iface_name_prefix i2))) i2"
    apply(simp add: iface_name_eq_alt iface_name_prefix_def)
    apply(safe)
      apply (metis min.commute take_take)
     apply (metis take_take)
    by (metis min_def)
  
    text{*If both are wildcards of equal length, then both iface names are actually equal*}
    lemma iface_name_eq_case_twowildcardeqlength: 
      assumes "length i1 = length i2" and "iface_name_is_wildcard i1" and "iface_name_is_wildcard i2"
      shows "iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2"
    proof -
      {
          fix n have "(min n (n - Suc 0)) = (n - Suc 0)" by linarith
      } note min_help=this
      from assms have i1_last: "last i1  = CHR ''+''" and i2_last: "last i2  = CHR ''+''"
        apply(simp_all add: iface_name_is_wildcard_alt)
        by (metis hd_rev)+
      from assms have "i1 \<noteq> []" and "i2 \<noteq> []"
        by(simp_all add: iface_name_is_wildcard_alt)

      from iface_name_eq_case_twowildcard assms have "iface_name_eq i1 i2 \<longleftrightarrow>
            take (min (length (iface_name_prefix i1)) (length (iface_name_prefix i2))) i1 = 
            take (min (length (iface_name_prefix i1)) (length (iface_name_prefix i2))) i2" by simp
      also have "\<dots> \<longleftrightarrow> take (length i1 - 1) i1 = take (length i1 - 1) i2"
        by(simp add: assms iface_name_prefix_def min_help)
      also have "\<dots> \<longleftrightarrow> butlast i1 = butlast i2" using assms(1) butlast_conv_take by metis
      also have "\<dots> \<longleftrightarrow> butlast i1 @ [last i1] = butlast i2 @ [last i2]"
        using i1_last i2_last by simp
      finally show "iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2" using `i1 \<noteq> []` `i2 \<noteq> []` append_butlast_last_id by simp
    qed
      
      

  
  (*fun iface_name_leq :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "iface_name_leq [] [] \<longleftrightarrow> True" |
    "iface_name_leq [i1] [] \<longleftrightarrow> False" |
    "iface_name_leq [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
    "iface_name_leq [i1] [i2] \<longleftrightarrow> (i1 = i2 \<or> i2 = CHR ''+'')" |
    "iface_name_leq (i1#i1s) (i2#i2s) \<longleftrightarrow> (i2 = CHR ''+'' \<and> i2s = []) \<or> (i1 = i2 \<and> iface_name_leq i1s i2s)" |
    "iface_name_leq _ _ \<longleftrightarrow> False"


  lemma "iface_name_leq ''lo'' ''lo''" by eval
  lemma "iface_name_leq ''lo'' ''lo+''" by eval
  lemma "iface_name_leq ''lo'' ''l+''" by eval
  lemma "iface_name_leq ''lo'' ''+''" by eval
  lemma "\<not> iface_name_leq ''lo+'' ''lo''" by eval
  lemma "\<not> iface_name_leq ''l+'' ''lo''" by eval
  lemma "\<not> iface_name_leq ''+'' ''lo''" by eval
  lemma "\<not> iface_name_leq ''lo'' ''lo++''" by eval
  lemma "iface_name_leq '''' ''+''" by eval
  lemma "iface_name_leq ''++'' ''+''" by eval
  lemma "iface_name_leq ''+'' ''++''" by eval (*NOOO*)
  lemma "\<not> iface_name_leq ''+'' ''''" by eval


  lemma "iface_name_leq i1 i2 \<longleftrightarrow> iface_name_eq i1 i2 \<and> (length (iface_name_prefix i2) \<le> length (iface_name_prefix i1))"
  apply(induction i1 i2 rule: iface_name_leq.induct)
         apply(simp_all)
         nitpick
    apply(simp_all add: iface_name_is_wildcard_alt take_Cons' split:split_if_asm)
          apply(safe)
  done
  lemma iface_name_leq_alt: "iface_name_leq i1 i2 \<longleftrightarrow> i1 = i2 \<or>
        iface_name_is_wildcard i2 \<and> take ((length i2) - 1) i2 = take ((length i2) - 1) i1"
  apply(induction i1 i2 rule: iface_name_leq.induct)
         apply(simp_all)
    apply(simp_all add: iface_name_is_wildcard_alt take_Cons' split:split_if_asm)
          apply(safe)
  done
  lemma iface_name_leq_iff_eq: "iface_name_leq i1 i2 \<longleftrightarrow> iface_name_eq i1 i2 \<and> (
            i1 = i2 \<or> 
            iface_name_is_wildcard i2 \<and> \<not> iface_name_is_wildcard i1 \<or>
            iface_name_is_wildcard i1 \<and> iface_name_is_wildcard i2 \<and> take ((length i2) - 1) i2 = take ((length i2) - 1) i1)"
    apply(induction i1 i2 rule: iface_name_leq.induct)
           apply(simp_all)
      apply(simp_all add: take_Cons' iface_name_eq_alt iface_name_is_wildcard_alt)
      apply(safe)
      apply(simp_all) (*TODO: indent by 117*)
    done


  lemma iface_name_leq_refl: "iface_name_leq is is" by(simp add: iface_name_leq_alt iface_name_eq_refl)
  lemma iface_name_leq_sym: "iface_name_leq i1 i2 \<Longrightarrow> iface_name_leq i2 i1 \<Longrightarrow> i1 = i2"
    nitpick
    apply(simp add: iface_name_leq_alt iface_name_eq_alt)
    oops
  lemma iface_name_leq_not_trans: "\<lbrakk>i1 = ''eth0''; i2 = ''eth+''; i3 = ''eth++''\<rbrakk> \<Longrightarrow> 
    iface_name_leq i1 i2 \<Longrightarrow> iface_name_leq i2 i3 \<Longrightarrow> \<not> iface_name_leq i1 i3" by(simp)

  lemma "iface_name_leq i1 i2 \<Longrightarrow> (*iface_name_leq i2 i1 \<Longrightarrow>*) iface_name_eq i1 i2" by(simp add: iface_name_leq_iff_eq iface_name_eq_sym)
  lemma "iface_name_leq i2 i1 \<Longrightarrow> (*iface_name_leq i2 i1 \<Longrightarrow>*) iface_name_eq i1 i2" by(simp add: iface_name_leq_iff_eq iface_name_eq_sym)*)


  text{*takes two interface names, returns the most specific one*}
  definition iface_name_conjuct_merge :: "string \<Rightarrow> string \<Rightarrow> string option" where
    "iface_name_conjuct_merge i1 i2 \<equiv> (if \<not> iface_name_eq i1 i2 then None else
      if iface_name_is_wildcard i1 \<and> iface_name_is_wildcard i2 then 
        (if length i1 \<le> length i2 then Some i2 else Some i1)
      else if iface_name_is_wildcard i1 then Some i2
      else Some i1
      )"


  lemma iface_name_conjuct_merge_sym: "iface_name_conjuct_merge i1 i2 = iface_name_conjuct_merge i2 i1"
    apply(simp add: iface_name_conjuct_merge_def)
    apply(safe)
                 apply(simp_all add: iface_name_eq_sym)
      apply(simp_all add: iface_name_eq_case_nowildcard)
    apply(simp add: iface_name_eq_case_twowildcardeqlength)
    done

  lemma "iface_name_conjuct_merge ''lo'' ''lo'' = Some ''lo''" by eval
  lemma "iface_name_conjuct_merge ''lo'' ''lo+'' = Some ''lo''" by eval
  lemma "iface_name_conjuct_merge ''lo'' ''l+'' = Some ''lo''" by eval
  lemma "iface_name_conjuct_merge ''lo'' ''+'' = Some ''lo''" by eval
  lemma "iface_name_conjuct_merge ''lo'' ''lo++'' = None" by eval
  lemma "iface_name_conjuct_merge '''' ''+'' = Some ''''" by eval
  lemma "iface_name_conjuct_merge ''++'' ''+'' = Some ''++''" by eval
  lemma "iface_name_conjuct_merge ''x'' '''' = None" by eval


   lemma "{i. \<exists> X. (iface_name_conjuct_merge i1 i2) = Some X \<and> iface_name_eq X i} = {i. iface_name_eq i1 i} \<inter> {i. iface_name_eq i2 i}"
    nitpick (*more iface_name_eq on right hand side?*)
    oops

   lemma "iface_name_eq i1 i \<and> iface_name_eq i2 i \<longleftrightarrow> (case (iface_name_conjuct_merge i1 i2) of 
      Some X \<Rightarrow> iface_name_eq X i |
      None \<Rightarrow> False)"
      oops




(*eth+ and !eth42. Problem!*)
fun match_iface_name_and :: "string negation_type \<Rightarrow> string negation_type \<Rightarrow> string negation_type option" where
  "match_iface_name_and (Pos i1) (Pos i2) = (if iface_name_eq i1 i2 then (if length i1 \<ge> length i2 then Some (Pos i1) else Some (Pos i2)) else None)"
  (*we need the 'shorter' iface. probably we want a pseudo order on the ifaces*)
    (*An order which is not transitive?*)

*)

end
