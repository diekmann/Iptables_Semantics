section\<open>Ternary Logic\<close>
theory Ternary
imports Main
begin

text\<open>Kleene logic\<close>

datatype ternaryvalue = TernaryTrue | TernaryFalse | TernaryUnknown
datatype ternaryformula = TernaryAnd ternaryformula ternaryformula
                        | TernaryOr ternaryformula ternaryformula
                        | TernaryNot ternaryformula
                        | TernaryValue ternaryvalue

fun ternary_to_bool :: "ternaryvalue \<Rightarrow> bool option" where
  "ternary_to_bool TernaryTrue = Some True" |
  "ternary_to_bool TernaryFalse = Some False" |
  "ternary_to_bool TernaryUnknown = None"

fun bool_to_ternary :: "bool \<Rightarrow> ternaryvalue" where
  "bool_to_ternary True = TernaryTrue" |
  "bool_to_ternary False = TernaryFalse"


lemma "the \<circ> ternary_to_bool \<circ> bool_to_ternary = id"
  by(simp add: fun_eq_iff, clarify, case_tac x, simp_all)
lemma ternary_to_bool_bool_to_ternary: "ternary_to_bool (bool_to_ternary X) = Some X"
by(cases X, simp_all)
lemma ternary_to_bool_None: "ternary_to_bool t = None \<longleftrightarrow> t = TernaryUnknown"
  by(cases t, simp_all)
lemma ternary_to_bool_SomeE: "ternary_to_bool t = Some X \<Longrightarrow>
  (t = TernaryTrue \<Longrightarrow> X = True \<Longrightarrow> P) \<Longrightarrow> (t = TernaryFalse \<Longrightarrow> X = False \<Longrightarrow> P)  \<Longrightarrow> P"
  by(cases t)(simp)+
lemma ternary_to_bool_Some: "ternary_to_bool t = Some X \<longleftrightarrow>
  (t = TernaryTrue \<and> X = True) \<or> (t = TernaryFalse \<and> X = False)"
  by(cases t, simp_all)
lemma bool_to_ternary_Unknown: "bool_to_ternary t = TernaryUnknown \<longleftrightarrow> False"
by(cases t, simp_all)


fun eval_ternary_And :: "ternaryvalue \<Rightarrow> ternaryvalue \<Rightarrow> ternaryvalue" where
  "eval_ternary_And TernaryTrue TernaryTrue = TernaryTrue" |
  "eval_ternary_And TernaryTrue TernaryFalse = TernaryFalse" |
  "eval_ternary_And TernaryFalse TernaryTrue = TernaryFalse" |
  "eval_ternary_And TernaryFalse TernaryFalse = TernaryFalse" |
  "eval_ternary_And TernaryFalse TernaryUnknown = TernaryFalse" |
  "eval_ternary_And TernaryTrue TernaryUnknown = TernaryUnknown" |
  "eval_ternary_And TernaryUnknown TernaryFalse = TernaryFalse" |
  "eval_ternary_And TernaryUnknown TernaryTrue = TernaryUnknown"  |
  "eval_ternary_And TernaryUnknown TernaryUnknown = TernaryUnknown" 

lemma eval_ternary_And_comm: "eval_ternary_And t1 t2 = eval_ternary_And t2 t1"
  by (cases t1 t2 rule: ternaryvalue.exhaust[case_product ternaryvalue.exhaust]) auto

fun eval_ternary_Or :: "ternaryvalue \<Rightarrow> ternaryvalue \<Rightarrow> ternaryvalue" where
  "eval_ternary_Or TernaryTrue TernaryTrue = TernaryTrue" |
  "eval_ternary_Or TernaryTrue TernaryFalse = TernaryTrue" |
  "eval_ternary_Or TernaryFalse TernaryTrue = TernaryTrue" |
  "eval_ternary_Or TernaryFalse TernaryFalse = TernaryFalse" |
  "eval_ternary_Or TernaryTrue TernaryUnknown = TernaryTrue" | 
  "eval_ternary_Or TernaryFalse TernaryUnknown = TernaryUnknown" | 
  "eval_ternary_Or TernaryUnknown TernaryTrue = TernaryTrue" | 
  "eval_ternary_Or TernaryUnknown TernaryFalse = TernaryUnknown" | 
  "eval_ternary_Or TernaryUnknown TernaryUnknown = TernaryUnknown"

fun eval_ternary_Not :: "ternaryvalue \<Rightarrow>  ternaryvalue" where
  "eval_ternary_Not TernaryTrue = TernaryFalse" |
  "eval_ternary_Not TernaryFalse = TernaryTrue" |
  "eval_ternary_Not TernaryUnknown = TernaryUnknown"


text\<open>Just to hint that we did not make a typo, we add the truth table for
      the implication and show that it is compliant with @{term "a \<longrightarrow> b \<longleftrightarrow> \<not>a \<or> b"}\<close>
fun eval_ternary_Imp :: "ternaryvalue \<Rightarrow> ternaryvalue \<Rightarrow> ternaryvalue" where
  "eval_ternary_Imp TernaryTrue TernaryTrue = TernaryTrue" |
  "eval_ternary_Imp TernaryTrue TernaryFalse = TernaryFalse" |
  "eval_ternary_Imp TernaryFalse TernaryTrue = TernaryTrue" |
  "eval_ternary_Imp TernaryFalse TernaryFalse = TernaryTrue" |
  "eval_ternary_Imp TernaryTrue TernaryUnknown = TernaryUnknown" | 
  "eval_ternary_Imp TernaryFalse TernaryUnknown = TernaryTrue" | 
  "eval_ternary_Imp TernaryUnknown TernaryTrue = TernaryTrue" | 
  "eval_ternary_Imp TernaryUnknown TernaryFalse = TernaryUnknown" | 
  "eval_ternary_Imp TernaryUnknown TernaryUnknown = TernaryUnknown"
lemma "eval_ternary_Imp a b = eval_ternary_Or (eval_ternary_Not a) b"
apply(cases a)
  apply(case_tac [!] b)
        apply(simp_all)
done



lemma eval_ternary_Not_UnknownD: "eval_ternary_Not t = TernaryUnknown \<Longrightarrow> t = TernaryUnknown"
  by (cases t) auto

lemma eval_ternary_DeMorgan:
  "eval_ternary_Not (eval_ternary_And a b) = eval_ternary_Or (eval_ternary_Not a) (eval_ternary_Not b)"
  "eval_ternary_Not (eval_ternary_Or a b) = eval_ternary_And (eval_ternary_Not a) (eval_ternary_Not b)"
  by (cases a b rule: ternaryvalue.exhaust[case_product ternaryvalue.exhaust],auto)+

lemma eval_ternary_idempotence_Not: "eval_ternary_Not (eval_ternary_Not a) = a"
  by (cases a) simp_all


lemma eval_ternary_simps_simple: 
  "eval_ternary_And TernaryTrue x = x"
  "eval_ternary_And x TernaryTrue = x"
  "eval_ternary_And TernaryFalse x = TernaryFalse"
  "eval_ternary_And x TernaryFalse = TernaryFalse"
  by(case_tac [!] x)(simp_all)


context
begin
  private lemma bool_to_ternary_simp1: "bool_to_ternary X = TernaryTrue \<longleftrightarrow> X"
    by (metis bool_to_ternary.elims ternaryvalue.distinct(1))
  private lemma bool_to_ternary_simp2:  "bool_to_ternary Y = TernaryFalse \<longleftrightarrow> \<not> Y"
    by (metis bool_to_ternary.elims ternaryvalue.distinct(1))
  private lemma bool_to_ternary_simp3: "eval_ternary_Not (bool_to_ternary X) = TernaryTrue \<longleftrightarrow> \<not> X"
    by (metis (full_types) bool_to_ternary_simp2 eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma bool_to_ternary_simp4: "eval_ternary_Not (bool_to_ternary X) = TernaryFalse \<longleftrightarrow> X"
    by (metis bool_to_ternary_simp1 eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma bool_to_ternary_simp5: "\<not> (eval_ternary_Not (bool_to_ternary X) = TernaryUnknown)"
    by (metis bool_to_ternary_Unknown eval_ternary_Not_UnknownD)

  private lemma bool_to_ternary_simp6: "bool_to_ternary X \<noteq> TernaryUnknown"
    by (metis (full_types) bool_to_ternary.simps(1) bool_to_ternary.simps(2) ternaryvalue.distinct(3) ternaryvalue.distinct(5))

  lemmas bool_to_ternary_simps = bool_to_ternary_simp1 bool_to_ternary_simp2
                                 bool_to_ternary_simp3 bool_to_ternary_simp4
                                 bool_to_ternary_simp5 bool_to_ternary_simp6
end

context
begin
  private lemma bool_to_ternary_pullup1:
    "eval_ternary_Not (bool_to_ternary X) = bool_to_ternary (\<not> X)"
    by(cases X)(simp_all)
  
  private lemma bool_to_ternary_pullup2:
    "eval_ternary_And (bool_to_ternary X1) (bool_to_ternary X2) = bool_to_ternary (X1 \<and> X2)"
    by (metis bool_to_ternary_simps(1) bool_to_ternary_simps(2) eval_ternary_simps_simple(2) eval_ternary_simps_simple(4))

  private lemma bool_to_ternary_pullup3:
    "eval_ternary_Imp (bool_to_ternary X1) (bool_to_ternary X2) = bool_to_ternary (X1 \<longrightarrow> X2)"
    by (metis bool_to_ternary_simps(1) bool_to_ternary_simps(2) eval_ternary_Imp.simps(1) 
        eval_ternary_Imp.simps(2) eval_ternary_Imp.simps(3) eval_ternary_Imp.simps(4))
    
  private lemma bool_to_ternary_pullup4:
    "eval_ternary_Or (bool_to_ternary X1) (bool_to_ternary X2) = bool_to_ternary (X1 \<or> X2)"
    by (metis (full_types) bool_to_ternary.simps(1) bool_to_ternary.simps(2) eval_ternary_Or.simps(1) eval_ternary_Or.simps(2) eval_ternary_Or.simps(3) eval_ternary_Or.simps(4))  
  
  lemmas bool_to_ternary_pullup = bool_to_ternary_pullup1 bool_to_ternary_pullup2
                                  bool_to_ternary_pullup3 bool_to_ternary_pullup4
end



fun ternary_ternary_eval :: "ternaryformula \<Rightarrow> ternaryvalue" where
  "ternary_ternary_eval (TernaryAnd t1 t2) = eval_ternary_And (ternary_ternary_eval t1) (ternary_ternary_eval t2)" |
  "ternary_ternary_eval (TernaryOr t1 t2) = eval_ternary_Or (ternary_ternary_eval t1) (ternary_ternary_eval t2)" |
  "ternary_ternary_eval (TernaryNot t) = eval_ternary_Not (ternary_ternary_eval t)" |
  "ternary_ternary_eval (TernaryValue t) = t"

lemma ternary_ternary_eval_DeMorgan: "ternary_ternary_eval (TernaryNot (TernaryAnd a b)) = 
    ternary_ternary_eval (TernaryOr (TernaryNot a) (TernaryNot b))"
by (simp add: eval_ternary_DeMorgan)

lemma ternary_ternary_eval_idempotence_Not:
  "ternary_ternary_eval (TernaryNot (TernaryNot a)) = ternary_ternary_eval a"
by (simp add: eval_ternary_idempotence_Not)

lemma ternary_ternary_eval_TernaryAnd_comm:
  "ternary_ternary_eval (TernaryAnd t1 t2) = ternary_ternary_eval (TernaryAnd t2 t1)"
by (simp add: eval_ternary_And_comm)

lemma "eval_ternary_Not (ternary_ternary_eval t) = (ternary_ternary_eval (TernaryNot t))" by simp


context
begin
  private lemma eval_ternary_simps_2:
      "eval_ternary_And (bool_to_ternary P) T = TernaryTrue \<longleftrightarrow> P \<and> T = TernaryTrue"
      "eval_ternary_And T (bool_to_ternary P) = TernaryTrue \<longleftrightarrow> P \<and> T = TernaryTrue"
  apply(case_tac [!] P)
     apply(simp_all add: eval_ternary_simps_simple)
  done

  private lemma eval_ternary_simps_3:
      "eval_ternary_And (ternary_ternary_eval x) T = TernaryTrue \<longleftrightarrow>
        ternary_ternary_eval x = TernaryTrue \<and> T = TernaryTrue"
      "eval_ternary_And T (ternary_ternary_eval x) = TernaryTrue \<longleftrightarrow>
        ternary_ternary_eval x = TernaryTrue \<and> T = TernaryTrue"
  apply(case_tac [!] T)
       apply(simp_all add: eval_ternary_simps_simple)
   apply(case_tac [!] "(ternary_ternary_eval x)")
       apply(simp_all)
  done

  lemmas eval_ternary_simps = eval_ternary_simps_simple eval_ternary_simps_2 eval_ternary_simps_3
end

definition ternary_eval :: "ternaryformula \<Rightarrow> bool option" where
  "ternary_eval t = ternary_to_bool (ternary_ternary_eval t)"

subsection\<open>Negation Normal Form\<close>

text\<open>A formula is in Negation Normal Form (NNF) if negations only occur at the atoms (not before and/or)\<close>
inductive NegationNormalForm :: "ternaryformula \<Rightarrow> bool" where
  "NegationNormalForm (TernaryValue v)" |
  "NegationNormalForm (TernaryNot (TernaryValue v))" |
  "NegationNormalForm \<phi> \<Longrightarrow> NegationNormalForm \<psi> \<Longrightarrow> NegationNormalForm (TernaryAnd \<phi> \<psi>)"|
  "NegationNormalForm \<phi> \<Longrightarrow> NegationNormalForm \<psi> \<Longrightarrow> NegationNormalForm (TernaryOr \<phi> \<psi>)"

text\<open>Convert a @{typ ternaryformula} to a  @{typ ternaryformula} in NNF.\<close>
fun NNF_ternary :: "ternaryformula \<Rightarrow> ternaryformula" where
  "NNF_ternary (TernaryValue v) = TernaryValue v" |
  "NNF_ternary (TernaryAnd t1 t2) = TernaryAnd (NNF_ternary t1) (NNF_ternary t2)" |
  "NNF_ternary (TernaryOr t1 t2) = TernaryOr (NNF_ternary t1) (NNF_ternary t2)" |
  "NNF_ternary (TernaryNot (TernaryNot t)) = NNF_ternary t" |
  "NNF_ternary (TernaryNot (TernaryValue v)) = TernaryValue (eval_ternary_Not v)" |
  "NNF_ternary (TernaryNot (TernaryAnd t1 t2)) = TernaryOr (NNF_ternary (TernaryNot t1)) (NNF_ternary (TernaryNot t2))" |
  "NNF_ternary (TernaryNot (TernaryOr t1 t2)) = TernaryAnd (NNF_ternary (TernaryNot t1)) (NNF_ternary (TernaryNot t2))"


lemma NNF_ternary_correct: "ternary_ternary_eval (NNF_ternary t) = ternary_ternary_eval t"
  proof(induction t rule: NNF_ternary.induct)
  qed(simp_all add: eval_ternary_DeMorgan eval_ternary_idempotence_Not)

lemma NNF_ternary_NegationNormalForm: "NegationNormalForm (NNF_ternary t)"
  proof(induction t rule: NNF_ternary.induct)
  qed(auto simp add: eval_ternary_DeMorgan eval_ternary_idempotence_Not intro: NegationNormalForm.intros)




context
begin
  private lemma ternary_lift1: "eval_ternary_Not tv \<noteq> TernaryFalse \<longleftrightarrow> tv = TernaryFalse \<or> tv = TernaryUnknown"
    using eval_ternary_Not.elims by blast
  private lemma ternary_lift2: "eval_ternary_Not tv \<noteq> TernaryTrue \<longleftrightarrow> tv = TernaryTrue \<or> tv = TernaryUnknown"
    using eval_ternary_Not.elims by blast
  private lemma ternary_lift3: "eval_ternary_Not tv = TernaryFalse \<longleftrightarrow> tv = TernaryTrue"
    by (metis eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma ternary_lift4: "eval_ternary_Not tv = TernaryTrue \<longleftrightarrow> tv = TernaryFalse"
    by (metis eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma ternary_lift5: "eval_ternary_Not tv = TernaryUnknown \<longleftrightarrow> tv = TernaryUnknown"
    by (metis eval_ternary_Not.simps(3) eval_ternary_idempotence_Not)

  private lemma ternary_lift6: "eval_ternary_And t1 t2 = TernaryFalse \<longleftrightarrow> t1 = TernaryFalse \<or> t2 = TernaryFalse"
    using eval_ternary_And.elims by blast
  private lemma ternary_lift7: "eval_ternary_And t1 t2 = TernaryTrue \<longleftrightarrow> t1 = TernaryTrue \<and> t2 = TernaryTrue"
    using eval_ternary_And.elims by blast

  lemmas ternary_lift = ternary_lift1 ternary_lift2 ternary_lift3 ternary_lift4 ternary_lift5 ternary_lift6 ternary_lift7
end

context
begin
  private lemma l1: "eval_ternary_Not tv = TernaryTrue \<Longrightarrow> tv = TernaryFalse"
    by (metis eval_ternary_Not.simps(1) eval_ternary_idempotence_Not)
  private lemma l2: "eval_ternary_And t1 t2 = TernaryFalse \<Longrightarrow> t1 = TernaryFalse \<or> t2 = TernaryFalse"
    using eval_ternary_And.elims by blast
  
  lemmas eval_ternaryD = l1 l2
end

end
