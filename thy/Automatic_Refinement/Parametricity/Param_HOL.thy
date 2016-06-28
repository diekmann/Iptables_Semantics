section {* Parametricity Theorems for HOL *}
theory Param_HOL
imports Param_Tool
begin

lemma param_if[param]: 
  assumes "(c,c')\<in>Id"
  assumes "\<lbrakk>c;c'\<rbrakk> \<Longrightarrow> (t,t')\<in>R"
  assumes "\<lbrakk>\<not>c;\<not>c'\<rbrakk> \<Longrightarrow> (e,e')\<in>R"
  shows "(If c t e, If c' t' e')\<in>R"
  using assms by auto

lemma param_Let[param]: 
  "(Let,Let)\<in>Ra \<rightarrow> (Ra\<rightarrow>Rr) \<rightarrow> Rr"
  by (auto dest: fun_relD)

lemma param_id[param]: "(id,id)\<in>R\<rightarrow>R" unfolding id_def by parametricity

lemma param_fun_comp[param]: "(op o, op o) \<in> (Ra\<rightarrow>Rb) \<rightarrow> (Rc\<rightarrow>Ra) \<rightarrow> Rc\<rightarrow>Rb" 
  unfolding comp_def[abs_def] by parametricity

lemma param_fun_upd[param]: "
  (op =, op =) \<in> Ra\<rightarrow>Ra\<rightarrow>Id 
  \<Longrightarrow> (fun_upd,fun_upd) \<in> (Ra\<rightarrow>Rb) \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> Ra \<rightarrow> Rb"
  unfolding fun_upd_def[abs_def]
  by (parametricity)

lemma param_unit[param]: "((),())\<in>unit_rel" by auto

lemma rec_bool_is_case: "old.rec_bool = case_bool"
  by (rule ext)+ (auto split: bool.split)

lemma param_bool[param]:
  "(True,True)\<in>Id"
  "(False,False)\<in>Id"
  "(conj,conj)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(disj,disj)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(Not,Not)\<in>Id\<rightarrow>Id"
  "(case_bool,case_bool)\<in>R\<rightarrow>R\<rightarrow>Id\<rightarrow>R"
  "(old.rec_bool,old.rec_bool)\<in>R\<rightarrow>R\<rightarrow>Id\<rightarrow>R"
  "(op \<longleftrightarrow>, op \<longleftrightarrow>)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op \<longrightarrow>, op \<longrightarrow>)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  by (auto split: bool.split simp: rec_bool_is_case)

lemma param_nat1[param]:
  "(0, 0::nat) \<in> Id"
  "(Suc, Suc) \<in> Id \<rightarrow> Id"
  "(1, 1::nat) \<in> Id"
  "(numeral n::nat,numeral n::nat) \<in> Id"
  "(op <, op <::nat \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op \<le>, op \<le>::nat \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op =, op =::nat \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op +::nat\<Rightarrow>_,op +)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op -::nat\<Rightarrow>_,op -)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op *::nat\<Rightarrow>_,op *)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op div::nat\<Rightarrow>_,op div)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op mod::nat\<Rightarrow>_,op mod)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  by auto

lemma param_case_nat[param]:
  "(case_nat,case_nat)\<in>Ra \<rightarrow> (Id \<rightarrow> Ra) \<rightarrow> Id \<rightarrow> Ra"
  apply (intro fun_relI)
  apply (auto split: nat.split dest: fun_relD)
  done

lemma param_rec_nat[param]: 
  "(rec_nat,rec_nat) \<in> R \<rightarrow> (Id \<rightarrow> R \<rightarrow> R) \<rightarrow> Id \<rightarrow> R"
proof (intro fun_relI, goal_cases)
  case (1 s s' f f' n n') thus ?case
    apply (induct n' arbitrary: n s s')
    apply (fastforce simp: fun_rel_def)+
    done
qed

lemma param_int[param]:
  "(0, 0::int) \<in> Id"
  "(1, 1::int) \<in> Id"
  "(numeral n::int,numeral n::int) \<in> Id"
  "(op <, op <::int \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op \<le>, op \<le>::int \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op =, op =::int \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  "(op +::int\<Rightarrow>_,op +)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op -::int\<Rightarrow>_,op -)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op *::int\<Rightarrow>_,op *)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op div::int\<Rightarrow>_,op div)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  "(op mod::int\<Rightarrow>_,op mod)\<in>Id\<rightarrow>Id\<rightarrow>Id"
  by auto

lemma rec_prod_is_case: "old.rec_prod = case_prod"
  by (rule ext)+ (auto split: bool.split)

lemma param_prod[param]:
  "(Pair,Pair)\<in>Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel"
  "(case_prod,case_prod) \<in> (Ra \<rightarrow> Rb \<rightarrow> Rr) \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rr"
  "(old.rec_prod,old.rec_prod) \<in> (Ra \<rightarrow> Rb \<rightarrow> Rr) \<rightarrow> \<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rr"
  "(fst,fst)\<in>\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Ra"
  "(snd,snd)\<in>\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rb"
  by (auto dest: fun_relD split: prod.split 
    simp: prod_rel_def rec_prod_is_case)

lemma param_case_prod':
  "\<lbrakk> (p,p')\<in>\<langle>Ra,Rb\<rangle>prod_rel;
     \<And>a b a' b'. \<lbrakk> p=(a,b); p'=(a',b'); (a,a')\<in>Ra; (b,b')\<in>Rb \<rbrakk> 
      \<Longrightarrow> (f a b, f' a' b')\<in>R
    \<rbrakk> \<Longrightarrow> (case_prod f p, case_prod f' p') \<in> R"
  by (auto split: prod.split)

lemma param_case_prod'': (* TODO: Really needed? *)
  "\<lbrakk> 
    \<And>a b a' b'. \<lbrakk>p=(a,b); p'=(a',b')\<rbrakk> \<Longrightarrow> (f a b,f' a' b')\<in>R  
  \<rbrakk> \<Longrightarrow> (case_prod f p, case_prod f' p')\<in>R"
  by (auto split: prod.split)


lemma param_map_prod[param]: 
  "(map_prod, map_prod) 
  \<in> (Ra\<rightarrow>Rb) \<rightarrow> (Rc\<rightarrow>Rd) \<rightarrow> \<langle>Ra,Rc\<rangle>prod_rel \<rightarrow> \<langle>Rb,Rd\<rangle>prod_rel"
  unfolding map_prod_def[abs_def]
  by parametricity

lemma param_apfst[param]: 
  "(apfst,apfst)\<in>(Ra\<rightarrow>Rb)\<rightarrow>\<langle>Ra,Rc\<rangle>prod_rel\<rightarrow>\<langle>Rb,Rc\<rangle>prod_rel"
  unfolding apfst_def[abs_def] by parametricity

lemma param_apsnd[param]: 
  "(apsnd,apsnd)\<in>(Rb\<rightarrow>Rc)\<rightarrow>\<langle>Ra,Rb\<rangle>prod_rel\<rightarrow>\<langle>Ra,Rc\<rangle>prod_rel"
  unfolding apsnd_def[abs_def] by parametricity

lemma param_curry[param]: 
  "(curry,curry) \<in> (\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rc) \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> Rc"
  unfolding curry_def by parametricity

context partial_function_definitions begin
  lemma 
    assumes M: "monotone le_fun le_fun F" 
    and M': "monotone le_fun le_fun F'"
    assumes ADM: 
      "admissible (\<lambda>a. \<forall>x xa. (x, xa) \<in> Rb \<longrightarrow> (a x, fixp_fun F' xa) \<in> Ra)"
    assumes bot: "\<And>x xa. (x, xa) \<in> Rb \<Longrightarrow> (lub {}, fixp_fun F' xa) \<in> Ra"
    assumes F: "(F,F')\<in>(Rb\<rightarrow>Ra)\<rightarrow>Rb\<rightarrow>Ra"
    assumes A: "(x,x')\<in>Rb"
    shows "(fixp_fun F x, fixp_fun F' x')\<in>Ra"
    using A
    apply (induct arbitrary: x x' rule: ccpo.fixp_induct[OF ccpo _ M])
    apply (rule ADM)
    apply(simp add: fun_lub_def bot)
    apply (subst ccpo.fixp_unfold[OF ccpo M'])
    apply (parametricity add: F)
    done
end


lemma param_option[param]:
  "(None,None)\<in>\<langle>R\<rangle>option_rel"
  "(Some,Some)\<in>R \<rightarrow> \<langle>R\<rangle>option_rel"
  "(case_option,case_option)\<in>Rr\<rightarrow>(R \<rightarrow> Rr)\<rightarrow>\<langle>R\<rangle>option_rel \<rightarrow> Rr"
  "(rec_option,rec_option)\<in>Rr\<rightarrow>(R \<rightarrow> Rr)\<rightarrow>\<langle>R\<rangle>option_rel \<rightarrow> Rr"
  by (auto split: option.split 
    simp: option_rel_def case_option_def[symmetric]
    dest: fun_relD)

lemma param_case_option':
  "\<lbrakk> (x,x')\<in>\<langle>Rv\<rangle>option_rel; 
     \<lbrakk>x=None; x'=None \<rbrakk> \<Longrightarrow> (fn,fn')\<in>R;  
     \<And>v v'. \<lbrakk> x=Some v; x'=Some v'; (v,v')\<in>Rv \<rbrakk> \<Longrightarrow> (fs v, fs' v')\<in>R
   \<rbrakk> \<Longrightarrow> (case_option fn fs x, case_option fn' fs' x') \<in> R"
  by (auto split: option.split)

lemma the_paramL: "\<lbrakk>l\<noteq>None; (l,r)\<in>\<langle>R\<rangle>option_rel\<rbrakk> \<Longrightarrow> (the l, the r)\<in>R"
  apply (cases l)
  by (auto elim: option_relE)

lemma the_paramR: "\<lbrakk>r\<noteq>None; (l,r)\<in>\<langle>R\<rangle>option_rel\<rbrakk> \<Longrightarrow> (the l, the r)\<in>R"
  apply (cases l)
  by (auto elim: option_relE)

lemma the_default_param[param]: 
  "(the_default, the_default) \<in> R \<rightarrow> \<langle>R\<rangle>option_rel \<rightarrow> R"
  unfolding the_default_def
  by parametricity

lemma rec_sum_is_case: "old.rec_sum = case_sum"
  by (rule ext)+ (auto split: sum.split)

lemma param_sum[param]:
  "(Inl,Inl) \<in> Rl \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel"
  "(Inr,Inr) \<in> Rr \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel"
  "(case_sum,case_sum) \<in> (Rl \<rightarrow> R) \<rightarrow> (Rr \<rightarrow> R) \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> R"
  "(old.rec_sum,old.rec_sum) \<in> (Rl \<rightarrow> R) \<rightarrow> (Rr \<rightarrow> R) \<rightarrow> \<langle>Rl,Rr\<rangle>sum_rel \<rightarrow> R"
  by (fastforce split: sum.split dest: fun_relD 
    simp: rec_sum_is_case)+

lemma param_case_sum':
  "\<lbrakk> (s,s')\<in>\<langle>Rl,Rr\<rangle>sum_rel;
     \<And>l l'. \<lbrakk> s=Inl l; s'=Inl l'; (l,l')\<in>Rl \<rbrakk> \<Longrightarrow> (fl l, fl' l')\<in>R;
     \<And>r r'. \<lbrakk> s=Inr r; s'=Inr r'; (r,r')\<in>Rr \<rbrakk> \<Longrightarrow> (fr r, fr' r')\<in>R
   \<rbrakk> \<Longrightarrow> (case_sum fl fr s, case_sum fl' fr' s')\<in>R"
  by (auto split: sum.split)

primrec is_Inl where "is_Inl (Inl _) = True" | "is_Inl (Inr _) = False"
primrec is_Inr where "is_Inr (Inr _) = True" | "is_Inr (Inl _) = False"

lemma is_Inl_param[param]: "(is_Inl,is_Inl) \<in> \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> bool_rel"
  unfolding is_Inl_def by parametricity
lemma is_Inr_param[param]: "(is_Inr,is_Inr) \<in> \<langle>Ra,Rb\<rangle>sum_rel \<rightarrow> bool_rel"
  unfolding is_Inr_def by parametricity

lemma sum_projl_param[param]: 
  "\<lbrakk>is_Inl s; (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> 
  \<Longrightarrow> (Sum_Type.sum.projl s',Sum_Type.sum.projl s) \<in> Ra"
  apply (cases s)
  apply (auto elim: sum_relE)
  done

lemma sum_projr_param[param]: 
  "\<lbrakk>is_Inr s; (s',s)\<in>\<langle>Ra,Rb\<rangle>sum_rel\<rbrakk> 
  \<Longrightarrow> (Sum_Type.sum.projr s',Sum_Type.sum.projr s) \<in> Rb"
  apply (cases s)
  apply (auto elim: sum_relE)
  done

lemma list_rel_append1: "(as @ bs, l) \<in> \<langle>R\<rangle>list_rel 
  \<longleftrightarrow> (\<exists>cs ds. l = cs@ds \<and> (as,cs)\<in>\<langle>R\<rangle>list_rel \<and> (bs,ds)\<in>\<langle>R\<rangle>list_rel)"
  apply (simp add: list_rel_def list_all2_append1)
  apply auto
  apply (metis list_all2_lengthD)
  done

lemma list_rel_append2: "(l,as @ bs) \<in> \<langle>R\<rangle>list_rel 
  \<longleftrightarrow> (\<exists>cs ds. l = cs@ds \<and> (cs,as)\<in>\<langle>R\<rangle>list_rel \<and> (ds,bs)\<in>\<langle>R\<rangle>list_rel)"
  apply (simp add: list_rel_def list_all2_append2)
  apply auto
  apply (metis list_all2_lengthD)
  done


lemma param_append[param]: 
  "(append, append)\<in>\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
  by (auto simp: list_rel_def list_all2_appendI)

lemma param_list1[param]:
  "(Nil,Nil)\<in>\<langle>R\<rangle>list_rel"
  "(Cons,Cons)\<in>R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
  "(case_list,case_list)\<in>Rr\<rightarrow>(R\<rightarrow>\<langle>R\<rangle>list_rel\<rightarrow>Rr)\<rightarrow>\<langle>R\<rangle>list_rel\<rightarrow>Rr"
  apply (force dest: fun_relD split: list.split)+
  done

lemma param_rec_list[param]: 
  "(rec_list,rec_list) 
  \<in> Ra \<rightarrow> (Rb \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> Ra \<rightarrow> Ra) \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> Ra"
proof (intro fun_relI, goal_cases)
  case prems: (1 a a' f f' l l')
  from prems(3) show ?case
    using prems(1,2)
    apply (induct arbitrary: a a')
    apply simp
    apply (fastforce dest: fun_relD)
    done
qed

lemma param_case_list':
  "\<lbrakk> (l,l')\<in>\<langle>Rb\<rangle>list_rel;
     \<lbrakk>l=[]; l'=[]\<rbrakk> \<Longrightarrow> (n,n')\<in>Ra;  
     \<And>x xs x' xs'. \<lbrakk> l=x#xs; l'=x'#xs'; (x,x')\<in>Rb; (xs,xs')\<in>\<langle>Rb\<rangle>list_rel \<rbrakk> 
     \<Longrightarrow> (c x xs, c' x' xs')\<in>Ra
   \<rbrakk> \<Longrightarrow> (case_list n c l, case_list n' c' l') \<in> Ra"
  by (auto split: list.split)
    
lemma param_map[param]: 
  "(map,map)\<in>(R1\<rightarrow>R2) \<rightarrow> \<langle>R1\<rangle>list_rel \<rightarrow> \<langle>R2\<rangle>list_rel"
  unfolding map_rec[abs_def] by (parametricity)
    
lemma param_fold[param]: 
  "(fold,fold)\<in>(Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs \<rightarrow> Rs"
  "(foldl,foldl)\<in>(Rs\<rightarrow>Re\<rightarrow>Rs) \<rightarrow> Rs \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs"
  "(foldr,foldr)\<in>(Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> \<langle>Re\<rangle>list_rel \<rightarrow> Rs \<rightarrow> Rs"
  unfolding List.fold_def List.foldr_def List.foldl_def
  by (parametricity)+

schematic_goal param_take[param]: "(take,take)\<in>(?R::(_\<times>_) set)"
  unfolding take_def 
  by (parametricity)

schematic_goal param_drop[param]: "(drop,drop)\<in>(?R::(_\<times>_) set)"
  unfolding drop_def 
  by (parametricity)

schematic_goal param_length[param]: 
  "(length,length)\<in>(?R::(_\<times>_) set)"
  unfolding size_list_overloaded_def size_list_def 
  by (parametricity)

fun list_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "list_eq eq [] [] \<longleftrightarrow> True"
| "list_eq eq (a#l) (a'#l') 
     \<longleftrightarrow> (if eq a a' then list_eq eq l l' else False)"
| "list_eq _ _ _ \<longleftrightarrow> False"

lemma param_list_eq[param]: "
  (list_eq,list_eq) \<in> 
    (R \<rightarrow> R \<rightarrow> Id) \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> Id"
proof (intro fun_relI, goal_cases)
  case prems: (1 eq eq' l1 l1' l2 l2')
  thus ?case
    apply -
    apply (induct eq' l1' l2' arbitrary: l1 l2 rule: list_eq.induct)
    apply (simp_all only: list_eq.simps |
      elim list_relE |
      parametricity)+
    done
qed

lemma id_list_eq_aux[simp]: "(list_eq op =) = (op =)"
proof (intro ext)
  fix l1 l2 :: "'a list"
  show "list_eq op = l1 l2 = (l1 = l2)"
    apply (induct "op = :: 'a \<Rightarrow> _" l1 l2 rule: list_eq.induct)
    apply simp_all
    done
qed

lemma param_list_equals[param]:
  "\<lbrakk> (op =, op =) \<in> R\<rightarrow>R\<rightarrow>Id \<rbrakk> 
  \<Longrightarrow> (op =, op =) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> Id"
  unfolding id_list_eq_aux[symmetric]
  by (parametricity) 

lemma param_tl[param]:
  "(tl,tl) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
  unfolding tl_def[abs_def]
  by (parametricity)


primrec list_all_rec where
  "list_all_rec P [] \<longleftrightarrow> True"
| "list_all_rec P (a#l) \<longleftrightarrow> P a \<and> list_all_rec P l"

primrec list_ex_rec where
  "list_ex_rec P [] \<longleftrightarrow> False"
| "list_ex_rec P (a#l) \<longleftrightarrow> P a \<or> list_ex_rec P l"

lemma list_all_rec_eq: "(\<forall>x\<in>set l. P x) = list_all_rec P l"
  by (induct l) auto

lemma list_ex_rec_eq: "(\<exists>x\<in>set l. P x) = list_ex_rec P l"
  by (induct l) auto

lemma param_list_ball[param]:
  "\<lbrakk>(P,P')\<in>(Ra\<rightarrow>Id); (l,l')\<in>\<langle>Ra\<rangle> list_rel\<rbrakk> 
    \<Longrightarrow> (\<forall>x\<in>set l. P x, \<forall>x\<in>set l'. P' x) \<in> Id"
  unfolding list_all_rec_eq
  unfolding list_all_rec_def
  by (parametricity)

lemma param_list_bex[param]:
  "\<lbrakk>(P,P')\<in>(Ra\<rightarrow>Id); (l,l')\<in>\<langle>Ra\<rangle> list_rel\<rbrakk> 
    \<Longrightarrow> (\<exists>x\<in>set l. P x, \<exists>x\<in>set l'. P' x) \<in> Id"
  unfolding list_ex_rec_eq[abs_def]
  unfolding list_ex_rec_def
  by (parametricity)

lemma param_rev[param]: "(rev,rev) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
  unfolding rev_def
  by (parametricity)
  
lemma param_Ball[param]: "(Ball,Ball)\<in>\<langle>Ra\<rangle>set_rel\<rightarrow>(Ra\<rightarrow>Id)\<rightarrow>Id"
  by (auto simp: set_rel_def dest: fun_relD)
lemma param_Bex[param]: "(Bex,Bex)\<in>\<langle>Ra\<rangle>set_rel\<rightarrow>(Ra\<rightarrow>Id)\<rightarrow>Id"
  apply (auto simp: set_rel_def dest: fun_relD)
  apply (drule (1) set_mp)
  apply (erule DomainE)
  apply (auto dest: fun_relD)
  done

lemma param_foldli[param]: "(foldli, foldli) 
  \<in> \<langle>Re\<rangle>list_rel \<rightarrow> (Rs\<rightarrow>Id) \<rightarrow> (Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> Rs \<rightarrow> Rs"
  unfolding foldli_def
  by parametricity

lemma param_foldri[param]: "(foldri, foldri) 
  \<in> \<langle>Re\<rangle>list_rel \<rightarrow> (Rs\<rightarrow>Id) \<rightarrow> (Re\<rightarrow>Rs\<rightarrow>Rs) \<rightarrow> Rs \<rightarrow> Rs"
  unfolding foldri_def[abs_def]
  by parametricity

lemma param_nth[param]: 
  assumes I: "i'<length l'"
  assumes IR: "(i,i')\<in>nat_rel"
  assumes LR: "(l,l')\<in>\<langle>R\<rangle>list_rel" 
  shows "(l!i,l'!i') \<in> R"
  using LR I IR
  by (induct arbitrary: i i' rule: list_rel_induct) 
     (auto simp: nth.simps split: nat.split)

lemma param_replicate[param]:
  "(replicate,replicate) \<in> nat_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>list_rel"
  unfolding replicate_def by parametricity

term list_update
lemma param_list_update[param]: 
  "(list_update,list_update) \<in> \<langle>Ra\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> Ra \<rightarrow> \<langle>Ra\<rangle>list_rel"
  unfolding list_update_def[abs_def] by parametricity

lemma param_zip[param]:
  "(zip, zip) \<in> \<langle>Ra\<rangle>list_rel \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel"
    unfolding zip_def by parametricity

lemma param_upt[param]:
  "(upt, upt) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel"
   unfolding upt_def[abs_def] by parametricity

lemma param_concat[param]: "(concat, concat) \<in> 
    \<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
unfolding concat_def[abs_def] by parametricity

lemma param_all_interval_nat[param]: 
  "(List.all_interval_nat, List.all_interval_nat) 
  \<in> (nat_rel \<rightarrow> bool_rel) \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel"
  unfolding List.all_interval_nat_def[abs_def]
  apply parametricity
  apply simp
  done

lemma param_dropWhile[param]: 
  "(dropWhile, dropWhile) \<in> (a \<rightarrow> bool_rel) \<rightarrow> \<langle>a\<rangle>list_rel \<rightarrow> \<langle>a\<rangle>list_rel"
  unfolding dropWhile_def by parametricity

lemma param_takeWhile[param]: 
  "(takeWhile, takeWhile) \<in> (a \<rightarrow> bool_rel) \<rightarrow> \<langle>a\<rangle>list_rel \<rightarrow> \<langle>a\<rangle>list_rel"
  unfolding takeWhile_def by parametricity


subsection {*Sets*}

lemma param_empty[param]:
  "({},{})\<in>\<langle>R\<rangle>set_rel" by (auto simp: set_rel_def)

lemma param_insert[param]:
  "single_valued R \<Longrightarrow> (insert,insert)\<in>R\<rightarrow>\<langle>R\<rangle>set_rel\<rightarrow>\<langle>R\<rangle>set_rel"
  by (auto simp: set_rel_def dest: single_valuedD)

lemma param_union[param]:
  "(op \<union>, op \<union>) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel"
  by (auto simp: set_rel_def)

lemma param_inter[param]:
  assumes "single_valued (R\<inverse>)"
  shows "(op \<inter>, op \<inter>) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel"
  using assms by (auto dest: single_valuedD simp: set_rel_def)

lemma param_diff[param]:
  assumes "single_valued (R\<inverse>)"
  shows "(op -, op -) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel"
  using assms 
  by (auto dest: single_valuedD simp: set_rel_def)

lemma param_subseteq[param]: 
  "\<lbrakk>single_valued (R\<inverse>)\<rbrakk> \<Longrightarrow> (op \<subseteq>, op \<subseteq>) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel \<rightarrow> bool_rel"
  by (clarsimp simp: set_rel_def single_valued_def) blast

lemma param_subset[param]: 
  "\<lbrakk>single_valued (R\<inverse>)\<rbrakk> \<Longrightarrow> (op \<subset>, op \<subset>) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel \<rightarrow> bool_rel"
  (* Fine-tuned proof for speed *)
  apply (simp add: set_rel_def single_valued_def)
  apply safe
  apply blast+
  done

lemma param_set[param]: 
  "single_valued Ra \<Longrightarrow> (set,set)\<in>\<langle>Ra\<rangle>list_rel \<rightarrow> \<langle>Ra\<rangle>set_rel"
proof 
  fix l l'
  assume A: "single_valued Ra"
  assume "(l,l')\<in>\<langle>Ra\<rangle>list_rel"
  thus "(set l, set l')\<in>\<langle>Ra\<rangle>set_rel"
    apply (induct)
    apply simp
    apply simp
    using A apply (parametricity)
    done
qed

end
