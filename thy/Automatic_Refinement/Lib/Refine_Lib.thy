theory Refine_Lib
imports 
  Refine_Util 
  Attr_Comb 
  Named_Sorted_Thms 
  Prio_List 
  Mpat_Antiquot
  Mk_Term_Antiquot
  Tagged_Solver
  Anti_Unification
  Misc
  Foldi
  Indep_Vars
  Select_Solve
  Mk_Record_Simp
  Digraph_Basic
begin
  ML_file "Cond_Rewr_Conv.ML"
  ML_file "Revert_Abbrev.ML"
end
