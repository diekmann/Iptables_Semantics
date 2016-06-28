theory Mk_Record_Simp
imports Refine_Util Mpat_Antiquot
begin

(*
  mk_record_simp: Converts a lemma of the form 
    "f s = x" to the form "r \<equiv> s \<Longrightarrow> f r = x"
  
  This is used to fold the x.simp - lemmas of a record x with a definition
  of the form "r \<equiv> \<lparr> ... \<rparr>".

  Usage example:
    record foo = ...
    definition c :: foo where "c \<equiv> \<lparr> ... \<rparr>"
    lemmas c_simps[simp] = foo.simps[mk_record_simp, OF c_def]
*)
lemma mk_record_simp_thm:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "f s = x"
  assumes "r \<equiv> s"
  shows "f r = x"
  using assms by simp

ML {*
  fun mk_record_simp context thm = let
    val ctxt = Context.proof_of context
    val cert = Thm.cterm_of ctxt
  in
    case Thm.concl_of thm of
      @{mpat "Trueprop (?f _=_)"} => 
        let
          val cf = cert f
          val r = infer_instantiate ctxt [(("f", 0), cf)] @{thm mk_record_simp_thm}
          val r = r OF [thm]
        in r end
    | _ => raise THM("",~1,[thm])

  end
*}

attribute_setup mk_record_simp = 
  {* Scan.succeed (Thm.rule_attribute [] (mk_record_simp)) *}
  "Make simplification rule for record definition"

end
