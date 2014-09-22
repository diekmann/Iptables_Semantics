theory codetests
imports "../CTranslation"
begin

ML {* Context.>> (Context.map_theory (
        TermsTypes.prim_mk_defn "foo" @{term "33::nat"}))
*}

thm foo_def

ML {*
  Context.>> (Context.map_theory (
    RecursiveRecordPackage.define_record_type [
      {record_name = "myrecord",
       fields = [{fldname = "fld1", fldty = @{typ "nat"}},
                 {fldname = "myset", fldty = @{typ "nat \<Rightarrow> bool"}}]}
    ]))
*}

thm myrecord_accupd_same

end
