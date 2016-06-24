theory Autoref_Data
imports Main "../Lib/Refine_Util"
begin

ML {*
  signature AUTOREF_DATA = sig
    type T
    exception exNULL
    exception exCIRCULAR
    val get: Proof.context -> T
    val init: Proof.context -> Proof.context
  end

  functor Autoref_Data (
    type T
    val compute: Proof.context -> T
    val prereq: (Proof.context -> Proof.context) list
  ) : AUTOREF_DATA = 
  struct
    type T = T
    datatype state = NULL | INITIALIZING | INIT of T
    exception exNULL
    exception exCIRCULAR

    structure data = Proof_Data ( 
      type T = state
      fun init _ = NULL
    )

    fun get ctxt = case data.get ctxt of
      NULL => raise exNULL
    | INITIALIZING => raise exCIRCULAR
    | INIT x => x
      
    fun init ctxt = case data.get ctxt of
      INITIALIZING => raise exCIRCULAR
    | INIT _ => ctxt
    | NULL =>
        let
          val ctxt = data.put INITIALIZING ctxt
          val ctxt = fold (fn f => fn ctxt => f ctxt) prereq ctxt
          val ctxt = data.put (INIT (compute ctxt)) ctxt
        in
          ctxt
        end

  end

*}

end
