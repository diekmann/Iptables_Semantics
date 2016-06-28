section {* Attribute Combinators *}
theory Attr_Comb
imports Refine_Util
begin

ML {*
  infixr 5 THEN_ATTR
  infixr 4 ELSE_ATTR


  signature ATTR_COMB = sig
    exception ATTR_EXC of string

    val NO_ATTR: attribute
    val ID_ATTR: attribute

    val ITE_ATTR': attribute -> attribute -> (exn -> attribute) -> attribute  
    val ITE_ATTR: attribute -> attribute -> attribute -> attribute  

    val THEN_ATTR: attribute * attribute -> attribute
    val ELSE_ATTR: attribute * attribute -> attribute

    val TRY_ATTR: attribute -> attribute
    val RPT_ATTR: attribute -> attribute
    val RPT1_ATTR: attribute -> attribute

    val EFF_ATTR: (Context.generic * thm -> 'a) -> attribute
    val WARN_ATTR: Context.generic -> string -> attribute
    val TRACE_ATTR: string -> attribute -> attribute


    val IGNORE_THM: attribute -> attribute

    val CHECK_PREPARE: (Context.generic * thm -> bool) -> attribute -> attribute

    val COND_attr: (Context.generic * thm -> bool) -> attribute
    val RS_attr: thm -> attribute
    val RSm_attr: thm -> attribute
  end

  structure Attr_Comb :ATTR_COMB = struct

    exception ATTR_EXC of string
    fun NO_ATTR _ = raise ATTR_EXC "NO_ATTR"
    fun ID_ATTR _ = (NONE,NONE)

    fun ITE_ATTR' a b c (context,thm) = let
      fun dflt v NONE = SOME v | dflt _ (SOME v) = SOME v
      val ccxt' = (true,a (context,thm)) 
        handle (e as ATTR_EXC _) => (false,c e (context,thm))
    in
      case ccxt' of
        (false,cxt')       => cxt'
      | (_,(NONE        , NONE    )) => b (context, thm)
      | (_,(SOME context, NONE    )) => b (context, thm) |>> dflt context
      | (_,(NONE        , SOME thm)) => b (context, thm) ||> dflt thm
      | (_,(SOME context, SOME thm)) => 
          b (context, thm) |>> dflt context ||> dflt thm
    end

    fun ITE_ATTR a b c = ITE_ATTR' a b (K c)

  
    fun (a THEN_ATTR b) = ITE_ATTR' a b (reraise)
    fun (a ELSE_ATTR b) = ITE_ATTR a ID_ATTR b

    fun TRY_ATTR a = a ELSE_ATTR ID_ATTR
    fun RPT_ATTR a cxt = (ITE_ATTR a (RPT_ATTR a) ID_ATTR) cxt
    fun RPT1_ATTR a = a THEN_ATTR RPT_ATTR a

    fun EFF_ATTR f cxt = (f cxt; (NONE,NONE))

    fun WARN_ATTR context msg = EFF_ATTR (fn (_,thm) => warning (msg ^ ": " 
      ^ Thm.string_of_thm (Context.proof_of context) thm))

    fun TRACE_ATTR msg a cxt = let
      val _ = tracing (msg ^ "\n" ^ @{make_string} cxt)
      val r = a cxt handle ATTR_EXC m => (
        tracing ("EXC "^m^"("^msg^")"); 
        raise ATTR_EXC m)
      val _ = tracing ("YIELDS (" ^ msg ^ ") " ^ @{make_string} r)
    in r end
  
    fun IGNORE_THM a = a #> apsnd (K NONE)

    fun COND_attr cond cxt = if cond cxt then (NONE,NONE) else 
      raise ATTR_EXC "COND_attr"

    fun CHECK_PREPARE check prep = 
      ITE_ATTR (COND_attr check) 
        ID_ATTR 
        (prep THEN_ATTR COND_attr check)

  
    fun RS_attr thm = 
      Thm.rule_attribute [thm] (fn _ => fn thm' => (
        thm' RS thm handle (exc as THM _) => 
          raise ATTR_EXC ("RS_attr: " ^ @{make_string} exc)))

    fun RSm_attr thm = 
      Thm.rule_attribute [thm] (fn context => fn thm' => (
        RSm (Context.proof_of context) thm' thm handle (exc as THM _) => 
          raise ATTR_EXC ("RSm_attr: " ^ @{make_string} exc)))

  end
*}

end
