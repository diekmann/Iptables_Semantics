let
  fun parser_end p i = let
    val (r,es) = Scan.finite Symbol.stopper p i
  in
    if es = [] then r else K r (* cause error - TODO: How do I do that properly? *) (($$ "x") (Symbol.explode ""))
  end
  val r1 = parser_end (($$ "o") -- (Scan.repeat (($$ "h" || $$ "l") >> (fn x => fn y => x ^ y)))) (Symbol.explode "ohhhll")
in
  (uncurry (fold (fn a => fn b => a b)) o swap) r1
end