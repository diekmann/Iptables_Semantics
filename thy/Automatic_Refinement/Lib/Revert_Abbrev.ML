(*
  Revert abbreviations.
 TODO: This is only a hack, a clean solution would somehow dock to the
   locale mechanism, and thus automatically consider new interpretations and
   extensions of the locale
*)

signature REVERT_ABBREV = sig
  val revert_abbrev_matching: (string -> bool) -> theory -> theory
  val revert_abbrev: string -> theory -> theory
end

structure Revert_Abbrev :REVERT_ABBREV = struct
  fun match_string' pat str = match_string ("^"^pat^"$") ("^"^str^"$")

  (* Revert all abbreviations whose name matches the given matcher *)
  fun revert_abbrev_matching match_fun thy = let
    val ctxt = Proof_Context.init_global thy;
    val {const_space, constants, ...} = Sign.consts_of thy |> Consts.dest;
    val names =
    Name_Space.extern_entries true ctxt const_space constants
    |> map_filter (fn 
        ((name, _), (_, SOME _)) => if match_fun name then SOME name else NONE
      | _ => NONE)
    val _ = if null names then 
      warning ("revert_abbrevs: No matching constants") 
    else ();
  in fold (Sign.revert_abbrev "") names thy end

  (* Revert abbreviations matching anchored glob-pattern *)
  fun revert_abbrev pat = revert_abbrev_matching (match_string' pat)
end
