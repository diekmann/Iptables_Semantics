theory Attic
imports Main
begin

ML\<open>(*unused*)
local
  fun skip_until_r _ beginning [] = (false, beginning, [])
   |  skip_until_r k beginning ss =
      let val (_, rest) = Scan.catch (Scan.this_string k) ss
      in
        (true, beginning, rest)
      end
      handle Fail _ => skip_until_r k (beginning @ [hd ss]) (tl ss);
in
  fun skip_until (k: string) (ss: string list) : (string list * string list) option = let
    val (found, beginning, rest) = skip_until_r k [] ss in
      if found then SOME (beginning, rest) else NONE
    end;
end;
\<close>
ML_val\<open>
skip_until " -j " (raw_explode "asdf -j foo");
skip_until " -xx " (raw_explode "a -x foo");
\<close>
end