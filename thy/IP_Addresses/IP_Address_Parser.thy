theory IP_Address_Parser
imports IP_Address
        IPv4
        IPv6
        "~~/src/HOL/Library/Code_Target_Nat" (*!!*)
begin

section\<open>Parsing IP Addresses\<close>

subsection\<open>IPv4 Parser\<close>

ML\<open>
local
  fun extract_int ss = case ss |> implode |> Int.fromString
                                of SOME i => i
                                |  NONE   => raise Fail "unparsable int";

  fun mk_nat maxval i = if i < 0 orelse i > maxval
            then
              raise Fail("nat ("^Int.toString i^") must be between 0 and "^Int.toString maxval)
            else (HOLogic.mk_number HOLogic.natT i);
  val mk_nat255 = mk_nat 255;

  fun mk_quadrupel (((a,b),c),d) = HOLogic.mk_prod
           (mk_nat255 a, HOLogic.mk_prod (mk_nat255 b, HOLogic.mk_prod (mk_nat255 c, mk_nat255 d)));

in 
  fun mk_ipv4addr ip = @{const ipv4addr_of_dotdecimal} $ mk_quadrupel ip;

  val parser_ipv4 = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int);
end;

local
  val (ip_term, rest) = "10.8.0.255" |> raw_explode |> Scan.finite Symbol.stopper (parser_ipv4 >> mk_ipv4addr);
in
  val _ = if rest <> [] then raise Fail "did not parse everything" else writeln "parsed";
  val _ = if
            Code_Evaluation.dynamic_value_strict @{context} ip_term
            <> @{term "168296703::ipv4addr"}
          then
            raise Fail "parser failed"
          else
            writeln "test passed";
end;
\<close>


subsection\<open>IPv6 Parser\<close>

  definition mk_ipv6addr :: "16 word option list \<Rightarrow> ipv6addr_syntax option" where
    "mk_ipv6addr partslist = (
      let (*remove empty lists to the beginning and end if omission occurs at start/end
            to join over ':' properly *)
          fix_start = (\<lambda>ps. case ps of None#None#_ \<Rightarrow> tl ps | _ \<Rightarrow> ps);
          fix_end = (\<lambda>ps. case rev ps of None#None#_ \<Rightarrow> butlast ps | _ \<Rightarrow> ps);
          ps = (fix_end \<circ> fix_start) partslist
      in
      if length (filter (\<lambda>p. p = None) ps) = 1
      then ipv6_unparsed_compressed_to_preferred ps
      else case ps of [Some a,Some b,Some c,Some d,Some e,Some f,Some g,Some h]
                              \<Rightarrow> Some (IPv6AddrPreferred a b c d e f g h)
                   |  _ \<Rightarrow> None
      )"


ML\<open>
local
  val fromHexString = StringCvt.scanString (Int.scan StringCvt.HEX);

  fun extract_int ss = case ss of "" => NONE
                               |  xs =>
                          case xs |> fromHexString
                                of SOME i => SOME i
                                |  NONE   => raise Fail "unparsable int";
in
  val mk_ipv6addr = map (fn p => case p of NONE => @{const None ("16 word")}
                                        |  SOME i => @{const Some ("16 word")} $
                                                      (@{const word_of_int (16)} $
                                                                  HOLogic.mk_number HOLogic.intT i)
                        )
                 #> HOLogic.mk_list @{typ "16 word option"}
                 (*TODO: never use THE! is there some option_dest?*)
                 #> (fn x => @{const ipv6preferred_to_int} $
                                   (@{const the ("ipv6addr_syntax")} $ (@{const mk_ipv6addr} $ x)));

  val parser_ipv6 = Scan.many1 (fn x => Symbol.is_ascii_hex x orelse x = ":")
                      >> (implode #> space_explode ":" #> map extract_int)
                  (* a different implementation which returns a list of exploded strings:
                    Scan.repeat ((Scan.many Symbol.is_ascii_hex >> extract_int) --| ($$ ":"))
                   @@@ (Scan.many Symbol.is_ascii_hex >> extract_int >> (fn p => [p]))*)
end;

local
  val parse_ipv6 = raw_explode
                   #> Scan.finite Symbol.stopper (parser_ipv6 >> mk_ipv6addr);
  fun unit_test (ip_string, ip_result) = let
    val (ip_term, rest) = ip_string |> parse_ipv6;
    val _ = if rest <> [] then raise Fail "did not parse everything" else ();
    val _ = Code_Evaluation.dynamic_value_strict @{context} ip_term |> Syntax.pretty_term @{context} |> Pretty.writeln;
    val _ = if
              Code_Evaluation.dynamic_value_strict @{context} ip_term <> ip_result
            then
              raise Fail "parser failed"
            else
              writeln ("test passed for "^ip_string);
  in
    ()
  end;
in
  val _ = map unit_test
          [("10:ab:FF:0::FF:4:255", @{term "83090298060623265259947972050027093::ipv6addr"})
          ,("2001:db8::8:800:200c:417a", @{term "42540766411282592856906245548098208122::ipv6addr"})
          ,("ff01::101", @{term "338958331222012082418099330867817087233::ipv6addr"})
          ,("::8:800:200c:417a", @{term "2260596444381562::ipv6addr"})
          ,("2001:db8::", @{term "42540766411282592856903984951653826560::ipv6addr"})
          ,("ff00::", @{term "338953138925153547590470800371487866880::ipv6addr"})
          ,("fe80::", @{term "338288524927261089654018896841347694592::ipv6addr"})
          ,("1::", @{term "5192296858534827628530496329220096::ipv6addr"})
          ,("1::", @{term "5192296858534827628530496329220096::ipv6addr"})
          ,("::", @{term "0::ipv6addr"})
          ,("::1", @{term "1::ipv6addr"})
          ,("2001:db8:0:1:1:1:1:1", @{term "42540766411282592875351010504635121665::ipv6addr"})
          ,("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff", @{term "340282366920938463463374607431768211455::ipv6addr"})
          ];
end;
\<close>
end
