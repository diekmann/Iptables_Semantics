theory IpAddr_toString
imports IPAddr IPv4Addr IPv6Addr
        Lib_Word_toString
begin

section\<open>Pretty Printing IP Addresses\<close>

subsection\<open>Generic Pretty Printer\<close>

  text\<open>Generic function. Whenever possible, use IPv4 or IPv6 pretty printing!\<close>
  definition ipaddr_generic_toString :: "'i::len word \<Rightarrow> string" where
    "ipaddr_generic_toString ip \<equiv>
      ''[IP address ('' @ string_of_nat (len_of TYPE('i)) @ '' bit): '' @ dec_string_of_word0 ip @ '']''"
  
  lemma "ipaddr_generic_toString (ipv4addr_of_dotdecimal (192,168,0,1)) = ''[IP address (32 bit): 3232235521]''" by eval


subsection\<open>IPv4 Pretty Printing\<close>

  fun dotteddecimal_toString :: "nat \<times> nat \<times> nat \<times> nat \<Rightarrow> string" where
    "dotteddecimal_toString (a,b,c,d) = string_of_nat a@''.''@string_of_nat b@''.''@string_of_nat c@''.''@string_of_nat d"
  
  definition ipv4addr_toString :: "ipv4addr \<Rightarrow> string" where
    "ipv4addr_toString ip = dotteddecimal_toString (dotdecimal_of_ipv4addr ip)"

  lemma "ipv4addr_toString (ipv4addr_of_dotdecimal (192, 168, 0, 1)) = ''192.168.0.1''" by eval

  text\<open>Correctness Theorems:\<close>
  thm dotdecimal_of_ipv4addr_ipv4addr_of_dotdecimal
      ipv4addr_of_dotdecimal_dotdecimal_of_ipv4addr

--\<open>Example parser\<close>
ML_val\<open>
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
  
  fun mk_ipv4addr ip = @{const ipv4addr_of_dotdecimal} $ mk_quadrupel ip;

  val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int);

in
  val (ip_term, rest) = "10.8.0.255" |> raw_explode |> Scan.finite Symbol.stopper (parser_ip >> mk_ipv4addr);
  val _ = if rest <> [] then raise Fail "did not parse everything" else writeln "parsed";
  val _ = if
            Code_Evaluation.dynamic_value_strict @{context} ip_term
            <> @{term "168296703::ipv4addr"}
          then
            raise Fail "parser failed"
          else
            writeln "test passed";
end
\<close>


subsection\<open>IPv6 Pretty Printing\<close>

  definition ipv6addr_toString :: "ipv6addr \<Rightarrow> string" where
    "ipv6addr_toString ip = (
      let partslist = ipv6_preferred_to_compressed (int_to_ipv6preferred ip);
          (*add empty lists to the beginning and end if omission occurs at start/end
            to join over ':' properly *)
          fix_start = (\<lambda>ps. case ps of None#_ \<Rightarrow> None#ps | _ \<Rightarrow> ps);
          fix_end = (\<lambda>ps. case rev ps of None#_ \<Rightarrow> ps@[None] | _ \<Rightarrow> ps)
      in list_separated_toString '':''
        (\<lambda>pt. case pt of None \<Rightarrow> ''''
                      |  Some w \<Rightarrow> hex_string_of_word0 w)
        ((fix_end \<circ> fix_start) partslist)
      )"
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xDB8 0x0 0x0 0x8 0x800 0x200C 0x417A))
              = ''2001:db8::8:800:200c:417a''" by eval --\<open>a unicast address\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0xFF01 0x0 0x0 0x0 0x0 0x0 0x0 0x0101)) =
              ''ff01::101''" by eval --\<open>a multicast address\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0 0 0 0 0x8 0x800 0x200C 0x417A)) =
               ''::8:800:200c:417a''" by eval
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xDB8 0 0 0 0 0 0)) =
               ''2001:db8::''" by eval 
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0xFF00 0 0 0 0 0 0 0)) =
               ''ff00::''" by eval --\<open>Multicast\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0xFE80 0 0 0 0 0 0 0)) =
               ''fe80::''" by eval --\<open>Link-Local unicast\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0 0 0 0 0 0 0 0)) =
               ''::''" by eval --\<open>unspecified address\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0 0 0 0 0 0 0 1)) =
               ''::1''" by eval --\<open>loopback address\<close>
  
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xdb8 0x0 0x1 0x1 0x1 0x1 0x1)) =
              ''2001:db8:0:1:1:1:1:1''" by eval --\<open>Section 4.2.2 of RFC5952\<close>

  lemma "ipv6addr_toString max_ipv6_addr = ''ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff''" by eval
  lemma "ipv6addr_toString (ipv6preferred_to_int (IPv6AddrPreferred 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff 0xffff)) =
              ''ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff''" by eval


  text\<open>Correctness Theorems:\<close>
  thm ipv6_preferred_to_compressed
      ipv6_preferred_to_compressed_RFC_4291_format
      ipv6_unparsed_compressed_to_preferred_identity1
      ipv6_unparsed_compressed_to_preferred_identity2
      RFC_4291_format
      ipv6preferred_to_int_int_to_ipv6preferred
      int_to_ipv6preferred_ipv6preferred_to_int


--\<open>DRAFT: Example parser\<close>

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

(*TODO: parser for compressed and preferred is needed! Does it handle all cases, e.g. :: or ::1 or 1:: correctly?*)
(*TODO: HOLogic.mk_nat makes a large SucSucSuc mess! jvm ran out of memory once*)
(*TODO: does not work for large numbers*)
ML_val\<open>
local
  
  val fromHexString = StringCvt.scanString (Int.scan StringCvt.HEX);

  fun extract_int ss = case ss of [] => NONE
                               |  xs =>
                          case xs |> implode |> fromHexString
                                of SOME i => SOME i
                                |  NONE   => raise Fail "unparsable int";


  val mk_ipv6addr = map (fn p => case p of NONE => @{const None ("16 word")}
                                        |  SOME i => @{const Some ("16 word")} $ (@{const of_nat ("16 word")} $ HOLogic.mk_nat i))
                 #> HOLogic.mk_list @{typ "16 word option"}
                 (*TODO: is there a nicer way?*)
                 (*TODO: never use THE!*)
                 #> (fn x => @{const ipv6preferred_to_int} $ (@{const the ("ipv6addr_syntax")} $ (@{const mk_ipv6addr} $ x)));

  (*TODO: I just want to split at ':'. There must be a better way to achieve this!*)
  val parser_ip = Scan.repeat ((Scan.many Symbol.is_ascii_hex >> extract_int) --| ($$ ":"))
                   @@@ (Scan.many Symbol.is_ascii_hex >> extract_int >> (fn p => [p]))

in
  val parse = raw_explode
              #> Scan.finite Symbol.stopper (parser_ip >> mk_ipv6addr);
  fun unit_test (ip_string, ip_result) = let
    val (ip_term, rest) = ip_string |> parse;
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
end
\<close>
end