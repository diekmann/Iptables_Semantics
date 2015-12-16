theory Parser
imports Code_Interface
  keywords "parse_iptables_save"::thy_decl
begin


context
begin
  private definition is_pos_Extra :: "common_primitive negation_type \<Rightarrow> bool" where
    "is_pos_Extra a \<equiv> (case a of Pos (Extra _) \<Rightarrow> True | _ \<Rightarrow> False)"
  private definition get_pos_Extra :: "common_primitive negation_type \<Rightarrow> string" where
    "get_pos_Extra a \<equiv> (case a of Pos (Extra e) \<Rightarrow> e | _ \<Rightarrow> undefined)"
  
  fun compress_parsed_extra :: "common_primitive negation_type list \<Rightarrow> common_primitive negation_type list" where
    "compress_parsed_extra [] = []" |
    "compress_parsed_extra (a1#a2#as) = (if is_pos_Extra a1 \<and> is_pos_Extra a2
        then compress_parsed_extra (Pos (Extra (get_pos_Extra a1@'' ''@get_pos_Extra a2))#as)
        else a1#compress_parsed_extra (a2#as)
        )" |
    "compress_parsed_extra (a#as) = a#compress_parsed_extra as"
  
  value "compress_parsed_extra
    (map Pos [Extra ''-m'', Extra ''recent'', Extra ''--update'', Extra ''--seconds'', Extra ''60'', IIface (Iface ''foobar''),
              Extra ''--name'', Extra ''DEFAULT'', Extra ''--rsource''])"
  
  private lemma eval_ternary_And_Unknown_Unkown: "eval_ternary_And TernaryUnknown (eval_ternary_And TernaryUnknown tv) = (eval_ternary_And TernaryUnknown tv)"
    by(cases tv) (simp_all)
  
  private lemma is_pos_Extra_alist_and: "is_pos_Extra a \<Longrightarrow> alist_and (a#as) = MatchAnd (Match (Extra (get_pos_Extra a))) (alist_and as)"
    apply(cases a)
     apply(simp_all add: get_pos_Extra_def is_pos_Extra_def)
    apply(rename_tac e)
    by(case_tac e)(simp_all)
  
  private lemma compress_parsed_extra_matchexpr_helper: "ternary_ternary_eval (map_match_tac common_matcher p (alist_and (compress_parsed_extra as))) =
         ternary_ternary_eval (map_match_tac common_matcher p (alist_and as))"
   apply(induction as rule: compress_parsed_extra.induct)
     apply(simp_all split: match_expr.split match_expr.split_asm common_primitive.split)
   apply(simp_all add: is_pos_Extra_alist_and)
   apply(safe)
     apply(simp_all add: eval_ternary_And_Unknown_Unkown bool_to_ternary_simps)
    apply(rename_tac a1 a2 as)
    apply(case_tac [!] a1)
      apply(simp_all)
   done
  
  text{*This lemma justifies that it is okay to fold together the parsed unknown tokens*}
  lemma compress_parsed_extra_matchexpr: "matches (common_matcher, \<alpha>) (alist_and (compress_parsed_extra as)) = matches (common_matcher, \<alpha>) (alist_and as)"
    apply(simp add: fun_eq_iff)
    apply(intro allI)
    apply(rule matches_iff_apply_f)
    apply(simp add: compress_parsed_extra_matchexpr_helper)
    done

  text{*This version of @{const alist_and} avoids the trailing @{const MatchAny}*}
  fun alist_and' :: "'a negation_type list \<Rightarrow> 'a match_expr" where
    "alist_and' [] = MatchAny" |
    "alist_and' [Pos e] = Match e" |
    "alist_and' [Neg e] = MatchNot (Match e)"|
    "alist_and' ((Pos e)#es) = MatchAnd (Match e) (alist_and' es)" |
    "alist_and' ((Neg e)#es) = MatchAnd (MatchNot (Match e)) (alist_and' es)"

  lemma alist_and': "matches (\<gamma>, \<alpha>) (alist_and' as) = matches (\<gamma>, \<alpha>) (alist_and as)"
    by(induction as rule: alist_and'.induct) (simp_all add: bunch_of_lemmata_about_matches)
end



ML{* (*my personal small library*)
fun takeWhile p xs = fst (take_prefix p xs);

fun dropWhile p xs = snd (take_prefix p xs);

fun dropWhileInclusive p xs = drop 1 (dropWhile p xs)

(*split at the predicate, do NOT keep the position where it was split*)
fun split_at p xs = (takeWhile p xs, dropWhileInclusive p xs);
*}

ML_val{*
split_at (fn x => x <> " ") (raw_explode "foo bar")
*}


section{*An SML Parser for iptables-save*}
text{*Work in Progress*}


ML{*
local
  fun is_start_of_table table s = s = ("*"^table);
  fun is_end_of_table s = s = "COMMIT";

  fun load_file (thy: theory) (path: string list) =
      let val p =  File.full_path (Resources.master_directory thy) (Path.make path); in
      let val _ = "loading file "^File.platform_path p |> writeln; in
        if not (File.exists p) orelse (File.is_dir p) then raise Fail "File not found" else File.read_lines p
      end end;

  fun extract_table _ [] = []
   |  extract_table table (r::rs) = if not (is_start_of_table table r) then extract_table table rs else
                                     takeWhile (fn x => not (is_end_of_table x)) rs

  fun writenumloaded table_name table =
    let val _ = "Loaded "^ Int.toString (length table) ^" lines of the "^table_name^" table" |> writeln; in
      table
    end;
in
  fun load_table table thy = load_file thy #> extract_table table #> writenumloaded table;
  val load_filter_table = load_table "filter";
end;
*}


ML{*
(*keep quoted strings as one token*)
local
  fun collapse_quotes [] = []
   |  collapse_quotes ("\""::ss) = let val (quoted, rest) = split_at (fn x => x <> "\"") ss in
                                          "\"" ^ implode quoted^"\"" :: rest end
   |  collapse_quotes (s::ss) = s :: collapse_quotes ss;
in
  val ipt_explode = raw_explode #> collapse_quotes;
end
*}
ML_val{*
ipt_explode "ad \"as das\" boo";
ipt_explode "ad \"foobar --boo boo";
*}


ML{*
datatype parsed_action_type = TypeCall | TypeGoto
datatype parsed_match_action = ParsedMatch of term | ParsedNegatedMatch of term | ParsedAction of parsed_action_type * string;
local (*iptables-save parsers*)
  val is_whitespace = Scan.many (fn x => x = " ");
  
  local (*parser for matches*)
    local
      fun extract_int ss = case ss |> implode |> Int.fromString of SOME i => i
                                                                 | NONE => raise Fail "unparsable int";
    
      fun is_iface_char x = Symbol.is_ascii x andalso
          (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "+" orelse x = "*" orelse x = ".")
    in
      fun mk_nat maxval i = if i < 0 orelse i > maxval
                then
                  raise Fail("nat ("^Int.toString i^") must be between 0 and "^Int.toString maxval)
                else (HOLogic.mk_number HOLogic.natT i);
      val mk_nat255 = mk_nat 255;
    
      fun mk_quadrupel (((a,b),c),d) = HOLogic.mk_prod
               (mk_nat255 a, HOLogic.mk_prod (mk_nat255 b, HOLogic.mk_prod (mk_nat255 c, mk_nat255 d)));
    
      fun ipNetmask_to_hol (ip,len) = @{const Ip4AddrNetmask} $ mk_quadrupel ip $ mk_nat 32 len;
      fun ipRange_to_hol (ip1,ip2) = @{const Ip4AddrRange} $ mk_quadrupel ip1 $ mk_quadrupel ip2;
    
      val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int);
      
      val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ipNetmask_to_hol;

      val parser_ip_range = parser_ip --| ($$ "-") -- parser_ip >> ipRange_to_hol;

      val parser_ip_addr = parser_ip >> (fn ip => @{const Ip4Addr} $ mk_quadrupel ip);
    
      val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => @{const Iface} $ HOLogic.mk_string x));

      val parser_protocol = Scan.this_string "tcp" >> K @{const primitive_protocol.TCP}
                         || Scan.this_string "udp" >> K @{const primitive_protocol.UDP}
                         || Scan.this_string "icmp" >> K @{const primitive_protocol.ICMP}
                         (*Moar Assigned Internet Protocol Numbers below: *)
                         || Scan.this_string "esp" >> K @{term "primitive_protocol.OtherProtocol 50"}
                         || Scan.this_string "ah" >> K @{term "primitive_protocol.OtherProtocol 51"}
                         || Scan.this_string "gre" >> K @{term "primitive_protocol.OtherProtocol 47"}

      val parser_ctstate = Scan.this_string "NEW" >> K @{const CT_New}
                         || Scan.this_string "ESTABLISHED" >> K @{const CT_Established}
                         || Scan.this_string "RELATED" >> K @{const CT_Related}
                         || Scan.this_string "UNTRACKED" >> K @{const CT_Untracked}
                         || Scan.this_string "INVALID" >> K @{const CT_Invalid}

      val parser_tcp_flag = Scan.this_string "SYN" >> K @{const TCP_SYN}
                         || Scan.this_string "ACK" >> K @{const TCP_ACK}
                         || Scan.this_string "FIN" >> K @{const TCP_FIN}
                         || Scan.this_string "RST" >> K @{const TCP_RST}
                         || Scan.this_string "URG" >> K @{const TCP_URG}
                         || Scan.this_string "PSH" >> K @{const TCP_PSH}

      fun parse_comma_separated_list parser = Scan.repeat (parser --| $$ ",") @@@ (parser >> (fn p => [p]))

      local
        val mk_port_single = mk_nat 65535 #> (fn n => @{const nat_to_16word} $ n)
        val parse_port_raw = Scan.many1 Symbol.is_ascii_digit >> extract_int
        fun port_tuple_warn (p1,p2) = if p1 >= p2 then let val _= writeln ("WARNING (in ports): "^Int.toString p1^" >= "^Int.toString p2) in (p1, p2) end else (p1, p2);
      in
        val parser_port_single_tup = (
                 (parse_port_raw --| $$ ":" -- parse_port_raw) >> (port_tuple_warn #> (fn (p1,p2) => (mk_port_single p1, mk_port_single p2)))
              || (parse_port_raw  >> (fn p => (mk_port_single p, mk_port_single p)))
            ) >> HOLogic.mk_prod
        end
      val parser_port_single_tup_term = parser_port_single_tup >> ((fn x => [x]) #> HOLogic.mk_list @{typ "16 word \<times> 16 word"})

      val parser_port_many1_tup = parse_comma_separated_list parser_port_single_tup >> HOLogic.mk_list @{typ "16 word \<times> 16 word"}

      val parser_ctstate_set = parse_comma_separated_list parser_ctstate >> HOLogic.mk_set @{typ "ctstate"}

      val parser_tcp_flag_set = parse_comma_separated_list parser_tcp_flag >> HOLogic.mk_set @{typ "tcp_flag"}

      val parser_tcp_flags = (parser_tcp_flag_set --| $$ " " -- parser_tcp_flag_set) >> (fn (m,c) => @{const TCP_Flags} $ m $ c)

      val parser_extra = Scan.many1 (fn x => x <> " " andalso Symbol.not_eof x) >> (implode #> HOLogic.mk_string);
    end;
    fun parse_cmd_option_generic (d: term -> parsed_match_action) (s: string) (t: term) (parser: string list -> (term * string list)) = 
        Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string s |-- (parser >> (fn r => d (t $ r))))

    fun parse_cmd_option (s: string) (t: term) (parser: string list -> (term * string list)) =  parse_cmd_option_generic ParsedMatch s t parser;

    (*both negated and not negated primitives*)
    fun parse_cmd_option_negated (s: string) (t: term) (parser: string list -> (term * string list)) =
          parse_cmd_option_generic ParsedNegatedMatch ("! "^s) t parser || parse_cmd_option s t parser;

    fun parse_cmd_option_negated_singleton s t parser = parse_cmd_option_negated s t parser >> (fn x => [x])

    (*TODO: is the 'Scan.finite Symbol.stopper' correct here?*)
    fun parse_with_module_prefix (module: string) (parser: (string list -> parsed_match_action * string list)) =
      (Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string module)) |-- (Scan.repeat parser)
  in

    val parse_ips = parse_cmd_option_negated_singleton "-s " @{const Src} (parser_ip_cidr || parser_ip_addr)
                 || parse_cmd_option_negated_singleton "-d " @{const Dst} (parser_ip_cidr || parser_ip_addr);

                            
    val parse_iprange = parse_with_module_prefix "-m iprange " (parse_cmd_option_negated "--src-range " @{const Src} parser_ip_range
                                                             || parse_cmd_option_negated "--dst-range " @{const Dst} parser_ip_range); 
    
    val parse_iface = parse_cmd_option_negated_singleton "-i " @{const IIface} parser_interface
                   || parse_cmd_option_negated_singleton "-o " @{const OIface} parser_interface;

    val parse_protocol = parse_cmd_option_negated_singleton "-p " @{term "Prot \<circ> Proto"} parser_protocol; (*negated?*)

    (*-m tcp requires that there is already an -p tcp, iptables checks that for you, we assume valid iptables-save (otherwise the kernel would not load it)*)
    val parse_tcp_options =
             parse_with_module_prefix "-m tcp " (parse_cmd_option_negated "--sport " @{const Src_Ports} parser_port_single_tup_term
                                              || parse_cmd_option_negated "--dport " @{const Dst_Ports} parser_port_single_tup_term
                                              || parse_cmd_option_negated "--tcp-flags " @{const L4_Flags} parser_tcp_flags);
    val parse_multiports = 
             parse_with_module_prefix "-m multiport " (parse_cmd_option_negated "--sports " @{const Src_Ports} parser_port_many1_tup
                                                    || parse_cmd_option_negated "--dports " @{const Dst_Ports} parser_port_many1_tup);
    val parse_udp_options = 
             parse_with_module_prefix "-m udp " (parse_cmd_option_negated "--sport " @{const Src_Ports} parser_port_single_tup_term
                                              || parse_cmd_option_negated "--dport " @{const Dst_Ports} parser_port_single_tup_term);

    val parse_ctstate = parse_with_module_prefix "-m state " (parse_cmd_option_negated "--state " @{term "CT_State"} parser_ctstate_set)
                     || parse_with_module_prefix "-m conntrack " (parse_cmd_option_negated "--ctstate " @{term "CT_State"} parser_ctstate_set);
    
     (*TODO: it would be good to fail if there is a "!" in the extra; it might be an unparsed negation*)
    val parse_unknown = (parse_cmd_option "" @{const Extra} parser_extra) >> (fn x => [x]);
  end;
  
  
  local (*parser for target/action*)
    fun is_target_char x = Symbol.is_ascii x andalso
        (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "-" orelse x = "_" orelse x = "~")

    fun parse_finite_skipwhite parser = Scan.finite Symbol.stopper (is_whitespace |-- parser);

    val is_icmp_type = fn x => Symbol.is_ascii_letter x orelse x = "-"
  in
    val parser_target = Scan.many1 is_target_char >> implode;
  
    (*parses: -j MY_CUSTOM_CHAIN*)
    (*The -j may not be the end of the line. example: -j LOG --log-prefix "[IPT_DROP]:"*)
    val parse_target_generic : (string list -> parsed_match_action * string list) =  parse_finite_skipwhite
      (Scan.this_string "-j " |-- (parser_target >> (fn s => ParsedAction (TypeCall, s))));

    (*parses: REJECT --reject-with type*)
    val parse_target_reject : (string list -> parsed_match_action * string list) =  parse_finite_skipwhite
      (Scan.this_string "-j " |-- (Scan.this_string "REJECT" >> (fn s => ParsedAction (TypeCall, s)))
       --| ((Scan.this_string " --reject-with " --| Scan.many1 is_icmp_type) || Scan.this_string ""));


    val parse_target_goto : (string list -> parsed_match_action * string list) = parse_finite_skipwhite
      (Scan.this_string "-g " |-- (parser_target >> (fn s => let val _ = writeln ("WARNING: goto in `"^s^"'") in ParsedAction (TypeGoto, s) end)));

    val parse_target : (string list -> parsed_match_action * string list) = parse_target_reject || parse_target_goto || parse_target_generic;
  end;
in
  (*parses: -A FORWARD*)
  val parse_table_append : (string list -> (string * string list)) = Scan.this_string "-A " |-- parser_target --| is_whitespace;

  (*parses: -s 0.31.123.213/88 --foo_bar -j chain --foobar
   First tries to parse a known field, afterwards, it parses something unknown until a blank space appears
  *)
  val option_parser : (string list -> (parsed_match_action list) * string list) = 
      Scan.recover (parse_ips || parse_iprange
                 || parse_iface
                 || parse_protocol
                 || parse_tcp_options || parse_udp_options || parse_multiports
                 || parse_ctstate
                 || parse_target >> (fn x => [x])) (K parse_unknown);
  
  
  (*parse_table_append should be called before option_parser, otherwise -A will simply be an unknown for option_parser*)
  
  local
    (*:DOS_PROTECT - [0:0]*)
    val custom_chain_decl_parser = ($$ ":") |-- parser_target --| Scan.this_string " - " #> fst;
    (*:INPUT ACCEPT [130:12050]*)
    (*TODO: PREROUTING is only valid if we are in the raw table*)
    val builtin_chain_decl_parser = ($$ ":") |--
      (Scan.this_string "INPUT" || Scan.this_string "FORWARD" || Scan.this_string "OUTPUT" || Scan.this_string "PREROUTING") --|
      ($$ " ") -- (Scan.this_string "ACCEPT" || Scan.this_string "DROP") --| ($$ " ") #> fst;
    val wrap_builtin_chain = (fn (name, policy) => (name, SOME policy));
    val wrap_custom_chain = (fn name => (name, NONE));
  in
    val chain_decl_parser : (string list -> string * string option) =
          Scan.recover (builtin_chain_decl_parser #> wrap_builtin_chain) (K (custom_chain_decl_parser #> wrap_custom_chain));
  end
end;
*}


(*TODO: is there a library function for this?*)
ML{*
local
  fun concat [] = []
   | concat (x :: xs) = x @ concat xs;
in
fun Scan_cons_repeat (parser: ('a -> 'b list * 'a)) (s: 'a) : ('b list * 'a) =
    let val (x, rest) = Scan.repeat parser s in (concat x, rest) end;
end
*}

ML_val{*(Scan_cons_repeat option_parser) (ipt_explode "-i lup -j net-fw")*}
ML_val{*(Scan_cons_repeat option_parser) (ipt_explode "")*}
ML_val{*(Scan_cons_repeat option_parser) (ipt_explode "-i lup foo")*}
ML_val{*(Scan_cons_repeat option_parser) (ipt_explode "-m tcp --dport 22 --sport 88")*}
ML_val{*(Scan_cons_repeat option_parser) (ipt_explode "-j LOG --log-prefix \"Shorewall:INPUT:REJECT:\" --log-level 6")*}


ML_val{*
val (x, rest) = (Scan_cons_repeat option_parser) (ipt_explode "-d 0.31.123.213/88 --foo_bar \"he he\" -f -i eth0+ -s 0.31.123.213/21 moreextra -j foobar --log");
map (fn p => case p of ParsedMatch t => type_of t | ParsedAction (_,_) => dummyT) x;
map (fn p => case p of ParsedMatch t => Pretty.writeln (Syntax.pretty_term @{context} t) | ParsedAction (_,a) => writeln ("action: "^a)) x;
*}

ML{*
local
  fun parse_rule_options (s: string list) : parsed_match_action list = let val (parsed, rest) = (case try (Scan.catch (Scan_cons_repeat option_parser)) s of SOME x => x | NONE => raise Fail "scanning")
            in
            if rest <> []
            then
              raise Fail ("Unparsed: `"^implode rest^"'")
            else
              parsed
            end
            handle Fail m => raise Fail ("parse_rule_options: "^m^" for rule `"^implode s^"'");

   fun get_target (ps : parsed_match_action list) : (parsed_action_type * string) option = let val actions = List.mapPartial (fn p => case p of ParsedAction a => SOME a | _ => NONE) ps
      in case actions of [] => NONE
                      |  [action] => SOME action
                      | _ => raise Fail "there can be at most one target"
      end;

   val get_matches : (parsed_match_action list -> term) =
        List.mapPartial (fn p => case p of
                            ParsedMatch m => SOME (@{const Pos (common_primitive)} $ m)
                          | ParsedNegatedMatch m => SOME (@{const Neg (common_primitive)} $ m)
                          | ParsedAction _ => NONE)
                         #> HOLogic.mk_list @{typ "common_primitive negation_type"};


   (*returns: (chainname the rule was appended to, target, matches)*)
   fun parse_rule (s: string) : (string * (parsed_action_type * string) option * term) = let
      val (chainname, rest) =
        (case try (ipt_explode #> Scan.finite Symbol.stopper parse_table_append) s of SOME x => x | NONE => raise Fail ("parse_rule: parse_table_append: "^s))
      in let val parsed = parse_rule_options rest in
        (chainname, get_target parsed, get_matches parsed)
      end end;
in
  (*returns (parsed chain declarations, parsed appended rules*)
  fun rule_type_partition (rs : string list) : ((string * string option) list * (string * (parsed_action_type * string) option * term) list) =
      let val (chain_decl, rules) = List.partition (String.isPrefix ":") rs in
      if not (List.all (String.isPrefix "-A") rules) then raise Fail "could not partition rules" else
        let val parsed_chain_decls = (case try (map (ipt_explode #> chain_decl_parser)) chain_decl of SOME x => x | NONE =>
                                                      raise Fail ("could not parse chain declarations: "^implode chain_decl)) in
        let val parsed_rules = map parse_rule rules in
            let val  _ = "Parsed "^ Int.toString (length parsed_chain_decls) ^" chain declarations" |> writeln in
            let val  _ = "Parsed "^ Int.toString (length parsed_rules) ^" rules" |> writeln in
              (parsed_chain_decls, parsed_rules)
            end end end end
      end
   fun get_chain_decls_policy (ls: ((string * string option) list * (string * (parsed_action_type * string) option * term) list)) = fst ls
   fun get_parsed_rules (ls: ((string * string option) list * (string * (parsed_action_type * string) option * term) list)) = snd ls
   val filter_chain_decls_names_only : 
         ((string * string option) list * (string * (parsed_action_type * string) option * term) list) ->
           (string list * (string * (parsed_action_type * string) option * term) list) = (fn (a,b) => (map fst a, b))
end;
*}


ML{* (*create a table with the firewall definition*)
structure FirewallTable = Table(type key = string; val ord = Library.string_ord);
type firewall_table = term list FirewallTable.table;

local
  (* Initialize the table. Create a key for every declared chain. *)
  fun FirewallTable_init chain_decls : firewall_table = fold (fn entry => fn accu => FirewallTable.update_new (entry, []) accu) chain_decls FirewallTable.empty;
  
  (* this takes like forever! *)
  (* apply compress_parsed_extra here?*)
  fun hacky_hack t = (*Code_Evaluation.dynamic_value_strict @{context} (@{const compress_extra} $ t)*)
    @{const alist_and' ("common_primitive")} $ (@{const compress_parsed_extra} $ t)
  
  fun mk_MatchExpr t = if fastype_of t <> @{typ "common_primitive negation_type list"} then raise Fail "Type Error" else hacky_hack t;
  fun mk_Rule_help t a = let val r = @{const Rule (common_primitive)} $ (mk_MatchExpr t) $ a in
      if fastype_of r <> @{typ "common_primitive rule"} then raise Fail "Type error in mk_Rule_help"
      else r end;
  
  fun append table chain rule = case FirewallTable.lookup table chain
      of NONE => raise Fail ("uninitialized cahin: "^chain)
      |  SOME rules => FirewallTable.update (chain, rules@[rule]) table
  
  fun mk_Rule (tbl: firewall_table) (chain: string, target : (parsed_action_type * string) option, t : term) =
    if not (FirewallTable.defined tbl chain) then raise Fail ("undefined chain to be appended: "^chain) else
    case target
    of NONE => mk_Rule_help t @{const action.Empty}
     | SOME (TypeCall, "ACCEPT") => mk_Rule_help t @{const action.Accept}
     | SOME (TypeCall, "DROP") => mk_Rule_help t @{const action.Drop}
     | SOME (TypeCall, "REJECT") => mk_Rule_help t @{const action.Reject}
     | SOME (TypeCall, "LOG") => mk_Rule_help t @{const action.Log}
     | SOME (TypeCall, "RETURN") => mk_Rule_help t @{const action.Return}
     | SOME (TypeCall, custom) => if not (FirewallTable.defined tbl custom) then raise Fail ("unknown action: "^custom) else
                      mk_Rule_help t (@{const action.Call} $ HOLogic.mk_string custom)
     | SOME (TypeGoto, "ACCEPT") => raise Fail "Unexpected"
     | SOME (TypeGoto, "DROP") => raise Fail "Unexpected"
     | SOME (TypeGoto, "REJECT") => raise Fail "Unexpected"
     | SOME (TypeGoto, "LOG") => raise Fail "Unexpected"
     | SOME (TypeGoto, "RETURN") => raise Fail "Unexpected"
     | SOME (TypeGoto, custom) => if not (FirewallTable.defined tbl custom) then raise Fail ("unknown action: "^custom) else
                      mk_Rule_help t (@{const action.Goto} $ HOLogic.mk_string custom);
  
  (*val init = FirewallTable_init parsed_chain_decls;*)
  (*map type_of (map (mk_Rule init) parsed_rules);*)

in
  local
    fun append_rule (tbl: firewall_table) (chain: string, target : (parsed_action_type * string) option, t : term) = append tbl chain (mk_Rule tbl (chain, target, t))
  in
    fun make_firewall_table (parsed_chain_decls : string list, parsed_rules : (string * (parsed_action_type * string) option * term) list) = 
      fold (fn rule => fn accu => append_rule accu rule) parsed_rules (FirewallTable_init parsed_chain_decls);
  end
end
*}



(*TODO: think about the path handling in the parser again*)
(*
ML_val{* (*Example: the functions*)
val filter_table = load_filter_table @{theory} ["../", "Examples", "Parser_Test", "data", "iptables-save"];
val parsed_ruleset = filter_table |> rule_type_partition |> filter_chain_decls_names_only |> make_firewall_table;

val (parsed_chain_decls, parsed_rules) = rule_type_partition filter_table;

val toString = (fn (a,target,b) => "-A "^a^" "^((Syntax.pretty_term @{context} #> Pretty.string_of) b)^(case target of NONE => "" | SOME (TypeCall, t) => " -j "^t | SOME (TypeGoto, t) => " -g "^t));
map (toString #> writeln) parsed_rules;

map (fn (_,_,b) =>  type_of b) parsed_rules;
*}
*)

ML{*
fun mk_Ruleset (tbl: firewall_table) = FirewallTable.dest tbl
    |> map (fn (k,v) => HOLogic.mk_prod (HOLogic.mk_string k, HOLogic.mk_list @{typ "common_primitive rule"} v))
    |> HOLogic.mk_list @{typ "string \<times> common_primitive rule list"}
*}


(*default policies*)
ML{*
local
  fun default_policy_action_to_term "ACCEPT" = @{const "action.Accept"}
   |  default_policy_action_to_term "DROP" = @{const "action.Drop"}
   |  default_policy_action_to_term a = raise Fail ("Not a valid default policy `"^a^"'")
in
  (*chain_name * default_policy*)
  fun preparedefault_policies [] = []
   |  preparedefault_policies ((chain_name, SOME default_policy)::ls) =
          (chain_name, default_policy_action_to_term default_policy) :: preparedefault_policies ls
   |  preparedefault_policies ((_, NONE)::ls) = preparedefault_policies ls
end
*}


ML{*
fun trace_timing (printstr : string) (f : 'a -> 'b) (a : 'a) : 'b =
  let val t0 = Time.now(); in
    let val result =  f a; in
    let val t1= Time.now(); in
    let val _ = writeln(String.concat [printstr^" (", Time.toString(Time.-(t1,t0)), " seconds)"]) in
      result
    end end end end;

fun simplify_code (ctx: Proof.context) = let val _ = writeln "unfolding (this may take a while) ..." in 
      trace_timing "Simplified term" (Code_Evaluation.dynamic_value_strict ctx)
    end

fun certify_term (ctx: Proof.context) (t: term) = trace_timing "Certified term" (Thm.cterm_of ctx) t
*}


ML_val{*(*Example: putting it all together*)
fun parse_iptables_save (thy: theory) (file: string list) : term = 
    load_filter_table thy file
    |> rule_type_partition
    |> filter_chain_decls_names_only
    |> make_firewall_table
    |> mk_Ruleset
    |> simplify_code @{context}

(*
val example = parse_iptables_save @{theory} ["Parser_Test", "data", "iptables-save"];

Pretty.writeln (Syntax.pretty_term @{context} example);*)
*}


ML{*
local
  fun define_const (t: term) (name: binding) (lthy: local_theory) : local_theory = let
        val _ = writeln ("Defining constant `"^Binding.name_of name^"' ("^Binding.name_of name^"_def')");
        val ((_, (_, thm)), lthy) = Local_Theory.define ((name, NoSyn), ((Binding.empty, []), t)) lthy;
        val (_, lthy) = Local_Theory.note ((Binding.suffix_name "_def" name, @{attributes [code]}), [thm]) lthy;
       in
         lthy
       end

  fun print_default_policies (ps: (string * term) list) = let
      val _ = map (fn (name, _) => if name <> "INPUT" andalso name <> "FORWARD" andalso name <> "OUTPUT" then
                      writeln ("WARNING: the chain `"^name^"' is not a built-in chain of the filter table") else ()) ps
      in ps end;

  fun sanity_check_ruleset t = let
      val check = Code_Evaluation.dynamic_value_strict @{context} (@{const sanity_wf_ruleset (common_primitive)} $ t)
    in
      if check <> @{term "True"} then raise ERROR "sanity_wf_ruleset failed" else t
    end;
in
  fun local_setup_parse_iptables_save (table: string) (name: binding) path lthy =
    let val prepared = path
            |> load_table table (Proof_Context.theory_of lthy)
            |> rule_type_partition in
    let val firewall = prepared
            |> filter_chain_decls_names_only
            |> make_firewall_table
            |> mk_Ruleset
            (*this may a while*)
            |> simplify_code @{context}
            |> trace_timing "checked sanity with sanity_wf_ruleset" sanity_check_ruleset
        val default_policis = prepared
            |> get_chain_decls_policy
            |> preparedefault_policies
            |> print_default_policies
    in
      lthy
      |> define_const firewall name
      |> fold (fn (chain_name, policy) => fn lthy => define_const policy (Binding.name (Binding.name_of name^"_"^chain_name^"_default_policy")) lthy) default_policis
    end end
end
*}


ML\<open>
  Outer_Syntax.local_theory @{command_keyword parse_iptables_save}
  "Load a file generated by iptables-save and make the firewall definition available as isabelle term"
    (Parse.binding --| @{keyword "="} -- Parse.string >> (fn (binding,path) => local_setup_parse_iptables_save "filter" binding [path]))
\<close>



end
