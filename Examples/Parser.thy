theory Parser
imports Code_Interface
begin



fun foldMatchAnd :: "'a list => 'a match_expr" where
  "foldMatchAnd [] = MatchAny" |
  "foldMatchAnd (m#ms) = MatchAnd (Match m) (foldMatchAnd ms)"

lemma "foldMatchAnd as = alist_and (map Pos as)"
  by(induction as)(simp_all)


(*Incomplete: An ML Parser for iptables-save*)

ML{*
fun takeWhile p xs = fst (take_prefix p xs);

fun dropWhile p xs = snd (take_prefix p xs);

fun dropWhileInclusive p xs = drop 1 (dropWhile p xs)

(*split at the predicate, do NOT keep the position where it was split*)
fun split_at p xs = (takeWhile p xs, dropWhileInclusive p xs);
*}
ML_val{*
split_at (fn x => x <> " ") (raw_explode "foo bar")
*}


ML{* (*unused*)
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
*}
ML_val{*
skip_until " -j " (raw_explode "asdf -j foo");
skip_until " -xx " (raw_explode "a -x foo");
*}

ML{*
val path = Path.append Path.root (Path.make ["home", "diekmann", "git", "net-network-private", "iptables-save-2015-05-15_15-23-41"]);
val _ = "loading file "^File.platform_path path |> writeln;
if not (File.exists path) orelse (File.is_dir path) then writeln "Not found" else ();
val iptables_save = File.read_lines path;

local
  fun is_start_of_filter_table s = s = "*filter";
  fun is_end_of_table s = s = "COMMIT";
  (*fun is_comment s = String.isPrefix "#" s*)

in
  fun extract_filter_table [] = []
   |  extract_filter_table (r::rs) = if not (is_start_of_filter_table r) then extract_filter_table rs else
                                     takeWhile (fn x => not (is_end_of_table x)) rs
end;

val filter_table = extract_filter_table iptables_save;

val _ = "Parsed "^ Int.toString (length filter_table) ^" entries" |> writeln;
(*val _ = filter_table |> map writeln;*)
*}


ML{*
String.explode "sasd";
(($$ "a") ::: (Scan.many (fn x => x = "s"))) (raw_explode "asdf");
Scan.this_string "as" (raw_explode "asdf");
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
ipt_explode "ad \"asdas\" boo";
ipt_explode "ad \"foobar --boo boo";
*}

ML{*

local
  fun extract_int ss = case ss |> implode |> Int.fromString of SOME i => i
                                                             | NONE => raise Fail "unparsable int";

  fun is_iface_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "+" orelse x = "*" orelse x = ".")

  fun is_target_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "-" orelse x = "_" orelse x = "~")
in
  (*TODO: assert max size?*)
  fun mk_nat i = (HOLogic.mk_number HOLogic.natT i)

  fun mk_quadrupel (((a,b),c),d) = HOLogic.mk_prod (mk_nat a, HOLogic.mk_prod (mk_nat b, HOLogic.mk_prod (mk_nat c, mk_nat d)));

  fun ip_to_hol (ip,len) = @{const Ip4AddrNetmask} $ mk_quadrupel ip $ mk_nat len;

  val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int);
  
  val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ip_to_hol;

  val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => @{const Iface} $ HOLogic.mk_string x));

  val parser_target = Scan.many1 is_target_char >> implode;

  val parser_extra = Scan.many1 (fn x => x <> " " andalso Symbol.not_eof x) >> (implode #> HOLogic.mk_string);

  val is_whitespace = Scan.many (fn x => x = " ");
end;

datatype parsed_match_action = ParsedMatch of term | ParsedAction of string;

fun parse_cmd_option (s: string) (t: term) (parser: string list -> (term * string list)) = 
    Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string s |-- (parser >> (fn r => ParsedMatch (t $ r))))


val parse_src_ip = parse_cmd_option "-s " @{const Src} parser_ip_cidr;
val parse_dst_ip = parse_cmd_option "-d " @{const Dst} parser_ip_cidr;


val parse_in_iface = parse_cmd_option "-i " @{const IIface} parser_interface;
val parse_out_iface = parse_cmd_option "-o " @{const OIface} parser_interface;

val parse_unknown = parse_cmd_option "" @{const Extra} parser_extra;


(*parses: -A FORWARD*)
val parse_table_append : (string list -> (string * string list)) = Scan.this_string "-A " |-- parser_target --| is_whitespace;


(*parses: -j MY_CUSTOM_CHAIN*)
(*The -j may not be the end of the line. example: -j LOG --log-prefix "[IPT_DROP]:"*)
val parse_target : (string list -> parsed_match_action * string list) = 
              Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string "-j " |-- (parser_target >> ParsedAction ));


(*parses: -s 0.31.123.213/88 --foo_bar -j chain --foobar
 First tries to parse a known field, afterwards, it parses something unknown until a blank space appears
*)
val option_parser : (string list -> (parsed_match_action) * string list) = 
    Scan.recover (parse_src_ip || parse_dst_ip || parse_in_iface || parse_out_iface || parse_target) (K parse_unknown);

(*parse_table_append should be called before option_parser, otherwise -A will simply be an unknown for option_parser*)


(*:INPUT ACCEPT [130:12050]*)
val chain_decl_parser = ($$ ":") |-- parser_target #> fst;
*}


ML_val{*
val (x, rest) = (Scan.repeat option_parser) (ipt_explode "-d 0.31.123.213/88 --foo_bar \"he he\" -f -i eth0+ -s 0.31.123.213/88 moreextra -j foobar --log");
map (fn p => case p of ParsedMatch t => type_of t | ParsedAction _ => dummyT) x;
map (fn p => case p of ParsedMatch t => Pretty.writeln (Syntax.pretty_term @{context} t) | ParsedAction a => writeln ("action: "^a)) x;
*}

ML{*
local
  fun parse_rule_options (s: string list) : parsed_match_action list = let val (parsed, rest) = (Scan.repeat option_parser) s
            in
            if rest <> []
            then
              raise Fail ("Unparsed: "^implode rest)
            else
              parsed
            end;

   fun get_target (ps : parsed_match_action list) : string option = let val actions = List.mapPartial (fn p => case p of ParsedAction a => SOME a | _ => NONE) ps
      in case actions of [] => NONE
                      |  [action] => SOME action
                      | _ => raise Fail "there can be at most one target"
      end;

   val get_matches : (parsed_match_action list -> term) =
        List.mapPartial (fn p => case p of ParsedMatch m => SOME m | _ => NONE) #> HOLogic.mk_list @{typ "common_primitive"};
in
   (*returns: (chainname the rule was appended to, target, matches)*)
   fun parse_rule (s: string) : (string * string option * term) = let val (chainname, rest) = s |> ipt_explode |> parse_table_append
      in let val parsed = parse_rule_options rest in
        (chainname, get_target parsed, get_matches parsed)
      end end
    ;
end
*}


ML{*
local
  (*returns (chain declarations, appended rules*)
  fun rule_type_partition (rs : string list) : (string list * string list) = let val (chain_decl, rules) = List.partition (String.isPrefix ":") rs in
      if not (List.all (String.isPrefix "-A") rules) then raise Fail "could not partition rules" else
        (chain_decl, rules)
      end

in
  val _ = "Parsed "^ Int.toString (length (snd (rule_type_partition filter_table))) ^" rules" |> writeln;

  val (chain_decls, rules) = rule_type_partition filter_table;

  val parsed_chain_decls = map (ipt_explode #> chain_decl_parser) chain_decls;

  val parsed_rules = map parse_rule rules;
end;
*}

ML_val{*
val toString = (fn (a,target,b) => "-A "^a^" "^((Syntax.pretty_term @{context} #> Pretty.string_of) b)^(case target of NONE => "" | SOME t => " -j "^t));
map (toString #> writeln) parsed_rules;
*}

ML_val{*
map (fn (_,_,b) =>  type_of b) parsed_rules;
*}


ML{*
structure FirewallTable = Table(type key = string; val ord = Library.string_ord);
type firewall_table = term list FirewallTable.table;

fun FirewallTable_init chain_decls :firewall_table = fold (fn entry => fn accu => FirewallTable.update_new (entry, []) accu) chain_decls FirewallTable.empty;

fun mk_MatchExpr t = if type_of t <> @{typ "common_primitive list"} then raise Fail "Type Error" else @{const foldMatchAnd (common_primitive)} $ t;
fun mk_Rule_help t a = let val r = @{const Rule (common_primitive)} $ (mk_MatchExpr t) $ a in
    if type_of r <> @{typ "common_primitive rule"} then raise Fail "Type error in mk_Rule_help"
    else r end;

fun append table chain rule = case FirewallTable.lookup table chain
    of NONE => raise Fail ("uninitialized cahin: "^chain)
    |  SOME rules => FirewallTable.update (chain, rules@[rule]) table
*}

ML{*
fun mk_Rule (tbl: firewall_table) (chain: string, target : string option, t : term) =
  if not (FirewallTable.defined tbl chain) then raise Fail ("undefined chain to be appended: "^chain) else
  case target
  of NONE => mk_Rule_help t @{const action.Empty}
   | SOME "ACCEPT" => mk_Rule_help t @{const action.Accept}
   | SOME "DROP" => mk_Rule_help t @{const action.Drop}
   | SOME "REJECT" => mk_Rule_help t @{const action.Reject}
   | SOME "LOG" => mk_Rule_help t @{const action.Log}
   | SOME "RETURN" => mk_Rule_help t @{const action.Return}
   | SOME custom => if not (FirewallTable.defined tbl custom) then raise Fail ("unknown action: "^custom) else
                    mk_Rule_help t (@{const action.Call} $ HOLogic.mk_string custom);
*}

ML_val{*
val init = FirewallTable_init parsed_chain_decls;
map type_of (map (mk_Rule init) parsed_rules);
*}

ML{*
fun append_rule (tbl: firewall_table) (chain: string, target : string option, t : term) = append tbl chain (mk_Rule tbl (chain, target, t))
*}


ML{*
val parsed_ruleset = fold (fn rule => fn accu => append_rule accu rule) parsed_rules (FirewallTable_init parsed_chain_decls);
*}

ML{*
fun mk_Ruleset (tbl: firewall_table) = FirewallTable.dest_list tbl |> map (fn (k,v) => HOLogic.mk_prod (HOLogic.mk_string k, v)) |> HOLogic.mk_list @{typ "string \<times> common_primitive rule"}
*}

ML_val{*
type_of (mk_Ruleset parsed_ruleset);
Pretty.writeln (Syntax.pretty_term @{context} (mk_Ruleset parsed_ruleset));
(*ALMOST! FirewallTable.dest_list is probably not the right thing to do*)
*}

ML_val{* @{const MatchAnd (common_primitive)} $ (@{const Src} $ @{term undefined}) $ @{term undefined} |> fastype_of *}

end
