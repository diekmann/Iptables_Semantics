theory Parser
imports Code_Interface
begin

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


ML{*
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
skip_until " -xx " (raw_explode "a - foo");
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
ipt_explode "ad asdas boo";
ipt_explode "ad \"foobar --boo boo";
*}

ML{*

local
  fun extract_int ss = case ss |> implode |> Int.fromString of SOME i => i
                                                             | NONE => raise Fail "unparsable int";

  fun is_iface_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "+" orelse x = "*" orelse x = ".")

  fun is_target_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse x = "-" orelse x = "~")
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

fun parse_cmd_option (s: string) (t: term) (parser: string list -> (term * string list)) = 
    Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string s -- (parser >> (fn r => t $ r)))


val parse_src_ip = parse_cmd_option "-s " @{const Src} parser_ip_cidr;
val parse_dst_ip = parse_cmd_option "-d " @{const Dst} parser_ip_cidr;


val parse_in_iface = parse_cmd_option "-i " @{const IIface} parser_interface;
val parse_out_iface = parse_cmd_option "-o " @{const OIface} parser_interface;

val parse_unknown = parse_cmd_option "" @{const Extra} parser_extra;


(*parses: -A FORWARD*)
val parse_table_append : (string list -> (string * string list)) = Scan.this_string "-A " |-- parser_target --| is_whitespace;

(*parses: -j MY_CUSTOM_CHAIN*)
(*TODO: parse until eol, ugly hack here!*)
val parse_target : (string list -> (string * string list)) = is_whitespace |-- Scan.this_string "-j " |-- parser_target;

(*parses: -s 0.31.123.213/88 --foo_bar*)
val option_parser : (string list -> (string * term) * string list) = 
    parse_src_ip || parse_dst_ip || parse_in_iface || parse_out_iface || parse_unknown;

(*parse_table_append and parse_target should be called first, otherwise those are unknown options for option_parser*)


fun debug_type_of [] = []
 |  debug_type_of ((_, t)::ts) = type_of t :: debug_type_of ts;
fun debug_print [] = []
 |  debug_print ((_, t)::ts) = Pretty.writeln (Syntax.pretty_term @{context} t) :: debug_print ts;

(*TODO: probably parse (from right? or with eol? the target, then parse all remaining options*)

val (x, rest) = (Scan.repeat option_parser) (ipt_explode "-d 0.31.123.213/88 --foo_bar \"hehe\" -i eth0+ -s 0.31.123.213/88 moreextra");
debug_type_of x;
debug_print x;
*}


ML{*


local
  datatype RuleType = ChainDecl | Rule
  fun rule_type s = if String.isPrefix ":" s then ChainDecl else
                    if String.isPrefix "-A" s then Rule else
                    raise Fail "could not parse rule"

  (*parse a rule. The parser returns ((string, term) list, unparsed_rest)
    For example: ([("-s", @{term "Src (Ip4AddrNetmask (0, 31, 123, 213) 88)"}), [])*)
  fun parse_rule_options (s: string list) : term list = let val (t, rest) = (Scan.repeat option_parser) s
            in
            if rest <> []
            then
              raise Fail ("Unparsed: "^implode rest)
            else
              map snd t
            end;

   fun parse_rule (s: string) : (string * term) = let val (chainname, cmd) = s |> ipt_explode |> parse_table_append
      in
        (chainname, parse_rule_options cmd |> HOLogic.mk_list @{typ "common_primitive"})
      end
    ;

in
  val _ = "Parsed "^ Int.toString (length (filter (fn r => case rule_type r of Rule => true | _ => false) filter_table)) ^" rules" |> writeln;

  fun parse_filter_table [] = []
   |  parse_filter_table (s::ss) = case rule_type s of ChainDecl => parse_filter_table ss
                                                    | Rule => parse_rule s :: parse_filter_table ss;
end;
*}

ML_val{*
map (fn (a,b) => let val _= writeln a in (Syntax.pretty_term @{context} #> Pretty.writeln) b end) (parse_filter_table filter_table);
*}

ML_val{* @{const MatchAnd (common_primitive)} $ (@{const Src} $ @{term undefined}) $ @{term undefined} |> fastype_of *}

end
