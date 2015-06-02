theory Parser
imports Code_Interface
begin



fun foldMatchAnd :: "'a list => 'a match_expr" where
  "foldMatchAnd [] = MatchAny" |
  "foldMatchAnd (m#ms) = MatchAnd (Match m) (foldMatchAnd ms)"

lemma foldMatchAnd_alist_and: "foldMatchAnd as = alist_and (map Pos as)"
  by(induction as)(simp_all)

fun compress_parsed_extra :: "common_primitive list \<Rightarrow> common_primitive list" where
  "compress_parsed_extra [] = []" |
  "compress_parsed_extra ((Extra e1)#(Extra e2)#as) = compress_parsed_extra ((Extra (e1@'' ''@e2))#as)" |
  "compress_parsed_extra (a#as) = a#compress_parsed_extra as"

value "compress_parsed_extra [Extra ''-m'', Extra ''recent'', Extra ''--update'', Extra ''--seconds'', Extra ''60'', Extra ''--name'', Extra ''DEFAULT'', Extra ''--rsource'']"

lemma compress_parsed_extra_matchexpr: "matches (common_matcher, \<alpha>) (foldMatchAnd (compress_parsed_extra m)) = matches (common_matcher, \<alpha>) (foldMatchAnd m)"
  apply(simp add: fun_eq_iff)
  apply(intro allI)
  apply(rule matches_iff_apply_f)
  apply(simp add: foldMatchAnd_alist_and )
  apply(induction m rule: compress_parsed_extra.induct)
  apply (simp_all)
oops


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
local
  fun is_start_of_filter_table s = s = "*filter";
  fun is_end_of_table s = s = "COMMIT";
  (*fun is_comment s = String.isPrefix "#" s*)

  fun load_file (path: string list) =
      let val p = Path.append Path.root (Path.make path); in
      let val _ = "loading file "^File.platform_path p |> writeln; in
        if not (File.exists p) orelse (File.is_dir p) then raise Fail "File not found" else File.read_lines p
      end end;

  fun extract_filter_table [] = []
   |  extract_filter_table (r::rs) = if not (is_start_of_filter_table r) then extract_filter_table rs else
                                     takeWhile (fn x => not (is_end_of_table x)) rs

  fun writenumloaded filter_table =
    let val _ = "Loaded "^ Int.toString (length filter_table) ^" lines of the filter table" |> writeln; in
      filter_table
    end;
in
  val load_filter_table = load_file #> extract_filter_table #> writenumloaded;
end;
*}

ML{*
(*val filter_table = load_filter_table ["home", "diekmann", "git", "Iptables_Semantics", "Examples", "SQRL_Shorewall", "iptables-saveakachan"];*)
val filter_table = load_filter_table ["home", "diekmann", "git", "net-network-private", "iptables-save-2015-05-15_15-23-41"];
(*val filter_table = load_filter_table ["home", "diekmann", "git", "Iptables_Semantics", "Examples", "Parser_Test", "iptables-save"];*)
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
datatype parsed_match_action = ParsedMatch of term | ParsedNegatedMatch of term | ParsedAction of string;
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
    
      fun ip_to_hol (ip,len) = @{const Ip4AddrNetmask} $ mk_quadrupel ip $ mk_nat 32 len;
    
      val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                     (Scan.many1 Symbol.is_ascii_digit >> extract_int);
      
      val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ip_to_hol;
    
      val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => @{const Iface} $ HOLogic.mk_string x));
    
      val parser_extra = Scan.many1 (fn x => x <> " " andalso Symbol.not_eof x) >> (implode #> HOLogic.mk_string);
    
    end;
    fun parse_cmd_option_generic (d: term -> parsed_match_action) (s: string) (t: term) (parser: string list -> (term * string list)) = 
        Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string s |-- (parser >> (fn r => d (t $ r))))

    fun parse_cmd_option (s: string) (t: term) (parser: string list -> (term * string list)) = parse_cmd_option_generic ParsedMatch s t parser;

    fun parse_cmd_option_negated (s: string) (t: term) (parser: string list -> (term * string list)) = parse_cmd_option_generic ParsedNegatedMatch s t parser;
  in
    
    val parse_src_ip = parse_cmd_option "-s " @{const Src} parser_ip_cidr;
    val parse_dst_ip = parse_cmd_option "-d " @{const Dst} parser_ip_cidr;

    val parse_src_ip_negated = parse_cmd_option_negated "! -s " @{const Src} parser_ip_cidr;
    val parse_dst_ip_negated = parse_cmd_option_negated "! -d " @{const Dst} parser_ip_cidr;    
    
    val parse_in_iface = parse_cmd_option "-i " @{const IIface} parser_interface;
    val parse_out_iface = parse_cmd_option "-o " @{const OIface} parser_interface;
    
    val parse_unknown = parse_cmd_option "" @{const Extra} parser_extra;
  end;
  
  
  local (*parser for target/action*)
    fun is_target_char x = Symbol.is_ascii x andalso
        (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "-" orelse x = "_" orelse x = "~")
  in
    val parser_target = Scan.many1 is_target_char >> implode;
  
    (*parses: -j MY_CUSTOM_CHAIN*)
    (*The -j may not be the end of the line. example: -j LOG --log-prefix "[IPT_DROP]:"*)
    val parse_target : (string list -> parsed_match_action * string list) = 
                  Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string "-j " |-- (parser_target >> ParsedAction ));
  end;
in
  (*parses: -A FORWARD*)
  val parse_table_append : (string list -> (string * string list)) = Scan.this_string "-A " |-- parser_target --| is_whitespace;
  
  
  (*parses: -s 0.31.123.213/88 --foo_bar -j chain --foobar
   First tries to parse a known field, afterwards, it parses something unknown until a blank space appears
  *)
  (*TODO: not parsed: negated IPs, ports, protocols, ...*)
  (*TODO: the new rulesets don't have negated IP addresses, but definetely test this!*)
  val option_parser : (string list -> (parsed_match_action) * string list) = 
      Scan.recover (parse_src_ip || parse_dst_ip || parse_in_iface || parse_out_iface ||
                    parse_target || parse_src_ip_negated || parse_dst_ip_negated) (K parse_unknown);
  
  
  (*parse_table_append should be called before option_parser, otherwise -A will simply be an unknown for option_parser*)
  
  (*:INPUT ACCEPT [130:12050]*)
  val chain_decl_parser = ($$ ":") |-- parser_target #> fst;
end;
*}

ML_val{*(Scan.repeat option_parser) (ipt_explode "-i lup -j net-fw")*}
ML_val{*(Scan.repeat option_parser) (ipt_explode "")*}
ML_val{*(Scan.repeat option_parser) (ipt_explode "-j LOG --log-prefix \"Shorewall:INPUT:REJECT:\" --log-level 6")*}


ML_val{*
val (x, rest) = (Scan.repeat option_parser) (ipt_explode "-d 0.31.123.213/88 --foo_bar \"he he\" -f -i eth0+ -s 0.31.123.213/88 moreextra -j foobar --log");
map (fn p => case p of ParsedMatch t => type_of t | ParsedAction _ => dummyT) x;
map (fn p => case p of ParsedMatch t => Pretty.writeln (Syntax.pretty_term @{context} t) | ParsedAction a => writeln ("action: "^a)) x;
*}

ML{*
local
  fun parse_rule_options (s: string list) : parsed_match_action list = let val (parsed, rest) = (case try (Scan.catch (Scan.repeat option_parser)) s of SOME x => x | NONE => raise Fail "scanning")
            in
            if rest <> []
            then
              raise Fail ("Unparsed: `"^implode rest^"'")
            else
              parsed
            end
            handle Fail m => raise Fail ("parse_rule_options: "^m^" for rule `"^implode s^"'");

   fun get_target (ps : parsed_match_action list) : string option = let val actions = List.mapPartial (fn p => case p of ParsedAction a => SOME a | _ => NONE) ps
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
   fun parse_rule (s: string) : (string * string option * term) = let
      val (chainname, rest) =
        (case try (ipt_explode #> Scan.finite Symbol.stopper parse_table_append) s of SOME x => x | NONE => raise Fail ("parse_rule: parse_table_append: "^s))
      in let val parsed = parse_rule_options rest in
        (chainname, get_target parsed, get_matches parsed)
      end end;
in
  (*returns (parsed chain declarations, parsed appended rules*)
  fun rule_type_partition (rs : string list) : (string list * (string * string option * term) list) =
      let val (chain_decl, rules) = List.partition (String.isPrefix ":") rs in
      if not (List.all (String.isPrefix "-A") rules) then raise Fail "could not partition rules" else
        let val parsed_chain_decls = map (ipt_explode #> chain_decl_parser) chain_decl in
        let val parsed_rules = map parse_rule rules in
            let val  _ = "Parsed "^ Int.toString (length parsed_chain_decls) ^" chain declarations" |> writeln in
            let val  _ = "Parsed "^ Int.toString (length parsed_rules) ^" rules" |> writeln in
              (parsed_chain_decls, parsed_rules)
            end end end end
      end
end;
*}

ML{*
  val (parsed_chain_decls, parsed_rules) = rule_type_partition filter_table;
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

(* this takes like forever! *)
(* apply compress_parsed_extra here?*)
fun hacky_hack t = (*Code_Evaluation.dynamic_value_strict @{context}*) (@{const compress_extra} $ t)

fun mk_MatchExpr t = if fastype_of t <> @{typ "common_primitive negation_type list"} then raise Fail "Type Error" else hacky_hack (@{const alist_and ("common_primitive")} $ t);
fun mk_Rule_help t a = let val r = @{const Rule (common_primitive)} $ (mk_MatchExpr t) $ a in
    if fastype_of r <> @{typ "common_primitive rule"} then raise Fail "Type error in mk_Rule_help"
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
(*map type_of (map (mk_Rule init) parsed_rules);*)
*}

ML{*
fun append_rule (tbl: firewall_table) (chain: string, target : string option, t : term) = append tbl chain (mk_Rule tbl (chain, target, t))
*}


ML{*
val parsed_ruleset = fold (fn rule => fn accu => append_rule accu rule) parsed_rules (FirewallTable_init parsed_chain_decls);
*}

ML{*
fun mk_Ruleset (tbl: firewall_table) = FirewallTable.dest tbl
    |> map (fn (k,v) => HOLogic.mk_prod (HOLogic.mk_string k, HOLogic.mk_list @{typ "common_primitive rule"} v))
    |> HOLogic.mk_list @{typ "string \<times> common_primitive rule list"}
*}

ML_val{*
type_of (mk_Ruleset parsed_ruleset);
Pretty.writeln (Syntax.pretty_term @{context} (mk_Ruleset parsed_ruleset));
*}

(*TODO: probably already add @{const map_of ("string", "common_primitive rule list")}*)

local_setup \<open>fn lthy =>
let
   val ((_, (_, thm)), lthy) =
    Local_Theory.define ((@{binding foo}, NoSyn),
        (*this takes a while*)
        ((Binding.empty, []), (Code_Evaluation.dynamic_value_strict @{context} (mk_Ruleset parsed_ruleset)))) lthy
    val (_, lthy) =
       Local_Theory.note ((@{binding foo_def}, []), [thm]) lthy
   in
     lthy
   end
 \<close>

(*todo: probably add foo_map_of*)

term foo
thm foo_def
declare foo_def[code]


value(code) "(map_of foo) ''FORWARD''" (*takes forever*)
value(code) "unfold_ruleset_FORWARD action.Accept (map_of foo)"
value(code) "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_FORWARD action.Accept (map_of foo))))"
value(code) "map simple_rule_toString (to_simple_firewall (lower_closure (unfold_ruleset_FORWARD action.Accept (map_of foo))))"


ML\<open>
Code_Simp.dynamic_conv @{context} @{cterm foo}
\<close>

(*
ML\<open>
Code_Evaluation.dynamic_conv @{context} @{cterm foo}
\<close>
*)

(*
value "True"

value(code) "(map_of foo) ''FORWARD''"

value(code) "map simple_rule_toString (to_simple_firewall (upper_closure (unfold_ruleset_FORWARD action.Accept (map_of foo))))"

ML{*Code_Evaluation.dynamic_conv @{context} @{cterm "unfold_ruleset_FORWARD action.Accept (map_of foo)"}*}
*)

end
