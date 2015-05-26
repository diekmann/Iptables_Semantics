theory Parser
imports Code_Interface
begin

(*Incomplete: An ML Parser for iptables-save*)

ML{*

(*TODO, library function?*)
fun takewhile _ [] = []
  | takewhile pred (x::xs) = 
        if  pred x  then  x :: takewhile pred xs  
        else  [];
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
                                     takewhile (fn x => not (is_end_of_table x)) rs
end;

val filter_table = extract_filter_table iptables_save;

val _ = "Parsed "^ Int.toString (length filter_table) ^" entries" |> writeln;
(*val _ = filter_table |> map writeln;*)

local

  datatype RuleType = ChainDecl | Rule
  fun rule_type s = if String.isPrefix ":" s then ChainDecl else
                    if String.isPrefix "-A" s then Rule else
                    raise Fail "could not parse rule"
in
  val _ = "Parsed "^ Int.toString (length (filter (fn r => case rule_type r of Rule => true | _ => false) filter_table)) ^" rules" |> writeln;
end;


*}

ML{*
String.explode "sasd";
raw_explode "as\"d"
*}

ML{*
(*TODO: it should keep quoted stings as one token*)
val ipt_explode = raw_explode
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
  fun mk_nat i = (HOLogic.mk_number HOLogic.natT i)

  fun mk_quadrupel (((a,b),c),d) = HOLogic.mk_prod (mk_nat a, HOLogic.mk_prod (mk_nat b, HOLogic.mk_prod (mk_nat c, mk_nat d)));

  fun ip_to_hol (ip,len) = @{const Ip4AddrNetmask} $ mk_quadrupel ip $ mk_nat len;

  fun conv f (a, s:string list) = (f a, s);

  val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int);
  
  val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int)
                       #> conv ip_to_hol;

  val parser_interface = (Scan.many1 is_iface_char >> implode #> conv (fn x => @{const Iface} $ HOLogic.mk_string x));

  val parser_target = (Scan.many1 is_target_char >> implode);

  val parser_extra = (Scan.many1 (fn x => x <> " ") >> implode #> conv HOLogic.mk_string);

  val is_whitespace = Scan.many (fn x => x = " ");
end;

fun parse_cmd_option (s: string) (t: term) (parser: string list -> (term * string list)) = 
    Scan.finite Symbol.stopper (is_whitespace |-- Scan.this_string s -- (parser >> (fn r => t $ r)))


val parse_src_ip = parse_cmd_option "-s " @{const Src} parser_ip_cidr;
val parse_dst_ip = parse_cmd_option "-d " @{const Dst} parser_ip_cidr;


val parse_in_iface = parse_cmd_option "-i " @{const IIface} parser_interface;
val parse_out_iface = parse_cmd_option "-o " @{const OIface} parser_interface;

(*
val parse_target = parse_cmd_option "-j " parser_target;
*)

val parse_unknown = parse_cmd_option "" @{const Extra} parser_extra;


val option_parser = parse_src_ip || parse_dst_ip || parse_in_iface || parse_out_iface || parse_unknown;

fun debug_type_of [] = []
 |  debug_type_of ((_, t)::ts) = type_of t :: debug_type_of ts;

(*TODO: probably parse (from right? or with eol? the target, then parse all remaining options*)

val (x, rest) = (Scan.repeat option_parser) (ipt_explode "-d 0.31.123.213/88 --foo_bar -i eth0+ -s 0.31.123.213/88 unparsed");
debug_type_of x;
*}

ML_val{* @{const MatchAnd (common_primitive)} $ (@{const Src} $ @{term undefined}) $ @{term undefined} |> fastype_of *}

ML_val{*
Symbol.explode;
Scan.many1 Symbol.is_ascii_digit (ipt_explode "212sdas34")
*}

end
