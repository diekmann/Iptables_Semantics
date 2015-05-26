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
  val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                 (Scan.many1 Symbol.is_ascii_digit >> extract_int);
  
  val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int)

  val parser_interface = (Scan.many1 is_iface_char >> implode);

  val parser_target = (Scan.many1 is_target_char >> implode);
end;

fun parse_cmd_option (s: string) (parser: string list -> ('a * string list)) = 
    Scan.finite Symbol.stopper (Scan.this_string s -- parser)

(*scan src ip*)
val parse_src_ip = parse_cmd_option "-s " parser_ip_cidr;
val parse_dst_ip = parse_cmd_option "-d " parser_ip_cidr;

val parse_in_iface = parse_cmd_option "-i " parser_interface;
val parse_out_iface = parse_cmd_option "-o " parser_interface;

val parse_target = parse_cmd_option "-j " parser_target;

val parse_unknown = Scan.many (fn x => x = " ") -- Scan.many1 (fn x => x <> " ");


val option_parser = parse_src_ip || parse_dst_ip (*|| parse_in_iface*);

Scan.repeat option_parser (ipt_explode "-d 0.31.123.213/88 --foo -s ");
*}

ML_val{*
Symbol.explode;
Scan.many1 Symbol.is_ascii_digit (ipt_explode "212sdas34")
*}

end
