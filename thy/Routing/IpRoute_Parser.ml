fun register_ip_route bitness (name,path) (lthy: local_theory) =
	let
	val _ = case bitness of
	    32  => writeln "Using IPv4 parser"
    | 128 => writeln "Using IPv6 parser"
    | _   => raise Fail("Unable to decide on IPv4 or IPv6")

	(* Bitness dependent stuff *)
  val v4 = (bitness = 32)
  val parser_ip = if v4 then (parser_ipv4 >> (fn ip => mk_ipv4addr ip)) else (parser_ipv6 >> (fn ip => mk_ipv6addr ip))
  val next_hop_update = if v4 then @{const routing_action_next_hop_update (32)} else @{const routing_action_next_hop_update (128)}
  val construct_prefix = if v4 then @{term "PrefixMatch :: 32 word \<Rightarrow> nat \<Rightarrow> 32 prefix_match"} else @{term "PrefixMatch :: 128 word \<Rightarrow> nat \<Rightarrow> 128 prefix_match"}
  val default_prefix = if v4 then @{const default_prefix (32)} else @{const default_prefix (128)}
  val oiface_update = if v4 then @{term "routing_action_oiface_update :: string \<Rightarrow> 32 routing_rule \<Rightarrow> 32 routing_rule"} else @{term "routing_action_oiface_update :: string \<Rightarrow> 128 routing_rule \<Rightarrow> 128 routing_rule"}
  val metric_update = if v4 then @{term "metric_update :: (nat \<Rightarrow> nat) \<Rightarrow> 32 routing_rule \<Rightarrow> 32 routing_rule"} else @{term "metric_update :: (nat \<Rightarrow> nat) \<Rightarrow> 128 routing_rule \<Rightarrow> 128 routing_rule"}
  val empty_rr = if v4 then @{const empty_rr_hlp (32)} else @{const empty_rr_hlp (128)}
  fun to_rtbl r = if v4 then @{const sort_rtbl (32)} $ (HOLogic.mk_list @{typ "32 routing_rule"} r) else @{const sort_rtbl (128)} $ (HOLogic.mk_list @{typ "128 routing_rule"} r)
  fun sanity_check r = if v4 then @{const sanity_ip_route (32)} $ r else @{const sanity_ip_route (128)} $ r

  (* the parser *)
  fun define_const (t: term) (name: binding) (lthy: local_theory) : local_theory = let
        val _ = writeln ("Defining constant `"^Binding.name_of name^"' ("^Binding.name_of name^"_def')...");
        val ((_, (_, thm)), lthy) = Local_Theory.define ((name, NoSyn), ((Binding.empty, []), t)) lthy;
        val (_, lthy) = Local_Theory.note ((Binding.suffix_name "_def" name, @{attributes [code]}), [thm]) lthy;
       in
         lthy
  end
  fun load_file (thy: theory) (path: string list) =
      let val p =  File.full_path (Resources.master_directory thy) (Path.make path); in
      let val _ = "Loading file "^File.platform_path p |> writeln; in
        if not (File.exists p) orelse (File.is_dir p) then raise Fail "File not found" else File.read_lines p
   end end;

  (* and now, some code duplication with the IPtables parser\<dots> *)
  fun extract_int ss = case ss |> implode |> Int.fromString of SOME i => i
                                                             | NONE => raise Fail "unparsable int";

  fun is_iface_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "+" orelse x = "*" orelse x = "." orelse x = "-")
  fun mk_nat maxval i = if i < 0 orelse i > maxval
            then
              raise Fail("nat ("^Int.toString i^") must be between 0 and "^Int.toString maxval)
            else (HOLogic.mk_number HOLogic.natT i);

  fun ipprefix_to_hol (ip,len) = construct_prefix $ ip $ mk_nat bitness len;
  
  val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ipprefix_to_hol;
  
  val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => HOLogic.mk_string x));
  (* end dup *)
  
  val parser_subnet =  (Scan.this_string "default" >> K default_prefix) ||
    parser_ip_cidr ||
    (parser_ip >> (fn ip => ipprefix_to_hol (ip,bitness)))
  val isSpace = (fn x => x = " " orelse  x = "\t")
  val parser_whitespace = Scan.many1 isSpace;
  val eater_whitespace = Scan.many isSpace; (* I refuse to have this eat \r to make the parser work with windows newlines. *)

  val parser_via = (Scan.this_string "via" -- parser_whitespace |-- parser_ip)
    >> (fn ip => fn pk => next_hop_update $ ip $ pk)
  val parser_dev = (Scan.this_string "dev" -- parser_whitespace |-- parser_interface)
    >> (fn dev => fn pk => oiface_update $ dev $ pk)
  val parser_metric = (Scan.this_string "metric" -- parser_whitespace |-- Scan.many1 Symbol.is_ascii_digit)
    >> (fn metric => fn pk => metric_update $ (@{term "(\<lambda> x _. x) :: nat \<Rightarrow> nat \<Rightarrow> nat"} $ (mk_nat 65535 (extract_int metric))) $ pk)

  (* the following values are going to be ignored since they can't be represented in the model, but I want to make sure they are parsed correctly *)
  val parser_scope = (Scan.this_string "scope" -- parser_whitespace |-- (
    Scan.this_string "host" || Scan.this_string "link" || Scan.this_string "global" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I (* K I -> constant ignore: this value indicates the scope of validity of the rule *)
  val parser_proto = (Scan.this_string "proto" -- parser_whitespace |-- (
    Scan.this_string "kernel" || Scan.this_string "boot" || Scan.this_string "static" || Scan.this_string "dhcp" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I (* ignore: this value indicates how the rt-entry came to existence *)
  val parser_src = (Scan.this_string "src" -- parser_whitespace |-- parser_ipv4) 
    >> K I (* ignore: this value is used if an application (on the same device as the routing table) is sending an IP packet and has not bound to a specific address *)

  (* TODO (for IPv6) there might be some more options to ignore\<dots> "pref medium"? *)

  fun parser_end p i = let
    val (r,es) = Scan.finite Symbol.stopper (p --| eater_whitespace) i
  in
    if es = [] then r else let val _ = writeln ("'" ^ (implode es) ^ "'") in K r (* cause error - TODO: How do I do that properly? *) 
    (($$ "x") (Symbol.explode ""))
  end end

  val parser =
    (parser_end ((parser_subnet >> (fn x => empty_rr $ x))
        -- Scan.repeat (parser_whitespace |-- (parser_via || parser_dev || parser_metric || parser_scope || parser_proto || parser_src)))) 
    #> swap #> (uncurry (fold (fn a => fn b => a b)))

  fun sanity_check_ip_route (ctx: Proof.context) t = let
    val _ = writeln "Checking sanity..."
    val check = Code_Evaluation.dynamic_value_strict ctx (sanity_check t)
  in
    if check <> @{term "True"} then raise ERROR "sanity_wf_ruleset failed" else t
  end;
	  val fcontent = load_file (Proof_Context.theory_of lthy) [path]
	  (*val _ = map (Pretty.writeln o Syntax.pretty_term @{context} o parser o Symbol.explode) fcontent (* keep this one, lets you see on which line it fails *)*)
	  val r = map (parser o Symbol.explode) fcontent
	  val c = to_rtbl r
	  val s = sanity_check_ip_route lthy c
	  val d = define_const s name lthy
	  val _ = writeln "Done."
	in
	  d
end