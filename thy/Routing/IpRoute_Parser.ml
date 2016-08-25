local
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

  fun ipprefix_to_hol (ip,len) = @{term "PrefixMatch :: 32 word \<Rightarrow> nat \<Rightarrow> 32 prefix_match"} $ (mk_ipv4addr ip) $ mk_nat 32 len;
  
  val parser_ip_cidr = parser_ipv4 --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ipprefix_to_hol;
  
  val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => HOLogic.mk_string x));
  (* end dup *)
  
  val parser_subnet = parser_ip_cidr ||
    (parser_ipv4 >> (fn ip => ipprefix_to_hol (ip,32))) ||
    (Scan.this_string "default" >> K @{term "PrefixMatch 0 0 :: 32 prefix_match"})
  val isSpace = (fn x => x = " " orelse  x = "\t")
  val parser_whitespace = Scan.many1 isSpace;
  val eater_whitespace = Scan.many isSpace; (* I refuse to have this eat \r to make the parser work with windows newlines. *)

  val parser_via = (Scan.this_string "via" -- parser_whitespace |-- parser_ipv4) 
    >> (fn ip => fn pk => @{const routing_action_next_hop_update} $ (mk_ipv4addr ip) $ pk)
  val parser_dev = (Scan.this_string "dev" -- parser_whitespace |-- parser_interface)
    >> (fn dev => fn pk => @{term "routing_action_oiface_update :: string \<Rightarrow> 32 routing_rule \<Rightarrow> 32 routing_rule"} $ dev $ pk)
  val parser_metric = (Scan.this_string "metric" -- parser_whitespace |-- Scan.many1 Symbol.is_ascii_digit)
    >> (fn metric => fn pk => @{term "metric_update :: (nat \<Rightarrow> nat) \<Rightarrow> 32 routing_rule \<Rightarrow> 32 routing_rule"} $ (@{term "(\<lambda> x _. x) :: nat \<Rightarrow> nat \<Rightarrow> nat"} $ (mk_nat 65535 (extract_int metric))) $ pk)
  (* these are going to be ignored anyway\<dots>(?) *)
  val parser_scope = (Scan.this_string "scope" -- parser_whitespace |-- (
    Scan.this_string "host" || Scan.this_string "link" || Scan.this_string "global" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I (* K I -> constant ignore: this value indicates the scope of validity of the rule *)
  val parser_proto = (Scan.this_string "proto" -- parser_whitespace |-- (
    Scan.this_string "kernel" || Scan.this_string "boot" || Scan.this_string "static" || Scan.this_string "dhcp" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I (* ignore: this value indicates how the rt-entry came to existence *)
  val parser_src = (Scan.this_string "src" -- parser_whitespace |-- parser_ipv4) 
    >> K I (* ignore: this value is used if an application (on the same device as the routing table) is sending an IP packet and has not bound to a specific address *)
  (* these three ignored values are not represented in the model. *)

  fun parser_end p i = let
    val (r,es) = Scan.finite Symbol.stopper (p --| eater_whitespace) i
  in
    if es = [] then r else let val _ = writeln ("'" ^ (implode es) ^ "'") in K r (* cause error - TODO: How do I do that properly? *) 
    (($$ "x") (Symbol.explode ""))
  end end

  val parser =
    (parser_end ((parser_subnet >> (fn x => @{const empty_rr_hlp} $ x))
        -- Scan.repeat (parser_whitespace |-- (parser_via || parser_dev || parser_metric || parser_scope || parser_proto || parser_src)))) 
    #> swap #> (uncurry (fold (fn a => fn b => a b)))

  fun sanity_check_ip_route (ctx: Proof.context) t = let
    val _ = writeln "Checking sanity..."
    val check = Code_Evaluation.dynamic_value_strict ctx (@{const sanity_ip_route} $ t)
  in
    if check <> @{term "True"} then raise ERROR "sanity_wf_ruleset failed" else t
  end;
in
	fun register_ip_route (name,path) (lthy: local_theory) =
	let
	  val fcontent = load_file (Proof_Context.theory_of lthy) [path]
	  (*val _ = map (Pretty.writeln o Syntax.pretty_term @{context} o parser o Symbol.explode) fcontent (* keep this one, lets you see where it fails *)*)
	  val r = map (parser o Symbol.explode) fcontent
	  val c = @{const sort_rtbl (32)} $ (HOLogic.mk_list @{typ "32 routing_rule"} r)
	  val s = sanity_check_ip_route lthy c
	  val d = define_const s name lthy
	  val _ = writeln "Done."
	in
	  d
	end
end