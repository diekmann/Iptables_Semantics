local
  fun define_const (t: term) (name: binding) (lthy: local_theory) : local_theory = let
        val _ = writeln ("Defining constant `"^Binding.name_of name^"' ("^Binding.name_of name^"_def')");
        val ((_, (_, thm)), lthy) = Local_Theory.define ((name, NoSyn), ((Binding.empty, []), t)) lthy;
        val (_, lthy) = Local_Theory.note ((Binding.suffix_name "_def" name, @{attributes [code]}), [thm]) lthy;
       in
         lthy
  end
  fun load_file (thy: theory) (path: string list) =
      let val p =  File.full_path (Resources.master_directory thy) (Path.make path); in
      let val _ = "loading file "^File.platform_path p |> writeln; in
        if not (File.exists p) orelse (File.is_dir p) then raise Fail "File not found" else File.read_lines p
   end end;

  (* and now, some code duplication with the IPtables parser\<dots> *)
  fun extract_int ss = case ss |> implode |> Int.fromString of SOME i => i
                                                             | NONE => raise Fail "unparsable int";

  fun is_iface_char x = Symbol.is_ascii x andalso
      (Symbol.is_ascii_letter x orelse Symbol.is_ascii_digit x orelse x = "+" orelse x = "*" orelse x = ".")
  fun mk_nat maxval i = if i < 0 orelse i > maxval
            then
              raise Fail("nat ("^Int.toString i^") must be between 0 and "^Int.toString maxval)
            else (HOLogic.mk_number HOLogic.natT i);
  val mk_nat255 = mk_nat 255;

  fun mk_quadrupel (((a,b),c),d) = HOLogic.mk_prod
               (mk_nat255 a, HOLogic.mk_prod (mk_nat255 b, HOLogic.mk_prod (mk_nat255 c, mk_nat255 d)));
  fun ipprefix_to_hol (ip,len) = @{term "PrefixMatch :: 32 word \<Rightarrow> nat \<Rightarrow> 32 prefix_match"} $ (@{const ipv4addr_of_dotdecimal} $ (mk_quadrupel ip)) $ mk_nat 32 len;

  val parser_ip = (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int) --| ($$ ".") --
                  (Scan.many1 Symbol.is_ascii_digit >> extract_int);
  
  val parser_ip_cidr = parser_ip --| ($$ "/") -- (Scan.many1 Symbol.is_ascii_digit >> extract_int) >> ipprefix_to_hol;
  
  val parser_interface = Scan.many1 is_iface_char >> (implode #> (fn x => HOLogic.mk_string x));
  (* end dup *)
  
  val parser_subnet = parser_ip_cidr ||
    (parser_ip >> (fn ip => ipprefix_to_hol (ip,32))) ||
    (Scan.this_string "default" >> K @{term "PrefixMatch 0 0 :: 32 prefix_match"})
  val parser_whitespace = Scan.many1 (fn x => x = " ");

  val parser_via = (Scan.this_string "via" -- parser_whitespace |-- parser_ip) 
    >> (fn ip => fn pk => @{const routing_action_next_hop_update} $ (@{const ipv4addr_of_dotdecimal} $ (mk_quadrupel ip)) $ pk)
  val parser_dev = (Scan.this_string "dev" -- parser_whitespace |-- parser_interface)
    >> (fn dev => fn pk => @{term "routing_action_oiface_update :: string \<Rightarrow> routing_rule \<Rightarrow> routing_rule"} $ dev $ pk)
  val parser_metric = (Scan.this_string "metric" -- parser_whitespace |-- Scan.many1 Symbol.is_ascii_digit)
    >> (fn metric => fn pk => @{term "metric_update :: (nat \<Rightarrow> nat) \<Rightarrow> routing_rule \<Rightarrow> routing_rule"} $ (@{term "const :: nat \<Rightarrow> nat \<Rightarrow> nat"} $ (mk_nat 65535 (extract_int metric))) $ pk)
  (* these are going to be ignored anyway\<dots>(?) *)
  val parser_scope = (Scan.this_string "scope" -- parser_whitespace |-- (
    Scan.this_string "host" || Scan.this_string "link" || Scan.this_string "global" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I
  val parser_proto = (Scan.this_string "proto" -- parser_whitespace |-- (
    Scan.this_string "kernel" || Scan.this_string "boot" || Scan.this_string "static" || Scan.this_string "dhcp" || (Scan.many1 Symbol.is_ascii_digit >> implode)))
    >> K I
  val parser_src = (Scan.this_string "src" -- parser_whitespace |-- parser_ip) >> mk_quadrupel >> K I

  fun parser_end p i = let
    val (r,es) = Scan.finite Symbol.stopper (Scan.many (fn x => x = " ") |-- p --| Scan.many (fn x => x = " ")) i
  in
    if es = [] then r else let val _ = writeln ("'" ^ (implode es) ^ "'") in K r (* cause error - TODO: How do I do that properly? *) 
    (($$ "x") (Symbol.explode ""))
  end end

  val parser =
    (parser_end ((parser_subnet >> (fn x => @{const empty_rr_hlp} $ x))
        -- Scan.repeat (parser_whitespace |-- (parser_via || parser_dev || parser_metric || parser_scope || parser_proto || parser_src)))) 
    #> swap #> (uncurry (fold (fn a => fn b => a b)))
in
	fun register_ip_route (name,path) (lthy: local_theory) =
	let
	  val fcontent = load_file (Proof_Context.theory_of lthy) [path]
	  val _ = map (Pretty.writeln o Syntax.pretty_term @{context} o parser o Symbol.explode) fcontent (* keep this one, lets you see where it fails *)
	  val r = map (parser o Symbol.explode) fcontent
	in
	  define_const (HOLogic.mk_list @{typ "routing_rule"} r) name lthy
	  (* TODO: Some kind of sanity check. Especially, output_iface \<noteq> [] *)
	  (* TODO: Rules are unsorted. Sort. *)
	end
end