section\<open>Simple Firewall Syntax\<close>
theory SimpleFw_Syntax
imports "../IP_Addresses/Hs_Compat"
        Firewall_Common_Decision_State
        "Primitives/Iface"
        "Primitives/L4_Protocol"
        "Simple_Packet"
begin

  text\<open>For for IP addresses of arbitrary length\<close>

  datatype simple_action = Accept | Drop
  
  text\<open>Simple match expressions do not allow negated expressions.
        However, Most match expressions can still be transformed into simple match expressions.
        
        A negated IP address range can be represented as a set of non-negated IP ranges.
        For example @{text "!8 = {0..7} \<union> {8 .. ipv4max}"}.
        Using CIDR notation (i.e. the @{text "a.b.c.d/n"} notation), we can represent negated IP
        ranges as a set of non-negated IP ranges with only fair blowup.
        Another handy result is that the conjunction of two IP ranges in CIDR notation is 
        either the smaller of the two ranges or the empty set.
        An empty IP range cannot be represented.
        If one wants to represent the empty range, then the complete rule needs to be removed.

        The same holds for layer 4 ports.
        In addition, there exists an empty port range, e.g. @{text "(1,0)"}.
        The conjunction of two port ranges is again just one port range.
        
        But negation of interfaces is not supported. Since interfaces support a wildcard character,
        transforming a negated interface would either result in an infeasible blowup or requires
        knowledge about the existing interfaces (e.g. there only is eth0, eth1, wlan3, and vbox42)
        An empirical test shows that negated interfaces do not occur in our data sets.
        Negated interfaces can also be considered bad style: What is !eth0? Everything that is
        not eth0, experience shows that interfaces may come up randomly, in particular in combination 
        with virtual machines, so !eth0 might not be the desired match.
        At the moment, if an negated interface occurs which prevents translation to a simple match,
        we recommend to abstract the negated interface to unknown and remove it (upper or lower closure
        rule set) before translating to a simple match.
        The same discussion holds for negated protocols.

        Noteworthy, simple match expressions are both expressive and support conjunction:
        @{text "simple-match1 \<and> simple-match2 = simple-match3"}
\<close>
        (*It took very long to design the simple match such that it can represent everything we need
        and that you can calculate with it. Disjunction is easy: just have two consecutive rules with the same action.
        Conjunction was a tough fight! It is needed to translate:
        common_primitive_match_to_simple_match (MatchAny e1 e2) =
          simple_match_and (common_primitive_match_to_simple_match e1) (common_primitive_match_to_simple_match e2)
        This is key to translate common_primitive_match to simple_match

        It may seem a simple enhancement to support iiface :: "iface negation_type", but then you
        can no longer form the conjunction of two simple_matches.
        *)

  record (overloaded) 'i simple_match =
    iiface :: "iface" --"in-interface"
      (*we cannot (and don't want to) express negated interfaces*)
      (*We could also drop interface wildcard support and try negated interfaces again \<dots>*)
    oiface :: "iface" --"out-interface"
    src :: "('i::len word \<times> nat) " --"source IP address"
    dst :: "('i::len word \<times> nat) " --"destination"
    proto :: "protocol"
    sports :: "(16 word \<times> 16 word)" --"source-port first:last"
    dports :: "(16 word \<times> 16 word)" --"destination-port first:last"

  
  context
    notes [[typedef_overloaded]]
  begin
    datatype 'i simple_rule = SimpleRule (match_sel: "'i simple_match") (action_sel: simple_action)
  end



text\<open>Simple rule destructor. Removes the @{typ "'a simple_rule"} type, returns a tuple with the match and action.\<close>
  definition simple_rule_dtor :: "'a simple_rule \<Rightarrow> 'a simple_match \<times> simple_action" where
    "simple_rule_dtor r \<equiv> (case r of SimpleRule m a \<Rightarrow> (m,a))"
  
  lemma simple_rule_dtor_ids:
    "uncurry SimpleRule \<circ> simple_rule_dtor = id"
    "simple_rule_dtor \<circ> uncurry SimpleRule = id" 
    unfolding simple_rule_dtor_def comp_def fun_eq_iff
    by(simp_all split: simple_rule.splits)

end
