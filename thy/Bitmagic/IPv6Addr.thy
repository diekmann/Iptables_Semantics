(*  Title:      IPv6Addr.thy
    Authors:    Cornelius Diekmann
*)
theory IPv6Addr
imports Main
  NumberWang
  WordInterval_Lists
  "./l4v/lib/WordLemmaBucket" (*I hope we won't need it*)
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Library/Code_Target_Nat" (*!*)
begin

value "(2::nat) < 2^128" (*without Code_Target_Nat, this would be really slow*)


section {*Modelling IPv6 Adresses*}
  text{*An IPv6 address is basically a 128 bit unsigned integer. RFC 4291, Section 2.*}
  type_synonym ipv6addr = "128 word"
 

  (*the next lines are a copy from IPv4Addr.thy*)
  text{*Conversion between natural numbers and IPv6 adresses*}
  definition nat_of_ipv6addr :: "ipv6addr \<Rightarrow> nat" where
    "nat_of_ipv6addr a = unat a"
  definition ipv6addr_of_nat :: "nat \<Rightarrow> ipv6addr" where
    "ipv6addr_of_nat n =  of_nat n"

  lemma "((nat_of_ipv6addr (42::ipv6addr))::nat) = 42" by eval
  lemma "((ipv6addr_of_nat (42::nat))::ipv6addr) = 42" by eval

  text{*The maximum IPv6 addres*}
  definition max_ipv6_addr :: "ipv6addr" where 
    "max_ipv6_addr \<equiv> ipv6addr_of_nat ((2^128) - 1)"

  lemma max_ipv6_addr_number: "max_ipv6_addr = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    unfolding max_ipv6_addr_def ipv6addr_of_nat_def by(simp)
  lemma "max_ipv6_addr = 340282366920938463463374607431768211455"
    by(fact max_ipv6_addr_number)
  lemma max_ipv6_addr_max_word: "max_ipv6_addr = max_word"
    by(simp add: max_ipv6_addr_number max_word_def)
  lemma max_ipv6_addr_max[simp]: "\<forall>a. a \<le> max_ipv6_addr"
    by(simp add: max_ipv6_addr_max_word)
  lemma range_0_max_UNIV: "UNIV = {0 .. max_ipv6_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ipv6_addr_max_word) fastforce

  text{*identity functions*}
  lemma nat_of_ipv6addr_ipv6addr_of_nat: "\<lbrakk> n \<le> nat_of_ipv6addr max_ipv6_addr \<rbrakk> \<Longrightarrow> nat_of_ipv6addr (ipv6addr_of_nat n) = n"
    by (metis ipv6addr_of_nat_def le_unat_uoi nat_of_ipv6addr_def)
  lemma nat_of_ipv6addr_ipv6addr_of_nat_mod: "nat_of_ipv6addr (ipv6addr_of_nat n) = n mod 2^128"
    by(simp add: ipv6addr_of_nat_def nat_of_ipv6addr_def unat_of_nat)
  lemma ipv6addr_of_nat_nat_of_ipv6addr: "ipv6addr_of_nat (nat_of_ipv6addr addr) = addr"
    by(simp add: ipv6addr_of_nat_def nat_of_ipv6addr_def)


  text{*Equality of IPv6 adresses*}
  lemma "\<lbrakk> n \<le> nat_of_ipv6addr max_ipv6_addr \<rbrakk> \<Longrightarrow> nat_of_ipv6addr (ipv6addr_of_nat n) = n"
    apply(simp add: nat_of_ipv6addr_def ipv6addr_of_nat_def)
    apply(induction n)
     apply(simp_all)
    by(unat_arith)

  lemma ipv6addr_of_nat_eq: "x = y \<Longrightarrow> ipv6addr_of_nat x = ipv6addr_of_nat y"
    by(simp add: ipv6addr_of_nat_def)

subsection{*Syntax of IPv6 Adresses*}
  text{*RFC 4291, Section 2.2.: Text Representation of Addresses*}

  text{*Quoting the RFC (note: errata exists):
   1. The preferred form is x:x:x:x:x:x:x:x, where the 'x's are one to
      four hexadecimal digits of the eight 16-bit pieces of the address.
      Examples:
         ABCD:EF01:2345:6789:ABCD:EF01:2345:6789
         2001:DB8:0:0:8:800:200C:417A
  *}
  datatype ipv6addr_syntax = 
    IPv6AddrPreferred "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word"


text{*
   2. [...] In order to make writing addresses containing zero
      bits easier, a special syntax is available to compress the zeros.
      The use of "::" indicates one or more groups of 16 bits of zeros.
      The "::" can only appear once in an address.  The "::" can also be
      used to compress leading or trailing zeros in an address.

      For example, the following addresses
         2001:DB8:0:0:8:800:200C:417A   a unicast address
         FF01:0:0:0:0:0:0:101           a multicast address
         0:0:0:0:0:0:0:1                the loopback address
         0:0:0:0:0:0:0:0                the unspecified address

      may be represented as
         2001:DB8::8:800:200C:417A      a unicast address
         FF01::101                      a multicast address
         ::1                            the loopback address
         ::                             the unspecified address
  *}
  (*datatype may take some minutes to load*)
  datatype ipv6addr_syntax_compressed =
  --{*using @{typ unit} for the omission :: 
      The first number is the position where the omission occurs.
      The second number is the length of the specified address pieces.
        I.e. `8 minus the second number' pieces are omitted.*}
    IPv6AddrCompressed1_0 unit
  | IPv6AddrCompressed1_1 unit "16 word"
  | IPv6AddrCompressed1_2 unit "16 word" "16 word"
  | IPv6AddrCompressed1_3 unit "16 word" "16 word" "16 word"
  | IPv6AddrCompressed1_4 unit "16 word" "16 word" "16 word" "16 word" 
  | IPv6AddrCompressed1_5 unit "16 word" "16 word" "16 word" "16 word" "16 word"
  | IPv6AddrCompressed1_6 unit "16 word" "16 word" "16 word" "16 word" "16 word" "16 word"
  | IPv6AddrCompressed1_7 unit "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word"

  | IPv6AddrCompressed2_1 "16 word" unit
  | IPv6AddrCompressed2_2 "16 word" unit "16 word"
  | IPv6AddrCompressed2_3 "16 word" unit "16 word" "16 word"
  | IPv6AddrCompressed2_4 "16 word" unit "16 word" "16 word" "16 word"
  | IPv6AddrCompressed2_5 "16 word" unit "16 word" "16 word" "16 word" "16 word"
  | IPv6AddrCompressed2_6 "16 word" unit "16 word" "16 word" "16 word" "16 word" "16 word"
  | IPv6AddrCompressed2_7 "16 word" unit "16 word" "16 word" "16 word" "16 word" "16 word" "16 word"

  | IPv6AddrCompressed3_2 "16 word" "16 word" unit
  | IPv6AddrCompressed3_3 "16 word" "16 word" unit "16 word"
  | IPv6AddrCompressed3_4 "16 word" "16 word" unit "16 word" "16 word"
  | IPv6AddrCompressed3_5 "16 word" "16 word" unit "16 word" "16 word" "16 word"
  | IPv6AddrCompressed3_6 "16 word" "16 word" unit "16 word" "16 word" "16 word" "16 word"
  | IPv6AddrCompressed3_7 "16 word" "16 word" unit "16 word" "16 word" "16 word" "16 word" "16 word"

  | IPv6AddrCompressed4_3 "16 word" "16 word" "16 word" unit
  | IPv6AddrCompressed4_4 "16 word" "16 word" "16 word" unit "16 word"
  | IPv6AddrCompressed4_5 "16 word" "16 word" "16 word" unit "16 word" "16 word"
  | IPv6AddrCompressed4_6 "16 word" "16 word" "16 word" unit "16 word" "16 word" "16 word"
  | IPv6AddrCompressed4_7 "16 word" "16 word" "16 word" unit "16 word" "16 word" "16 word" "16 word"

  | IPv6AddrCompressed5_4 "16 word" "16 word" "16 word" "16 word" unit
  | IPv6AddrCompressed5_5 "16 word" "16 word" "16 word" "16 word" unit "16 word"
  | IPv6AddrCompressed5_6 "16 word" "16 word" "16 word" "16 word" unit "16 word" "16 word"
  | IPv6AddrCompressed5_7 "16 word" "16 word" "16 word" "16 word" unit "16 word" "16 word" "16 word"

  | IPv6AddrCompressed6_5 "16 word" "16 word" "16 word" "16 word" "16 word" unit
  | IPv6AddrCompressed6_6 "16 word" "16 word" "16 word" "16 word" "16 word" unit "16 word"
  | IPv6AddrCompressed6_7 "16 word" "16 word" "16 word" "16 word" "16 word" unit "16 word" "16 word"

  | IPv6AddrCompressed7_6 "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" unit
  | IPv6AddrCompressed7_7 "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" unit "16 word"

  (*RFC 5952:
    """
    4.  A Recommendation for IPv6 Text Representation
    4.2.2.  Handling One 16-Bit 0 Field
       The symbol "::" MUST NOT be used to shorten just one 16-bit 0 field.
       For example, the representation 2001:db8:0:1:1:1:1:1 is correct, but
       2001:db8::1:1:1:1:1 is not correct.
    """

    So we could remove all IPv6AddrCompressed*_7 constructors.
    But these are `recommendations', we might still see these non-recommended definitions.
    "[...] all implementations must accept and be able to handle any legitimate RFC 4291 format."
  *)

  (*More convenient parser helper function:
    Some 16word \<longrightarrow> address piece
    None \<longrightarrow> ommission :: *)
  fun parse_ipv6_address :: "((16 word) option) list \<Rightarrow> ipv6addr_syntax_compressed option" where
    "parse_ipv6_address as = (case as of 
      [None] \<Rightarrow> Some (IPv6AddrCompressed1_0 ())
    | [None, Some a] \<Rightarrow> Some (IPv6AddrCompressed1_1 () a)
    | [None, Some a, Some b] \<Rightarrow> Some (IPv6AddrCompressed1_2 () a b)
    | [None, Some a, Some b, Some c] \<Rightarrow> Some (IPv6AddrCompressed1_3 () a b c)
    | [None, Some a, Some b, Some c, Some d] \<Rightarrow> Some (IPv6AddrCompressed1_4 () a b c d)
    | [None, Some a, Some b, Some c, Some d, Some e] \<Rightarrow> Some (IPv6AddrCompressed1_5 () a b c d e)
    | [None, Some a, Some b, Some c, Some d, Some e, Some f] \<Rightarrow> Some (IPv6AddrCompressed1_6 () a b c d e f)
    | [None, Some a, Some b, Some c, Some d, Some e, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed1_7 () a b c d e f g)
  
    | [Some a, None] \<Rightarrow> Some (IPv6AddrCompressed2_1 a ())
    | [Some a, None, Some b] \<Rightarrow> Some (IPv6AddrCompressed2_2 a () b)
    | [Some a, None, Some b, Some c] \<Rightarrow> Some (IPv6AddrCompressed2_3 a () b c)
    | [Some a, None, Some b, Some c, Some d] \<Rightarrow> Some (IPv6AddrCompressed2_4 a () b c d)
    | [Some a, None, Some b, Some c, Some d, Some e] \<Rightarrow> Some (IPv6AddrCompressed2_5 a () b c d e)
    | [Some a, None, Some b, Some c, Some d, Some e, Some f] \<Rightarrow> Some (IPv6AddrCompressed2_6 a () b c d e f)
    | [Some a, None, Some b, Some c, Some d, Some e, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed2_7 a () b c d e f g)
  
    | [Some a, Some b, None] \<Rightarrow> Some (IPv6AddrCompressed3_2 a b ())
    | [Some a, Some b, None, Some c] \<Rightarrow> Some (IPv6AddrCompressed3_3 a b () c)
    | [Some a, Some b, None, Some c, Some d] \<Rightarrow> Some (IPv6AddrCompressed3_4 a b () c d)
    | [Some a, Some b, None, Some c, Some d, Some e] \<Rightarrow> Some (IPv6AddrCompressed3_5 a b () c d e)
    | [Some a, Some b, None, Some c, Some d, Some e, Some f] \<Rightarrow> Some (IPv6AddrCompressed3_6 a b () c d e f)
    | [Some a, Some b, None, Some c, Some d, Some e, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed3_7 a b () c d e f g)
  
    | [Some a, Some b, Some c, None] \<Rightarrow> Some (IPv6AddrCompressed4_3 a b c ())
    | [Some a, Some b, Some c, None, Some d] \<Rightarrow> Some (IPv6AddrCompressed4_4 a b c () d)
    | [Some a, Some b, Some c, None, Some d, Some e] \<Rightarrow> Some (IPv6AddrCompressed4_5 a b c () d e)
    | [Some a, Some b, Some c, None, Some d, Some e, Some f] \<Rightarrow> Some (IPv6AddrCompressed4_6 a b c () d e f)
    | [Some a, Some b, Some c, None, Some d, Some e, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed4_7 a b c () d e f g)
  
    | [Some a, Some b, Some c, Some d, None] \<Rightarrow> Some (IPv6AddrCompressed5_4 a b c d ())
    | [Some a, Some b, Some c, Some d, None, Some e] \<Rightarrow> Some (IPv6AddrCompressed5_5 a b c d () e)
    | [Some a, Some b, Some c, Some d, None, Some e, Some f] \<Rightarrow> Some (IPv6AddrCompressed5_6 a b c d () e f)
    | [Some a, Some b, Some c, Some d, None, Some e, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed5_7 a b c d () e f g)
  
    | [Some a, Some b, Some c, Some d, Some e, None] \<Rightarrow> Some (IPv6AddrCompressed6_5 a b c d e ())
    | [Some a, Some b, Some c, Some d, Some e, None, Some f] \<Rightarrow> Some (IPv6AddrCompressed6_6 a b c d e () f)
    | [Some a, Some b, Some c, Some d, Some e, None, Some f, Some g] \<Rightarrow> Some (IPv6AddrCompressed6_7 a b c d e () f g)
  
    | [Some a, Some b, Some c, Some d, Some e, Some f, None] \<Rightarrow> Some (IPv6AddrCompressed7_6 a b c d e f ())
    | [Some a, Some b, Some c, Some d, Some e, Some f, None, Some g] \<Rightarrow> Some (IPv6AddrCompressed7_7 a b c d e f () g)
    | _ \<Rightarrow> None (*invalid ipv6 copressed address.*)
)"

  fun ipv6addr_syntax_compressed_to_list :: "ipv6addr_syntax_compressed \<Rightarrow> ((16 word) option) list"
    where 
      "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_0 _) =
                                     [None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_1 () a) =
                                     [None, Some a]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_2 () a b) =
                                     [None, Some a, Some b]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_3 () a b c) =
                                     [None, Some a, Some b, Some c]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_4 () a b c d) =
                                     [None, Some a, Some b, Some c, Some d]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_5 () a b c d e) =
                                     [None, Some a, Some b, Some c, Some d, Some e]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_6 () a b c d e f) =
                                     [None, Some a, Some b, Some c, Some d, Some e, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed1_7 () a b c d e f g) =
                                     [None, Some a, Some b, Some c, Some d, Some e, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_1 a ()) =
                                     [Some a, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_2 a () b) =
                                     [Some a, None, Some b]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_3 a () b c) =
                                     [Some a, None, Some b, Some c]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_4 a () b c d) =
                                     [Some a, None, Some b, Some c, Some d]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_5 a () b c d e) =
                                     [Some a, None, Some b, Some c, Some d, Some e]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_6 a () b c d e f) =
                                     [Some a, None, Some b, Some c, Some d, Some e, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed2_7 a () b c d e f g) =
                                     [Some a, None, Some b, Some c, Some d, Some e, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_2 a b ()) = [Some a, Some b, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_3 a b () c) =
                                     [Some a, Some b, None, Some c]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_4 a b () c d) =
                                     [Some a, Some b, None, Some c, Some d]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_5 a b () c d e) =
                                     [Some a, Some b, None, Some c, Some d, Some e]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_6 a b () c d e f) =
                                     [Some a, Some b, None, Some c, Some d, Some e, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed3_7 a b () c d e f g) =
                                     [Some a, Some b, None, Some c, Some d, Some e, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed4_3 a b c ()) =
                                     [Some a, Some b, Some c, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed4_4 a b c () d) =
                                     [Some a, Some b, Some c, None, Some d]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed4_5 a b c () d e) =
                                     [Some a, Some b, Some c, None, Some d, Some e]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed4_6 a b c () d e f) =
                                     [Some a, Some b, Some c, None, Some d, Some e, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed4_7 a b c () d e f g) =
                                     [Some a, Some b, Some c, None, Some d, Some e, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed5_4 a b c d ()) =
                                     [Some a, Some b, Some c, Some d, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed5_5 a b c d () e) =
                                     [Some a, Some b, Some c, Some d, None, Some e]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed5_6 a b c d () e f) =
                                     [Some a, Some b, Some c, Some d, None, Some e, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed5_7 a b c d () e f g) =
                                     [Some a, Some b, Some c, Some d, None, Some e, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed6_5 a b c d e ()) =
                                     [Some a, Some b, Some c, Some d, Some e, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed6_6 a b c d e () f) =
                                     [Some a, Some b, Some c, Some d, Some e, None, Some f]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed6_7 a b c d e () f g) =
                                     [Some a, Some b, Some c, Some d, Some e, None, Some f, Some g]"
  
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed7_6 a b c d e f ()) =
                                     [Some a, Some b, Some c, Some d, Some e, Some f, None]"
    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed7_7 a b c d e f () g) =
                                     [Some a, Some b, Some c, Some d, Some e, Some f, None, Some g]"


(*for all ipv6_syntax, there is a corresponding list representation*)
lemma parse_ipv6_address_exists:
      fixes ipv6_syntax::ipv6addr_syntax_compressed
      shows "\<exists>ss. parse_ipv6_address ss = Some ipv6_syntax"
  apply(rule_tac x="ipv6addr_syntax_compressed_to_list ipv6_syntax" in exI)
  apply(case_tac ipv6_syntax) (*takes quite long until output panel shows sth.*)
                                     apply(simp_all)
  done

lemma parse_ipv6_address_identity:
      "parse_ipv6_address (ipv6addr_syntax_compressed_to_list (ipv6_syntax)) = Some ipv6_syntax"
  by(cases ipv6_syntax) simp_all

(* won't load in reasonable time
 fun parse_ipv6_address2 :: "((16 word) option) list \<Rightarrow> ipv6addr_syntax_compressed option" where
      "parse_ipv6_address2 [None] = Some (IPv6AddrCompressed1_0 ())"
    | "parse_ipv6_address2 [None, Some a] = Some (IPv6AddrCompressed1_1 () a)"
    | "parse_ipv6_address2 [None, Some a, Some b] = Some (IPv6AddrCompressed1_2 () a b)"
    | "parse_ipv6_address2 [None, Some a, Some b, Some c] = Some (IPv6AddrCompressed1_3 () a b c)"
    | "parse_ipv6_address2 [None, Some a, Some b, Some c, Some d] = Some (IPv6AddrCompressed1_4 () a b c d)"
    | "parse_ipv6_address2 [None, Some a, Some b, Some c, Some d, Some e] = Some (IPv6AddrCompressed1_5 () a b c d e)"
    | "parse_ipv6_address2 [None, Some a, Some b, Some c, Some d, Some e, Some f] = Some (IPv6AddrCompressed1_6 () a b c d e f)"
    | "parse_ipv6_address2 [None, Some a, Some b, Some c, Some d, Some e, Some f, Some g] = Some (IPv6AddrCompressed1_7 () a b c d e f g)"
  
    | "parse_ipv6_address2 [Some a, None] = Some (IPv6AddrCompressed2_1 a ())"
    | "parse_ipv6_address2 [Some a, None, Some b] = Some (IPv6AddrCompressed2_2 a () b)"
    | "parse_ipv6_address2 [Some a, None, Some b, Some c] = Some (IPv6AddrCompressed2_3 a () b c)"
    | "parse_ipv6_address2 [Some a, None, Some b, Some c, Some d] = Some (IPv6AddrCompressed2_4 a () b c d)"
    | "parse_ipv6_address2 [Some a, None, Some b, Some c, Some d, Some e] = Some (IPv6AddrCompressed2_5 a () b c d e)"
    | "parse_ipv6_address2 [Some a, None, Some b, Some c, Some d, Some e, Some f] = Some (IPv6AddrCompressed2_6 a () b c d e f)"
    | "parse_ipv6_address2 [Some a, None, Some b, Some c, Some d, Some e, Some f, Some g] = Some (IPv6AddrCompressed2_7 a () b c d e f g)"
  
    | "parse_ipv6_address2 [Some a, Some b, None] = Some (IPv6AddrCompressed3_2 a b ())"
    | "parse_ipv6_address2 [Some a, Some b, None, Some c] = Some (IPv6AddrCompressed3_3 a b () c)"
    | "parse_ipv6_address2 [Some a, Some b, None, Some c, Some d] = Some (IPv6AddrCompressed3_4 a b () c d)"
    | "parse_ipv6_address2 [Some a, Some b, None, Some c, Some d, Some e] = Some (IPv6AddrCompressed3_5 a b () c d e)"
    | "parse_ipv6_address2 [Some a, Some b, None, Some c, Some d, Some e, Some f] = Some (IPv6AddrCompressed3_6 a b () c d e f)"
    | "parse_ipv6_address2 [Some a, Some b, None, Some c, Some d, Some e, Some f, Some g] = Some (IPv6AddrCompressed3_7 a b () c d e f g)"
  
    | "parse_ipv6_address2 [Some a, Some b, Some c, None] = Some (IPv6AddrCompressed4_3 a b c ())"
    | "parse_ipv6_address2 [Some a, Some b, Some c, None, Some d] = Some (IPv6AddrCompressed4_4 a b c () d)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, None, Some d, Some e] = Some (IPv6AddrCompressed4_5 a b c () d e)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, None, Some d, Some e, Some f] = Some (IPv6AddrCompressed4_6 a b c () d e f)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, None, Some d, Some e, Some f, Some g] = Some (IPv6AddrCompressed4_7 a b c () d e f g)"
  
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, None] = Some (IPv6AddrCompressed5_4 a b c d ())"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, None, Some e] = Some (IPv6AddrCompressed5_5 a b c d () e)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, None, Some e, Some f] = Some (IPv6AddrCompressed5_6 a b c d () e f)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, None, Some e, Some f, Some g] = Some (IPv6AddrCompressed5_7 a b c d () e f g)"
  
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, Some e, None] = Some (IPv6AddrCompressed6_5 a b c d e ())"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, Some e, None, Some f] = Some (IPv6AddrCompressed6_6 a b c d e () f)"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, Some e, None, Some f, Some g] = Some (IPv6AddrCompressed6_7 a b c d e () f g)"
  
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, Some e, Some f, None] = Some (IPv6AddrCompressed7_6 a b c d e f ())"
    | "parse_ipv6_address2 [Some a, Some b, Some c, Some d, Some e, Some f, None, Some g] = Some (IPv6AddrCompressed7_7 a b c d e f () g)"
    | "parse_ipv6_address2 _ = None"
*)

(* infeasible proof
lemma "parse_ipv6_address as = Some ipv6 \<Longrightarrow>
  \<exists>a b c d e f g.
    as = [None] \<and> ipv6 = (IPv6AddrCompressed1_0 ()) \<or> 
    as = [None, Some a] \<and> ipv6 = (IPv6AddrCompressed1_1 () a) \<or> 
    as = [None, Some a, Some b] \<and> ipv6 = (IPv6AddrCompressed1_2 () a b) \<or> 
    as = [None, Some a, Some b, Some c] \<and> ipv6 = (IPv6AddrCompressed1_3 () a b c) \<or> 
    as = [None, Some a, Some b, Some c, Some d] \<and> ipv6 = (IPv6AddrCompressed1_4 () a b c d) \<or> 
    as = [None, Some a, Some b, Some c, Some d, Some e] \<and> ipv6 = (IPv6AddrCompressed1_5 () a b c d e) \<or> 
    as = [None, Some a, Some b, Some c, Some d, Some e, Some f] \<and> ipv6 = (IPv6AddrCompressed1_6 () a b c d e f) \<or> 
    as = [None, Some a, Some b, Some c, Some d, Some e, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed1_7 () a b c d e f g) \<or>
  
    as = [Some a, None] \<and> ipv6 = (IPv6AddrCompressed2_1 a ()) \<or> 
    as = [Some a, None, Some b] \<and> ipv6 = (IPv6AddrCompressed2_2 a () b) \<or> 
    as = [Some a, None, Some b, Some c] \<and> ipv6 = (IPv6AddrCompressed2_3 a () b c) \<or> 
    as = [Some a, None, Some b, Some c, Some d] \<and> ipv6 = (IPv6AddrCompressed2_4 a () b c d) \<or> 
    as = [Some a, None, Some b, Some c, Some d, Some e] \<and> ipv6 = (IPv6AddrCompressed2_5 a () b c d e) \<or> 
    as = [Some a, None, Some b, Some c, Some d, Some e, Some f] \<and> ipv6 = (IPv6AddrCompressed2_6 a () b c d e f) \<or> 
    as = [Some a, None, Some b, Some c, Some d, Some e, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed2_7 a () b c d e f g) \<or>
  
    as = [Some a, Some b, None] \<and> ipv6 = (IPv6AddrCompressed3_2 a b ()) \<or> 
    as = [Some a, Some b, None, Some c] \<and> ipv6 = (IPv6AddrCompressed3_3 a b () c) \<or> 
    as = [Some a, Some b, None, Some c, Some d] \<and> ipv6 = (IPv6AddrCompressed3_4 a b () c d) \<or> 
    as = [Some a, Some b, None, Some c, Some d, Some e] \<and> ipv6 = (IPv6AddrCompressed3_5 a b () c d e) \<or> 
    as = [Some a, Some b, None, Some c, Some d, Some e, Some f] \<and> ipv6 = (IPv6AddrCompressed3_6 a b () c d e f) \<or> 
    as = [Some a, Some b, None, Some c, Some d, Some e, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed3_7 a b () c d e f g) \<or>
  
    as = [Some a, Some b, Some c, None] \<and> ipv6 = (IPv6AddrCompressed4_3 a b c ()) \<or> 
    as = [Some a, Some b, Some c, None, Some d] \<and> ipv6 = (IPv6AddrCompressed4_4 a b c () d) \<or> 
    as = [Some a, Some b, Some c, None, Some d, Some e] \<and> ipv6 = (IPv6AddrCompressed4_5 a b c () d e) \<or> 
    as = [Some a, Some b, Some c, None, Some d, Some e, Some f] \<and> ipv6 = (IPv6AddrCompressed4_6 a b c () d e f) \<or> 
    as = [Some a, Some b, Some c, None, Some d, Some e, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed4_7 a b c () d e f g) \<or>
  
    as = [Some a, Some b, Some c, Some d, None] \<and> ipv6 = (IPv6AddrCompressed5_4 a b c d ()) \<or> 
    as = [Some a, Some b, Some c, Some d, None, Some e] \<and> ipv6 = (IPv6AddrCompressed5_5 a b c d () e) \<or> 
    as = [Some a, Some b, Some c, Some d, None, Some e, Some f] \<and> ipv6 = (IPv6AddrCompressed5_6 a b c d () e f) \<or> 
    as = [Some a, Some b, Some c, Some d, None, Some e, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed5_7 a b c d () e f g) \<or>
  
    as = [Some a, Some b, Some c, Some d, Some e, None] \<and> ipv6 = (IPv6AddrCompressed6_5 a b c d e ()) \<or> 
    as = [Some a, Some b, Some c, Some d, Some e, None, Some f] \<and> ipv6 = (IPv6AddrCompressed6_6 a b c d e () f) \<or> 
    as = [Some a, Some b, Some c, Some d, Some e, None, Some f, Some g] \<and> ipv6 = (IPv6AddrCompressed6_7 a b c d e () f g) \<or>
  
    as = [Some a, Some b, Some c, Some d, Some e, Some f, None] \<and> ipv6 = (IPv6AddrCompressed7_6 a b c d e f ()) \<or> 
    as = [Some a, Some b, Some c, Some d, Some e, Some f, None, Some g] \<and> ipv6 = (IPv6AddrCompressed7_7 a b c d e f () g)"
apply simp
apply(case_tac as)
 apply(simp_all)
apply(rename_tac a as')
apply(case_tac a)
 apply(simp_all)
 apply(case_tac as')
  apply(simp_all)
 apply(rename_tac aa aas')
 apply(case_tac aa)
  apply(simp_all)
 apply(rename_tac aaa aaas')
 apply(case_tac aaa)
  apply(simp_all)
 apply(rename_tac aaaa aaaas')
 apply(case_tac aaaa)
  apply(simp_all)
 apply(rename_tac aaaaa aaaaas')
 apply(case_tac aaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaa aaaaaas')
 apply(case_tac aaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaa aaaaaaas')
 apply(case_tac aaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaa aaaaaaaas')
 apply(case_tac aaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaa aaaaaaaaas')
 apply(case_tac aaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaa aaaaaaaaaas')
 apply(case_tac aaaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaaa aaaaaaaaaaas')
 apply(case_tac aaaaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaaaa aaaaaaaaaaaas')
 apply(case_tac aaaaaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaaaaa aaaaaaaaaaaaas')
 apply(case_tac aaaaaaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaaaaaa aaaaaaaaaaaaaas')
 apply(case_tac aaaaaaaaaaaaaa)
  apply(simp_all)
 apply(rename_tac aaaaaaaaaaaaaaa aaaaaaaaaaaaaaas')
 apply(case_tac aaaaaaaaaaaaaaa)
  apply(simp_all)
(*yay*)
apply(rename_tac b a as')
apply(case_tac a)
 apply(simp_all)
 apply(case_tac as')
  apply(simp_all)
 apply(rename_tac bb aa aas')
 apply(case_tac bb)
  apply(simp_all)
(*now the same again? several times?*)
*)

lemma parse_ipv6_address_identity2:
      "ipv6addr_syntax_compressed_to_list ipv6_syntax = ls \<longleftrightarrow> (parse_ipv6_address ls) = Some ipv6_syntax"
  apply(cases ipv6_syntax)
  apply simp_all
  oops (*TODO*)

text{*Valid IPv6 compressed notation:
  \<^item> at most one omission
  \<^item> at most 7 pieces
*}
lemma "parse_ipv6_address as \<noteq> None \<longleftrightarrow>
       length (filter (\<lambda>p. p = None) as) = 1 \<and>
       length as \<le> 7"
  apply(induction as)
   apply(simp)
  apply(simp del: parse_ipv6_address.simps)
  apply(intro conjI impI)
   apply simp
   
   apply(simp del: parse_ipv6_address.simps)
  oops (*TODO*)

text{*
  3. An alternative form that is sometimes more convenient when dealing
      with a mixed environment of IPv4 and IPv6 nodes is
      x:x:x:x:x:x:d.d.d.d, where the 'x's are the hexadecimal values of
      the six high-order 16-bit pieces of the address, and the 'd's are
      the decimal values of the four low-order 8-bit pieces of the
      address (standard IPv4 representation).  Examples:

         0:0:0:0:0:0:13.1.68.3
         0:0:0:0:0:FFFF:129.144.52.38

      or in compressed form:

         ::13.1.68.3
         ::FFFF:129.144.52.38
*}
  (*TODO*)
  (*TODO: oh boy, they can also be compressed*)

subsection{*Semantics*}
  fun ipv6preferred_to_int :: "ipv6addr_syntax \<Rightarrow> ipv6addr" where
    "ipv6preferred_to_int (IPv6AddrPreferred a b c d e f g h) = (ucast a << (16 * 7)) OR
                                                                (ucast b << (16 * 6)) OR
                                                                (ucast c << (16 * 5)) OR
                                                                (ucast d << (16 * 4)) OR
                                                                (ucast e << (16 * 3)) OR
                                                                (ucast f << (16 * 2)) OR
                                                                (ucast g << (16 * 1)) OR
                                                                (ucast h << (16 * 0))"

  lemma "ipv6preferred_to_int (IPv6AddrPreferred 0x2001 0xDB8 0x0 0x0 0x8 0x800 0x200C 0x417A) = 
          42540766411282592856906245548098208122" by eval

  lemma "ipv6preferred_to_int (IPv6AddrPreferred 0xFF01 0x0 0x0 0x0 0x0 0x0 0x0 0x101) = 
          338958331222012082418099330867817087233" by eval

  declare ipv6preferred_to_int.simps[simp del]


  definition int_to_ipv6preferred :: "ipv6addr \<Rightarrow> ipv6addr_syntax" where
    "int_to_ipv6preferred i = IPv6AddrPreferred (ucast ((i AND 0xFFFF0000000000000000000000000000) >> 16*7))
                                                (ucast ((i AND 0xFFFF000000000000000000000000) >> 16*6))
                                                (ucast ((i AND 0xFFFF00000000000000000000) >> 16*5))
                                                (ucast ((i AND 0xFFFF0000000000000000) >> 16*4))
                                                (ucast ((i AND 0xFFFF000000000000) >> 16*3))
                                                (ucast ((i AND 0xFFFF00000000) >> 16*2))
                                                (ucast ((i AND 0xFFFF0000) >> 16*1))
                                                (ucast ((i AND 0xFFFF)))"

  lemma "int_to_ipv6preferred 42540766411282592856906245548098208122 =
         IPv6AddrPreferred 0x2001 0xDB8 0x0 0x0 0x8 0x800 0x200C 0x417A" by eval

  lemma "word_of_int (uint ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)))))  = 
          ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))"
    apply(subst word_of_int_uint)
    ..

  lemma x: "(word_of_int:: int \<Rightarrow> 'b::len0 word) (uint ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))) << (112::nat) = 
          ((word_of_int::int \<Rightarrow> 'b::len0 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))  << 112"
    apply(subst word_of_int_uint)
    ..

  (*I could also use word_split to extract bits?*)
  
  lemma word128_mask112: "(0xFFFF0000000000000000000000000000::ipv6addr) = (mask 16) << 112"
    by(simp add: mask_def)
  lemma xxx: fixes ip::ipv6addr
    shows  "((ip >> 112) && mask 16) = (ip >> 112)"
    proof -
      have "size ip = 128" by( simp add: word_size)
      with WordLemmaBucket.shiftr_mask_eq[of ip 112] show ?thesis by simp
    qed
    
  lemma "of_bl (to_bl x) = x" by simp
 
  value "(slice 112 (0xFFFF0000000000000000000000000000::ipv6addr))::16 word"
  thm slice_shiftr

  lemma "of_bl (to_bl (of_bl (to_bl x))) = x"
  proof -
   have 1: "of_bl (to_bl x) = x"
    apply(subst Word.word_bl.Rep_inverse) ..
   show "of_bl (to_bl (of_bl (to_bl x))) = x"
    apply(subst 1)
  oops

  lemma "xx && ~~ mask y >> y = ( (xx && (~~ (mask y))) >> y  )" by simp

  (*fun story: sledgehammer does not find this one!*)
  lemma mask_16_shiftl112_128word: "((mask 16 << 112)::128 word) = ~~ mask 112"
    by(simp add: mask_def)

  lemma word128_and_slice112:
    fixes ip::ipv6addr
    shows "(ip AND 0xFFFF0000000000000000000000000000 >> 112) = slice 112 ip"
    apply(subst Word.shiftr_slice[symmetric])
    apply(subst word128_mask112)
    apply(subst mask_16_shiftl112_128word)
    apply(subst WordLemmaBucket.mask_shift)
    apply simp
    done

  lemma helpx16: 
    fixes w::"16 word"
    shows "uint ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl w)) = uint w"
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp)
    apply(simp)
    done

  lemma helpx128:
    fixes w::"128 word"
    shows "length (to_bl w) \<le> 16 \<Longrightarrow> 
           uint ((of_bl:: bool list \<Rightarrow> 16 word) (to_bl (w))) = 
           uint w "
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp)
    apply(simp)
    done

  value "bintrunc 3 0x0"

  lemma uint_bl_less_length: "uint (of_bl ls) < 2 ^ length ls"
    by (metis bintrunc_bintrunc_min bl_to_bin_lt2p lt2p_lem min_def of_bl_def trunc_bl2bin_len word_ubin.inverse_norm)


  value "let ls = [True,True,True,True,True,True,True,True,True,True,True,True,True,True,True,True] in 
    (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl::bool list \<Rightarrow> 16 word) (True # ls))) = 
    of_bl (True # ls)"
  lemma "length ls < 16 \<Longrightarrow> 
    (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl::bool list \<Rightarrow> 16 word) (True # ls))) = 
    of_bl (True # ls)"
    quickcheck
    apply(simp)
    apply(rule Word.word_uint_eqI)
    apply(subst helpx16)
    
    (*apply(subst Word.uint_plus_if')
    apply(simp)
    apply(intro conjI impI)*)
     
    apply(subst Word.uint_word_ariths(1))+

    apply(subst Word_Miscellaneous.push_mods(1))
    apply(subst Word_Miscellaneous.push_mods(1)) back

    apply(case_tac ls)
    apply(simp)
    apply(case_tac list)
    apply(simp)
    
    
    apply(simp)
    using [[ML_print_depth=100]] ML_val \<open>@{Isar.goal} |> #goal |> Thm.prop_of\<close>
    oops

  lemma "to_bl (of_bl (False # ls)) = to_bl (of_bl ls)" oops

  value "to_bl ((of_bl [False])::ipv6addr)"
  lemma "n \<le> 16 \<Longrightarrow> length (to_bl (of_bl (take n ls))) \<le> 16"
    apply(simp)
    oops

(*copy of lemma (*uint_of_bl_is_bl_to_bin: l4v WordLib*)
  "length l\<le>len_of TYPE('a) \<Longrightarrow>
   uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans, rule bl_to_bin_lt2p)
  apply (rule order_trans, erule power_increasing)
   apply simp_all
  done*)


(*TODO: add to l4v bl_to_bin_lt2p*)
thm Bool_List_Representation.bl_to_bin_lt2p
lemma bl_to_bin_lt2p_Not: "bl_to_bin bs < (2 ^ length (dropWhile Not bs))"
  apply (unfold bl_to_bin_def)
  apply(induction bs)
   apply(simp)
  apply(simp)
  by (metis bl_to_bin_lt2p_aux one_add_one)

(*TODO: add to l4v uint_of_bl_is_bl_to_bin*)
thm WordLib.uint_of_bl_is_bl_to_bin
lemma uint_of_bl_is_bl_to_bin_Not:
  "length (dropWhile Not l) \<le> len_of TYPE('a) \<Longrightarrow>
   uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply (simp add: of_bl_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num bl_to_bin_ge0)
  apply (rule order_less_le_trans)
  apply (rule bl_to_bin_lt2p_Not)
  apply(simp)
  done


lemma length_takeWhile_Not_replicate_False:
  "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
  by (metis in_set_replicate length_append length_replicate takeWhile_append2)


lemma length_dropWhile_Not_bl: "length (dropWhile Not (to_bl (of_bl bs))) \<le> length bs"
 apply(subst Word.word_rep_drop)
 apply(subst List.dropWhile_eq_drop)
 apply(simp)
 apply(subst length_takeWhile_Not_replicate_False)
 apply(simp)
 done
 
thm Word.word_bl_Rep'
  
  (*TODO: add to l4v*)
  (*taking only the high-order bits from a bitlist, casting to a longer word and casting back to
    a shorter type, casting to to longer type again is equal to just taking the bits and casting to
    the longer type.
    'l is the longer word. E.g. 128 bit
    's is the shorter word. E.g. 16 bit
  *)
  lemma bl_cast_long_short_long_take:
  "n \<le> len_of TYPE('s) \<Longrightarrow> len_of TYPE('s) \<le> len_of TYPE('l) \<Longrightarrow>
    of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 's::len word) 
            (to_bl ((of_bl:: bool list \<Rightarrow> 'l::len word) (take n ls))))) =
    (of_bl:: bool list \<Rightarrow> 'l::len word) (take n ls)"
    apply(rule Word.word_uint_eqI)
    apply(subst WordLib.uint_of_bl_is_bl_to_bin)
     apply(simp; fail)
    apply(subst Word.to_bl_bin)
    apply(subst uint_of_bl_is_bl_to_bin_Not)
     apply(subgoal_tac "length (take n ls) \<le> len_of TYPE('s)")
      prefer 2
      apply fastforce
     apply(subgoal_tac "length (dropWhile Not (to_bl (of_bl (take n ls)))) \<le> length (take n ls)")
      using dual_order.trans apply blast
     using length_dropWhile_Not_bl apply blast
    apply(simp)
    done

corollary yaaaaaaaaaaaaaaaayaiohhgoo: 
  "n \<le> 16 \<Longrightarrow> of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 16 word)
            (to_bl ((of_bl:: bool list \<Rightarrow> 128 word) (take n ls))))) =
    (of_bl:: bool list \<Rightarrow> 128 word) (take n ls)"
  apply(rule bl_cast_long_short_long_take)
   apply(simp_all)
  done

  (*this would be nice*)
  lemma hooo: fixes ip::ipv6addr
    shows "length ls \<le> 16 \<Longrightarrow> 
     of_bl (to_bl ((of_bl:: bool list \<Rightarrow> 16 word)
            (to_bl ((of_bl:: bool list \<Rightarrow> 128 word) ls)))) =
    (of_bl:: bool list \<Rightarrow> 128 word) ls"
    oops




  lemma ucast16_ucast128_maks_highest_bits: fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst word128_and_slice112)
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_bl)
    apply(simp)
    apply(subst word128_mask112)+
    apply(subst WordLemmaBucket.word_and_mask_shiftl)+
    apply(subst xxx)+
    apply(subst Word.shiftr_bl)
    apply(subst Word.shiftl_bl)
    apply simp
    apply(subst Word.of_bl_append)+
    apply simp
    apply(subst Word.slice_take)
    apply(simp)
    thm yaaaaaaaaaaaaaaaayaiohhgoo
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    done

  (*the same without slice to generalize to the other cases*)
  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst word128_mask112)
    apply(subst mask_16_shiftl112_128word)
    apply(subst WordLemmaBucket.mask_shift)
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_bl)
    apply(simp)
    apply(subst word128_mask112)+
    apply(subst WordLemmaBucket.word_and_mask_shiftl)+
    apply(subst xxx)+
    apply(subst Word.shiftr_bl)
    apply(subst Word.shiftl_bl)
    apply simp
    apply(subst Word.of_bl_append)+
    apply simp
    apply(subst Word.shiftr_bl)
    apply(simp)
    thm yaaaaaaaaaaaaaaaayaiohhgoo
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    done

  lemma word128_mask96: "(0xFFFF000000000000000000000000::ipv6addr) = (mask 16) << 96"
    by(simp add: mask_def)

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000000000000000 >> 96)) << 96) =
         ip AND 0xFFFF000000000000000000000000"
    apply(subst word128_mask96)
    apply(subst Word.ucast_bl)+
    apply(subst Word.shiftl_bl)
    apply(simp)
    apply(subst word128_mask96)+
    apply(subst WordLemmaBucket.word_and_mask_shiftl)+
    apply(subst Word.shiftr_bl)
    apply(subst Word.shiftl_bl)
    apply simp
    apply(subst Word.of_bl_append)+
    apply simp
    apply(subst Word.shiftr_bl)
    apply(simp)
    thm yaaaaaaaaaaaaaaaayaiohhgoo
    thm bl_cast_long_short_long_take
    apply(subst bl_cast_long_short_long_take_sorry)
    apply(subst bl_cast_long_short_long_take[symmetric]) back
     apply simp_all (*c'mon! take32 fuu!*)
    oops


  lemma "ip \<le> 2^(len_of TYPE(16)) \<Longrightarrow> (ucast::16 word \<Rightarrow> 128 word) ((ucast::128 word \<Rightarrow> 16 word) ip) = ip"
    apply(simp add: ucast_def)
    oops
    
    

 lemma Word_ucast_bl_16_128:
  "(ucast::16 word \<Rightarrow> ipv6addr) ((ucast::ipv6addr \<Rightarrow> 16 word) ip) =
   (of_bl:: bool list \<Rightarrow> 128 word) (to_bl ((of_bl:: bool list \<Rightarrow> 16 word) ((to_bl:: 128 word \<Rightarrow> bool list) ip)))"
    apply(subst Word.ucast_bl)+
    apply simp
    done

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (slice 112 ip)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    apply(subst Word_ucast_bl_16_128)
    apply(subst Word.shiftl_bl)
    apply(simp)
    apply(subst word128_mask112)+
    apply(subst WordLemmaBucket.word_and_mask_shiftl)+
    apply(subst xxx)+
    apply(subst Word.shiftr_bl)
    apply(subst Word.shiftl_bl)
    apply simp
    apply(subst Word.of_bl_append)+
    apply simp
    apply(subst Word.slice_take)+
    apply(simp)
    apply(subst yaaaaaaaaaaaaaaaayaiohhgoo)
     apply simp_all
    oops

  lemma fixes ip::ipv6addr
    shows "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
           (ip AND 0xFFFF0000000000000000000000000000)"
    using ucast16_ucast128_maks_highest_bits by simp
    (*proof -
      have "(word_of_int::int \<Rightarrow> 128 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))) << (112::nat) =
           ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat) << (112::nat)"
      by simp
      show "(word_of_int :: int \<Rightarrow> 128 word) (uint 
          ((word_of_int :: int \<Rightarrow> 16 word) (uint (ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat))))) << (112::nat) =
    ip && (0xFFFF0000000000000000000000000000::128 word)"
        apply(simp)
        done
    apply(simp add: ucast_def)
    apply(subst x)
    thm word_of_int_uint
    thm Word.word_of_int_uint[of "ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)"]
    apply(subst Word.word_of_int_uint[of "ip && (0xFFFF0000000000000000000000000000::128 word) >> (112::nat)"])
    apply simp
    apply(simp add: Word.word_of_int_uint)
    oops*)

  (*TODO: round trip property one*)
  lemma "ipv6preferred_to_int (int_to_ipv6preferred ip) = ip"
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    apply(simp add: ucast16_ucast128_maks_highest_bits)
    oops
    

  (*TODO: round trip property two*)
  lemma "int_to_ipv6preferred (ipv6preferred_to_int ip) = ip"
    apply(cases ip, rename_tac a b c d e f g h)
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    oops

end
