(*  Title:      IPv6Addr.thy
    Authors:    Cornelius Diekmann
*)
theory IPv6Addr
imports Main
  NumberWang
  WordInterval_Lists
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

subsection{*Representing IPv6 Adresses*}
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
  datatype ipv6addr_syntax_compressed =
  (*using unit for the omission :: 
    The first number is the position where the omission occurs.
    The second number is the length of the specified address pieces.
      I.e. `8 minus the second number' pieces are omitted.*)
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
  (*datatype may take a minute to load*)

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

end
