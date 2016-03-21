(*  Title:      IPv6Addr.thy
    Authors:    Cornelius Diekmann
*)
theory IPv6Addr
imports IPv6Bitmagic
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

  | IPv6AddrCompressed8_7 "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" unit

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
  definition parse_ipv6_address :: "((16 word) option) list \<Rightarrow> ipv6addr_syntax_compressed option" where
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

    | [Some a, Some b, Some c, Some d, Some e, Some f, Some g, None] \<Rightarrow> Some (IPv6AddrCompressed8_7 a b c d e f g ())
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

    | "ipv6addr_syntax_compressed_to_list (IPv6AddrCompressed8_7 a b c d e f g ()) =
                                     [Some a, Some b, Some c, Some d, Some e, Some f, Some g, None]"


(*for all ipv6_syntax, there is a corresponding list representation*)
lemma parse_ipv6_address_exists:
  obtains ss where "parse_ipv6_address ss = Some ipv6_syntax"
  proof
    def ss \<equiv> "ipv6addr_syntax_compressed_to_list ipv6_syntax"
    thus "parse_ipv6_address ss = Some ipv6_syntax"
      by (cases ipv6_syntax; simp add: parse_ipv6_address_def)
  qed

lemma parse_ipv6_address_identity:
      "parse_ipv6_address (ipv6addr_syntax_compressed_to_list (ipv6_syntax)) = Some ipv6_syntax"
  by(cases ipv6_syntax; simp add: parse_ipv6_address_def)

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

lemma parse_ipv6_address_someE:
  assumes "parse_ipv6_address as = Some ipv6"
  obtains
    "as = [None]" "ipv6 = (IPv6AddrCompressed1_0 ())"  |
    a where "as = [None, Some a]" "ipv6 = (IPv6AddrCompressed1_1 () a)"  |
    a b where "as = [None, Some a, Some b]" "ipv6 = (IPv6AddrCompressed1_2 () a b)"  |
    a b c where "as = [None, Some a, Some b, Some c]" "ipv6 = (IPv6AddrCompressed1_3 () a b c)" |
    a b c d where "as = [None, Some a, Some b, Some c, Some d]" "ipv6 = (IPv6AddrCompressed1_4 () a b c d)" |
    a b c d e where "as = [None, Some a, Some b, Some c, Some d, Some e]" "ipv6 = (IPv6AddrCompressed1_5 () a b c d e)" |
    a b c d e f where "as = [None, Some a, Some b, Some c, Some d, Some e, Some f]" "ipv6 = (IPv6AddrCompressed1_6 () a b c d e f)" |
    a b c d e f g where "as = [None, Some a, Some b, Some c, Some d, Some e, Some f, Some g]" "ipv6 = (IPv6AddrCompressed1_7 () a b c d e f g)" |
  
    a where "as = [Some a, None]" "ipv6 = (IPv6AddrCompressed2_1 a ())" |
    a b where "as = [Some a, None, Some b]" "ipv6 = (IPv6AddrCompressed2_2 a () b)" |
    a b c where "as = [Some a, None, Some b, Some c]" "ipv6 = (IPv6AddrCompressed2_3 a () b c)" |
    a b c d where "as = [Some a, None, Some b, Some c, Some d]" "ipv6 = (IPv6AddrCompressed2_4 a () b c d)" |
    a b c d e where "as = [Some a, None, Some b, Some c, Some d, Some e]" "ipv6 = (IPv6AddrCompressed2_5 a () b c d e)" |
    a b c d e f where "as = [Some a, None, Some b, Some c, Some d, Some e, Some f]" "ipv6 = (IPv6AddrCompressed2_6 a () b c d e f)" |
    a b c d e f g where "as = [Some a, None, Some b, Some c, Some d, Some e, Some f, Some g]" "ipv6 = (IPv6AddrCompressed2_7 a () b c d e f g)" |
  
    a b where "as = [Some a, Some b, None]" "ipv6 = (IPv6AddrCompressed3_2 a b ())" |
    a b c where "as = [Some a, Some b, None, Some c]" "ipv6 = (IPv6AddrCompressed3_3 a b () c)" |
    a b c d where "as = [Some a, Some b, None, Some c, Some d]" "ipv6 = (IPv6AddrCompressed3_4 a b () c d)" |
    a b c d e where "as = [Some a, Some b, None, Some c, Some d, Some e]" "ipv6 = (IPv6AddrCompressed3_5 a b () c d e)" |
    a b c d e f where "as = [Some a, Some b, None, Some c, Some d, Some e, Some f]" "ipv6 = (IPv6AddrCompressed3_6 a b () c d e f)" |
    a b c d e f g where "as = [Some a, Some b, None, Some c, Some d, Some e, Some f, Some g]" "ipv6 = (IPv6AddrCompressed3_7 a b () c d e f g)" |
  
    a b c where "as = [Some a, Some b, Some c, None]" "ipv6 = (IPv6AddrCompressed4_3 a b c ())" |
    a b c d where "as = [Some a, Some b, Some c, None, Some d]" "ipv6 = (IPv6AddrCompressed4_4 a b c () d)" |
    a b c d e where "as = [Some a, Some b, Some c, None, Some d, Some e]" "ipv6 = (IPv6AddrCompressed4_5 a b c () d e)" |
    a b c d e f where "as = [Some a, Some b, Some c, None, Some d, Some e, Some f]" "ipv6 = (IPv6AddrCompressed4_6 a b c () d e f)" |
    a b c d e f g where "as = [Some a, Some b, Some c, None, Some d, Some e, Some f, Some g]" "ipv6 = (IPv6AddrCompressed4_7 a b c () d e f g)" |
  
    a b c d where "as = [Some a, Some b, Some c, Some d, None]" "ipv6 = (IPv6AddrCompressed5_4 a b c d ())" |
    a b c d e where "as = [Some a, Some b, Some c, Some d, None, Some e]" "ipv6 = (IPv6AddrCompressed5_5 a b c d () e)" |
    a b c d e f where "as = [Some a, Some b, Some c, Some d, None, Some e, Some f]" "ipv6 = (IPv6AddrCompressed5_6 a b c d () e f)" |
    a b c d e f g where "as = [Some a, Some b, Some c, Some d, None, Some e, Some f, Some g]" "ipv6 = (IPv6AddrCompressed5_7 a b c d () e f g)" |
  
    a b c d e where "as = [Some a, Some b, Some c, Some d, Some e, None]" "ipv6 = (IPv6AddrCompressed6_5 a b c d e ())" |
    a b c d e f where "as = [Some a, Some b, Some c, Some d, Some e, None, Some f]" "ipv6 = (IPv6AddrCompressed6_6 a b c d e () f)" |
    a b c d e f g where "as = [Some a, Some b, Some c, Some d, Some e, None, Some f, Some g]" "ipv6 = (IPv6AddrCompressed6_7 a b c d e () f g)" |
  
    a b c d e f where "as = [Some a, Some b, Some c, Some d, Some e, Some f, None]" "ipv6 = (IPv6AddrCompressed7_6 a b c d e f ())" |
    a b c d e f g where "as = [Some a, Some b, Some c, Some d, Some e, Some f, None, Some g]" "ipv6 = (IPv6AddrCompressed7_7 a b c d e f () g)" |

    a b c d e f g where "as = [Some a, Some b, Some c, Some d, Some e, Some f, Some g, None]" "ipv6 = (IPv6AddrCompressed8_7 a b c d e f g ())"
using assms
unfolding parse_ipv6_address_def
by (auto split: list.split_asm option.split_asm) (* takes a minute *)

lemma parse_ipv6_address_identity2:
      "ipv6addr_syntax_compressed_to_list ipv6_syntax = ls \<longleftrightarrow> (parse_ipv6_address ls) = Some ipv6_syntax" (is "?lhs = ?rhs")
proof
  assume ?rhs
  thus ?lhs
    by (auto elim: parse_ipv6_address_someE)
next
  assume ?lhs
  thus ?rhs
    by (cases ipv6_syntax) (auto simp: parse_ipv6_address_def)
qed

text{*Valid IPv6 compressed notation:
  \<^item> at most one omission
  \<^item> at most 7 pieces
*}
lemma "parse_ipv6_address as \<noteq> None \<longleftrightarrow>
       length (filter (\<lambda>p. p = None) as) = 1 \<and>
       length (filter (\<lambda>p. p \<noteq> None) as) \<le> 7" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain addr where "parse_ipv6_address as = Some addr"
    by blast
  thus ?rhs
    by (elim parse_ipv6_address_someE; simp)
next
  assume ?rhs
  thus ?lhs
    unfolding parse_ipv6_address_def
    by (auto split: option.split list.split split_if_asm)
qed

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




  lemma word128_masks_ipv6pieces:
    "(0xFFFF0000000000000000000000000000::ipv6addr) = (mask 16) << 112"
    "(0xFFFF000000000000000000000000::ipv6addr) = (mask 16) << 96"
    "(0xFFFF00000000000000000000::ipv6addr) = (mask 16) << 80"
    "(0xFFFF0000000000000000::ipv6addr) = (mask 16) << 64"
    "(0xFFFF000000000000::ipv6addr) = (mask 16) << 48"
    "(0xFFFF00000000::ipv6addr) = (mask 16) << 32"
    "(0xFFFF0000::ipv6addr) = (mask 16) << 16"
    "(0xFFFF::ipv6addr) = (mask 16)"
    by(simp add: mask_def)+



  text{*Correctness: round trip property one*}
  lemma ipv6preferred_to_int_int_to_ipv6preferred:
    "ipv6preferred_to_int (int_to_ipv6preferred ip) = ip"
  proof -
    have and_mask_shift_helper: "w AND (mask m << n) >> n << n = w AND (mask m << n)"
      for m n::nat and w::ipv6addr
     proof - (*sledgehammered for 128 word and concrete values for m and n*)
       have f1: "\<And>w wa wb. ((w::'a::len word) && wa) && wb = w && wb && wa"
         by (simp add: word_bool_alg.conj_left_commute word_bw_comms(1))
       have "\<And>w n wa. ((w::'a::len word) && ~~ mask n) && (wa << n) = (w >> n) && wa << n"
         by (simp add: and_not_mask shiftl_over_and_dist)
       then show ?thesis
        by (simp add: is_aligned_mask is_aligned_shiftr_shiftl word_bool_alg.conj.assoc)
        (*using f1 by (metis (no_types) and_not_mask word_and_mask_shiftl word_bw_comms(1))*)
     qed
    have ucast_ipv6_piece_rule:
      "length (dropWhile Not (to_bl w)) \<le> 16 \<Longrightarrow> (ucast::16 word \<Rightarrow> 128 word) ((ucast::128 word \<Rightarrow> 16 word) w) = w"
      for w::ipv6addr 
      by(rule ucast_short_ucast_long_ingoreLeadingZero) (simp_all)
    have ucast_ipv6_piece: "16 \<le> 128 - n \<Longrightarrow> 
      (ucast::16 word \<Rightarrow> 128 word) ((ucast::128 word \<Rightarrow> 16 word) (w AND (mask 16 << n) >> n)) << n = w AND (mask 16 << n)"
      for w::ipv6addr and n::nat
      apply(subst ucast_ipv6_piece_rule)
       apply(rule length_dropNot_mask_inner)
       apply(simp; fail)
      apply(subst and_mask_shift_helper)
      apply simp
      done

    have ucast16_ucast128_masks_highest_bits:
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000000000000000 >> 112)) << 112) = 
             (ip AND 0xFFFF0000000000000000000000000000)"
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000000000000000 >> 96)) << 96) =
           ip AND 0xFFFF000000000000000000000000"
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF00000000000000000000 >> 80)) << 80) =
           ip AND 0xFFFF00000000000000000000" 
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000000000000000 >> 64)) << 64) =
           ip AND 0xFFFF0000000000000000"
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF000000000000 >> 48)) << 48) =
           ip AND 0xFFFF000000000000"
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF00000000 >> 32)) << 32) =
           ip AND 0xFFFF00000000"
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF0000 >> 16)) << 16) =
           ip AND 0xFFFF0000"
      by((subst word128_masks_ipv6pieces)+, subst ucast_ipv6_piece, simp_all)+

    have ucast16_ucast128_masks_highest_bits0: 
      "(ucast ((ucast::ipv6addr \<Rightarrow> 16 word) (ip AND 0xFFFF))) = ip AND 0xFFFF"
      apply(subst word128_masks_ipv6pieces)+
      apply(subst ucast_short_ucast_long_ingoreLeadingZero)
        apply simp_all
      by (simp add: length_dropNot_mask)

    have ipv6addr_16word_pieces_compose_or:
            "ip && (mask 16 << 112) ||
             ip && (mask 16 << 96) ||
             ip && (mask 16 << 80) ||
             ip && (mask 16 << 64) ||
             ip && (mask 16 << 48) ||
             ip && (mask 16 << 32) ||
             ip && (mask 16 << 16) ||
             ip && mask 16 =
             ip"
      apply(subst word_ao_dist2[symmetric])+
      apply(simp add: mask_def)
      apply(subst mask128)
      apply(rule mask_len_word)
      apply simp
      done

    show ?thesis
      apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
      apply(simp add: ucast16_ucast128_masks_highest_bits ucast16_ucast128_masks_highest_bits0)
      apply(simp add: word128_masks_ipv6pieces)
      apply(rule ipv6addr_16word_pieces_compose_or)
      done
  qed




  text{*Correctness: round trip property two*}
  lemma int_to_ipv6preferred_ipv6preferred_to_int: "int_to_ipv6preferred (ipv6preferred_to_int ip) = ip"
  proof -
    note ucast_shift_simps=helper_masked_ucast_generic helper_masked_ucast_reverse_generic
                           helper_masked_ucast_generic[where n=0, simplified]
                           helper_masked_ucast_equal_generic 
    note ucast_simps=helper_masked_ucast_reverse_generic[where m=0, simplified]
                     helper_masked_ucast_equal_generic[where n=0, simplified]
    show ?thesis
    apply(cases ip, rename_tac a b c d e f g h)
    apply(simp add: ipv6preferred_to_int.simps int_to_ipv6preferred_def)
    apply(simp add: word128_masks_ipv6pieces)
    apply(simp add: word_ao_dist ucast_shift_simps ucast_simps)
    done
  qed

end
