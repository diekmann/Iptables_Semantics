(*  Title:      IPv6.thy
    Authors:    Cornelius Diekmann
*)
theory IPv6
imports IP_Address
        NumberWang_IPv6
        (* include "~~/src/HOL/Library/Code_Target_Nat" if you need to work with actual numbers.*)
begin


section \<open>IPv6 Addresses\<close>
  text\<open>An IPv6 address is basically a 128 bit unsigned integer. RFC 4291, Section 2.\<close>
  type_synonym ipv6addr = "128 word"
 
  text\<open>Conversion between natural numbers and IPv6 adresses\<close>
  definition nat_of_ipv6addr :: "ipv6addr \<Rightarrow> nat" where
    "nat_of_ipv6addr a = unat a"
  definition ipv6addr_of_nat :: "nat \<Rightarrow> ipv6addr" where
    "ipv6addr_of_nat n =  of_nat n"

  lemma "ipv6addr_of_nat n = word_of_int (int n)"
    by(simp add: ipv6addr_of_nat_def word_of_nat)

  text\<open>The maximum IPv6 address\<close>
  definition max_ipv6_addr :: "ipv6addr" where 
    "max_ipv6_addr \<equiv> ipv6addr_of_nat ((2^128) - 1)"

  lemma max_ipv6_addr_number: "max_ipv6_addr = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    unfolding max_ipv6_addr_def ipv6addr_of_nat_def by(simp)
  lemma "max_ipv6_addr = 340282366920938463463374607431768211455"
    by(fact max_ipv6_addr_number)
  lemma max_ipv6_addr_max_word: "max_ipv6_addr = max_word"
    by(simp add: max_ipv6_addr_number max_word_def)
  lemma max_ipv6_addr_max: "\<forall>a. a \<le> max_ipv6_addr"
    by(simp add: max_ipv6_addr_max_word)
  lemma UNIV_ipv6addrset: "UNIV = {0 .. max_ipv6_addr}" (*not in the simp set, for a reason*)
    by(simp add: max_ipv6_addr_max_word) fastforce

  text\<open>identity functions\<close>
  lemma nat_of_ipv6addr_ipv6addr_of_nat:
    "n \<le> nat_of_ipv6addr max_ipv6_addr \<Longrightarrow> nat_of_ipv6addr (ipv6addr_of_nat n) = n"
    by(simp add: nat_of_ipv6addr_def ipv6addr_of_nat_def le_unat_uoi)
  lemma nat_of_ipv6addr_ipv6addr_of_nat_mod: "nat_of_ipv6addr (ipv6addr_of_nat n) = n mod 2^128"
    by(simp add: ipv6addr_of_nat_def nat_of_ipv6addr_def unat_of_nat)
  lemma ipv6addr_of_nat_nat_of_ipv6addr: "ipv6addr_of_nat (nat_of_ipv6addr addr) = addr"
    by(simp add: ipv6addr_of_nat_def nat_of_ipv6addr_def)

subsection\<open>Syntax of IPv6 Adresses\<close>
  text\<open>RFC 4291, Section 2.2.: Text Representation of Addresses\<close>

  text\<open>Quoting the RFC (note: errata exists):\<close>
  text_raw\<open>
  \begin{verbatim}
   1. The preferred form is x:x:x:x:x:x:x:x, where the 'x's are one to
      four hexadecimal digits of the eight 16-bit pieces of the address.
      Examples:
         ABCD:EF01:2345:6789:ABCD:EF01:2345:6789
         2001:DB8:0:0:8:800:200C:417A
  \end{verbatim}
\<close>
  datatype ipv6addr_syntax = 
    IPv6AddrPreferred "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word" "16 word"

  text_raw\<open>
  \begin{verbatim}
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
  \end{verbatim}
\<close>
  (*datatype may take some minutes to load*)
  datatype ipv6addr_syntax_compressed =
  --\<open>using @{typ unit} for the omission @{text "::"}. 

     Naming convention of the datatype: 
      The first number is the position where the omission occurs.
      The second number is the length of the specified address pieces.
        I.e. `8 minus the second number' pieces are omitted.\<close>
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

  (*More convenient parser helper function for compressed IPv6 addresses:
    Input list (from parser):
      Some 16word \<longrightarrow> address piece
      None \<longrightarrow> omission '::'
    
  
   Basically, the parser must only do the following (python syntax):
     split the string which is an ipv6 address at ':'
     map empty string to None
     map everything else to Some (string_to_16word str)
     sanitize empty strings at the start and the end (see toString and parser theories)
   Example:
     "1:2:3".split(":")  = ['1', '2', '3']
     ":2:3:4".split(":") = ['', '2', '3', '4']
     ":2::3".split(":")  = ['', '2', '', '3']
     "1:2:3:".split(":") = ['1', '2', '3', '']
  *)
  definition parse_ipv6_address_compressed :: "((16 word) option) list \<Rightarrow> ipv6addr_syntax_compressed option" where
    "parse_ipv6_address_compressed as = (case as of 
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
lemma parse_ipv6_address_compressed_exists:
  obtains ss where "parse_ipv6_address_compressed ss = Some ipv6_syntax"
  proof
    def ss \<equiv> "ipv6addr_syntax_compressed_to_list ipv6_syntax"
    thus "parse_ipv6_address_compressed ss = Some ipv6_syntax"
      by (cases ipv6_syntax; simp add: parse_ipv6_address_compressed_def)
  qed

lemma parse_ipv6_address_compressed_identity:
      "parse_ipv6_address_compressed (ipv6addr_syntax_compressed_to_list (ipv6_syntax)) = Some ipv6_syntax"
  by(cases ipv6_syntax; simp add: parse_ipv6_address_compressed_def)


lemma parse_ipv6_address_compressed_someE:
  assumes "parse_ipv6_address_compressed as = Some ipv6"
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
unfolding parse_ipv6_address_compressed_def
by (auto split: list.split_asm option.split_asm) (* takes a minute *)

lemma parse_ipv6_address_compressed_identity2:
      "ipv6addr_syntax_compressed_to_list ipv6_syntax = ls \<longleftrightarrow>
        (parse_ipv6_address_compressed ls) = Some ipv6_syntax"
      (is "?lhs = ?rhs")
proof
  assume ?rhs
  thus ?lhs
    by (auto elim: parse_ipv6_address_compressed_someE)
next
  assume ?lhs
  thus ?rhs
    by (cases ipv6_syntax) (auto simp: parse_ipv6_address_compressed_def)
qed

text\<open>Valid IPv6 compressed notation:
  \<^item> at most one omission
  \<^item> at most 7 pieces
\<close>
lemma RFC_4291_format: "parse_ipv6_address_compressed as \<noteq> None \<longleftrightarrow>
       length (filter (\<lambda>p. p = None) as) = 1 \<and> length (filter (\<lambda>p. p \<noteq> None) as) \<le> 7"
       (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain addr where "parse_ipv6_address_compressed as = Some addr"
    by blast
  thus ?rhs
    by (elim parse_ipv6_address_compressed_someE; simp)
next
  assume ?rhs
  thus ?lhs
    unfolding parse_ipv6_address_compressed_def
    by (auto split: option.split list.split if_split_asm)
qed

  text_raw\<open>
  \begin{verbatim}
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
  \end{verbatim}

  This is currently not supported by our library!
\<close>
  (*TODO*)
  (*TODO: oh boy, they can also be compressed*)

subsection\<open>Semantics\<close>
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


  text\<open>Correctness: round trip property one\<close>
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
       apply(rule length_drop_mask_inner)
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
      by (simp add: length_drop_mask)

    have mask_len_word:"n = (len_of TYPE('a)) \<Longrightarrow> w AND mask n = w"
      for n and w::"'a::len word" by (simp add: mask_eq_iff) 

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


  text\<open>Correctness: round trip property two\<close>
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



text\<open>compressed to preferred format\<close>
fun ipv6addr_c2p :: "ipv6addr_syntax_compressed \<Rightarrow> ipv6addr_syntax" where
    "ipv6addr_c2p (IPv6AddrCompressed1_0 ()) = IPv6AddrPreferred 0 0 0 0 0 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed1_1 () h) = IPv6AddrPreferred 0 0 0 0 0 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_2 () g h) = IPv6AddrPreferred 0 0 0 0 0 0 g h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_3 () f g h) = IPv6AddrPreferred 0 0 0 0 0 f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_4 () e f g h) = IPv6AddrPreferred 0 0 0 0 e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_5 () d e f g h) = IPv6AddrPreferred 0 0 0 d e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_6 () c d e f g h) = IPv6AddrPreferred 0 0 c d e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed1_7 () b c d e f g h) = IPv6AddrPreferred 0 b c d e f g h"

  | "ipv6addr_c2p (IPv6AddrCompressed2_1 a ()) = IPv6AddrPreferred a 0 0 0 0 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed2_2 a () h) = IPv6AddrPreferred a 0 0 0 0 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed2_3 a () g h) = IPv6AddrPreferred a 0 0 0 0 0 g h"
  | "ipv6addr_c2p (IPv6AddrCompressed2_4 a () f g h) = IPv6AddrPreferred a 0 0 0 0 f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed2_5 a () e f g h) = IPv6AddrPreferred a 0 0 0 e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed2_6 a () d e f g h) = IPv6AddrPreferred a 0 0 d e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed2_7 a () c d e f g h) = IPv6AddrPreferred a 0 c d e f g h"

  | "ipv6addr_c2p (IPv6AddrCompressed3_2 a b ()) = IPv6AddrPreferred a b 0 0 0 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed3_3 a b () h) = IPv6AddrPreferred a b 0 0 0 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed3_4 a b () g h) = IPv6AddrPreferred a b 0 0 0 0 g h"
  | "ipv6addr_c2p (IPv6AddrCompressed3_5 a b () f g h) = IPv6AddrPreferred a b 0 0 0 f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed3_6 a b () e f g h) = IPv6AddrPreferred a b 0 0 e f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed3_7 a b () d e f g h) = IPv6AddrPreferred a b 0 d e f g h"

  | "ipv6addr_c2p (IPv6AddrCompressed4_3 a b c ()) = IPv6AddrPreferred a b c 0 0 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed4_4 a b c () h) = IPv6AddrPreferred a b c 0 0 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed4_5 a b c () g h) = IPv6AddrPreferred a b c 0 0 0 g h"
  | "ipv6addr_c2p (IPv6AddrCompressed4_6 a b c () f g h) = IPv6AddrPreferred a b c 0 0 f g h"
  | "ipv6addr_c2p (IPv6AddrCompressed4_7 a b c () e f g h) = IPv6AddrPreferred a b c 0 e f g h"

  | "ipv6addr_c2p (IPv6AddrCompressed5_4 a b c d ()) = IPv6AddrPreferred a b c d 0 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed5_5 a b c d () h) = IPv6AddrPreferred a b c d 0 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed5_6 a b c d () g h) = IPv6AddrPreferred a b c d 0 0 g h"
  | "ipv6addr_c2p (IPv6AddrCompressed5_7 a b c d () f g h) = IPv6AddrPreferred a b c d 0 f g h"

  | "ipv6addr_c2p (IPv6AddrCompressed6_5 a b c d e ()) = IPv6AddrPreferred a b c d e 0 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed6_6 a b c d e () h) = IPv6AddrPreferred a b c d e 0 0 h"
  | "ipv6addr_c2p (IPv6AddrCompressed6_7 a b c d e () g h) = IPv6AddrPreferred a b c d e 0 g h"

  | "ipv6addr_c2p (IPv6AddrCompressed7_6 a b c d e f ()) = IPv6AddrPreferred a b c d e f 0 0"
  | "ipv6addr_c2p (IPv6AddrCompressed7_7 a b c d e f () h) = IPv6AddrPreferred a b c d e f 0 h"

  | "ipv6addr_c2p (IPv6AddrCompressed8_7 a b c d e f g ()) = IPv6AddrPreferred a b c d e f g 0"


definition ipv6_unparsed_compressed_to_preferred :: "((16 word) option) list \<Rightarrow> ipv6addr_syntax option" where
  "ipv6_unparsed_compressed_to_preferred ls = (
    if
      length (filter (\<lambda>p. p = None) ls) \<noteq> 1 \<or> length (filter (\<lambda>p. p \<noteq> None) ls) > 7
    then
      None
    else
      let
        before_omission = map the (takeWhile (\<lambda>x. x \<noteq> None) ls);
        after_omission = map the (drop 1 (dropWhile (\<lambda>x. x \<noteq> None) ls));
        num_omissions = 8 - (length before_omission + length after_omission);
        expanded = before_omission @ (replicate num_omissions 0) @ after_omission
      in
        case expanded of [a,b,c,d,e,f,g,h] \<Rightarrow> Some (IPv6AddrPreferred a b c d e f g h)
                         | _               \<Rightarrow> None
      )"

  lemma "ipv6_unparsed_compressed_to_preferred
    [Some 0x2001, Some 0xDB8, None, Some 0x8, Some 0x800, Some 0x200C, Some 0x417A]
      = Some (IPv6AddrPreferred 0x2001 0xDB8 0 0 8 0x800 0x200C 0x417A)" by eval

  lemma "ipv6_unparsed_compressed_to_preferred [None] = Some (IPv6AddrPreferred 0 0 0 0 0 0 0 0)" by eval

  lemma "ipv6_unparsed_compressed_to_preferred [] = None" by eval


  lemma ipv6_unparsed_compressed_to_preferred_identity1:
   "ipv6_unparsed_compressed_to_preferred (ipv6addr_syntax_compressed_to_list ipv6compressed) = Some ipv6prferred
    \<longleftrightarrow> ipv6addr_c2p ipv6compressed = ipv6prferred"
  by(cases ipv6compressed) (simp_all add: ipv6_unparsed_compressed_to_preferred_def) (*1s*)
 
  lemma ipv6_unparsed_compressed_to_preferred_identity2: 
    "ipv6_unparsed_compressed_to_preferred ls = Some ipv6prferred
     \<longleftrightarrow> (\<exists>ipv6compressed. parse_ipv6_address_compressed ls = Some ipv6compressed \<and>
                           ipv6addr_c2p ipv6compressed = ipv6prferred)"
  apply(rule iffI)
   apply(subgoal_tac "parse_ipv6_address_compressed ls \<noteq> None")
    prefer 2
    apply(subst RFC_4291_format)
    apply(simp add: ipv6_unparsed_compressed_to_preferred_def split: if_split_asm; fail)
   apply(simp)
   apply(erule exE, rename_tac ipv6compressed)
   apply(rule_tac x="ipv6compressed" in exI)
   apply(simp)
   apply(subgoal_tac "(ipv6addr_syntax_compressed_to_list ipv6compressed = ls)")
    prefer 2
    using parse_ipv6_address_compressed_identity2 apply presburger
   using ipv6_unparsed_compressed_to_preferred_identity1 apply blast
  apply(erule exE, rename_tac ipv6compressed)
  apply(subgoal_tac "(ipv6addr_syntax_compressed_to_list ipv6compressed = ls)")
   prefer 2
   using parse_ipv6_address_compressed_identity2 apply presburger
  using ipv6_unparsed_compressed_to_preferred_identity1 apply blast
  done
  

subsection\<open>IPv6 Pretty Printing (converting to compressed format)\<close>
text_raw\<open>
RFC5952:
\begin{verbatim}
4.  A Recommendation for IPv6 Text Representation

   A recommendation for a canonical text representation format of IPv6
   addresses is presented in this section.  The recommendation in this
   document is one that complies fully with [RFC4291], is implemented by
   various operating systems, and is human friendly.  The recommendation
   in this section SHOULD be followed by systems when generating an
   address to be represented as text, but all implementations MUST
   accept and be able to handle any legitimate [RFC4291] format.  It is
   advised that humans also follow these recommendations when spelling
   an address.

4.1.  Handling Leading Zeros in a 16-Bit Field

   Leading zeros MUST be suppressed.  For example, 2001:0db8::0001 is
   not acceptable and must be represented as 2001:db8::1.  A single 16-
   bit 0000 field MUST be represented as 0.

4.2.  "::" Usage

4.2.1.  Shorten as Much as Possible

   The use of the symbol "::" MUST be used to its maximum capability.
   For example, 2001:db8:0:0:0:0:2:1 must be shortened to 2001:db8::2:1.
   Likewise, 2001:db8::0:1 is not acceptable, because the symbol "::"
   could have been used to produce a shorter representation 2001:db8::1.

4.2.2.  Handling One 16-Bit 0 Field

   The symbol "::" MUST NOT be used to shorten just one 16-bit 0 field.
   For example, the representation 2001:db8:0:1:1:1:1:1 is correct, but
   2001:db8::1:1:1:1:1 is not correct.

4.2.3.  Choice in Placement of "::"

   When there is an alternative choice in the placement of a "::", the
   longest run of consecutive 16-bit 0 fields MUST be shortened (i.e.,
   the sequence with three consecutive zero fields is shortened in 2001:
   0:0:1:0:0:0:1).  When the length of the consecutive 16-bit 0 fields
   are equal (i.e., 2001:db8:0:0:1:0:0:1), the first sequence of zero
   bits MUST be shortened.  For example, 2001:db8::1:0:0:1 is correct
   representation.

4.3.  Lowercase

   The characters "a", "b", "c", "d", "e", and "f" in an IPv6 address
   MUST be represented in lowercase.
\end{verbatim}
\<close>
text\<open>See @{file "IP_Address_toString.thy"} for examples and test cases.\<close>
context
begin
  private function goup_by_zeros :: "16 word list \<Rightarrow> 16 word list list" where
    "goup_by_zeros [] = []" |
    "goup_by_zeros (x#xs) = (
        if x = 0
        then takeWhile (\<lambda>x. x = 0) (x#xs) # (goup_by_zeros (dropWhile (\<lambda>x. x = 0) xs))
        else [x]#(goup_by_zeros xs))"
  by(pat_completeness, auto)
  
  termination goup_by_zeros
	 apply(relation "measure (\<lambda>xs. length xs)")
	   apply(simp_all)
	 by (simp add: le_imp_less_Suc length_dropWhile_le)
	
	private lemma "goup_by_zeros [0,1,2,3,0,0,0,0,3,4,0,0,0,2,0,0,2,0,3,0] =
	        [[0], [1], [2], [3], [0, 0, 0, 0], [3], [4], [0, 0, 0], [2], [0, 0], [2], [0], [3], [0]]"
	by eval
	
	private lemma "concat (goup_by_zeros ls) = ls"
	  by(induction ls rule:goup_by_zeros.induct) simp+
	
	private lemma "[] \<notin> set (goup_by_zeros ls)"
	  by(induction ls rule:goup_by_zeros.induct) simp+
	  
  private primrec List_replace1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "List_replace1 _ _ [] = []" |
    "List_replace1 a b (x#xs) = (if a = x then b#xs else x#List_replace1 a b xs)"
    
	private lemma "List_replace1 a a ls = ls"
	  by(induction ls) simp_all
	
	private lemma "a \<notin> set ls \<Longrightarrow> List_replace1 a b ls = ls"
	  by(induction ls) simp_all
	
	private lemma "a \<in> set ls \<Longrightarrow> b \<in> set (List_replace1 a b ls)"
	  apply(induction ls)
	   apply(simp)
	  apply(simp)
	  by blast
  
	private fun List_explode :: "'a list list \<Rightarrow> ('a option) list" where
	  "List_explode [] = []" |
	  "List_explode ([]#xs) = None#List_explode xs" |
	  "List_explode (xs1#xs2) = map Some xs1@List_explode xs2"
	  
  private lemma "List_explode [[0::int], [2,3], [], [3,4]] = [Some 0, Some 2, Some 3, None, Some 3, Some 4]"
  by eval

  private lemma List_explode_def: 
    "List_explode xss = concat (map (\<lambda>xs. if xs = [] then [None] else map Some xs) xss)"
    by(induction xss rule: List_explode.induct) simp+
	  
  private lemma List_explode_no_empty: "[] \<notin> set xss \<Longrightarrow> List_explode xss = map Some (concat xss)"
    by(induction xss rule: List_explode.induct) simp+

  private lemma List_explode_replace1: "[] \<notin> set xss \<Longrightarrow> foo \<in> set xss \<Longrightarrow>
          List_explode (List_replace1 foo [] xss) =
            map Some (concat (takeWhile (\<lambda>xs. xs \<noteq> foo) xss)) @ [None] @
              map Some (concat (tl (dropWhile (\<lambda>xs. xs \<noteq> foo) xss)))"
    apply(induction xss rule: List_explode.induct)
      apply(simp; fail)
     apply(simp; fail)
    apply(simp)
    apply safe
      apply(simp_all add: List_explode_no_empty)
    done
    
  fun ipv6_preferred_to_compressed :: "ipv6addr_syntax \<Rightarrow> ((16 word) option) list" where
  "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (
    let lss = goup_by_zeros [a,b,c,d,e,f,g,h];
        max_zero_seq = foldr (\<lambda>xs. max (length xs)) lss 0;
        shortened = if max_zero_seq > 1 then List_replace1 (replicate max_zero_seq 0) [] lss else lss
    in
      List_explode shortened
    )"
  declare ipv6_preferred_to_compressed.simps[simp del]

  private lemma foldr_max_length: "foldr (\<lambda>xs. max (length xs)) lss n = fold max (map length lss) n"
    apply(subst List.foldr_fold)
     apply fastforce
    apply(induction lss arbitrary: n)
     apply(simp; fail)
    apply(simp)
    done

  private lemma List_explode_goup_by_zeros: "List_explode (goup_by_zeros xs) = map Some xs"
    apply(induction xs rule: goup_by_zeros.induct)
     apply(simp; fail)
    apply(simp)
    apply(safe)
     apply(simp)
    by (metis map_append takeWhile_dropWhile_id)
  
  private definition "max_zero_streak xs \<equiv> foldr (\<lambda>xs. max (length xs)) (goup_by_zeros xs) 0"    

  private lemma max_zero_streak_def2: "max_zero_streak xs = fold max (map length (goup_by_zeros xs)) 0"
    unfolding max_zero_streak_def
    by(simp add: foldr_max_length)

  private lemma ipv6_preferred_to_compressed_pull_out_if:
    "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (
    if max_zero_streak [a,b,c,d,e,f,g,h] > 1 then
      List_explode (List_replace1 (replicate (max_zero_streak [a,b,c,d,e,f,g,h]) 0) [] (goup_by_zeros [a,b,c,d,e,f,g,h]))
    else
      map Some [a,b,c,d,e,f,g,h]
    )"
  by(simp add: ipv6_preferred_to_compressed.simps max_zero_streak_def List_explode_goup_by_zeros)

    
  private lemma "ipv6_preferred_to_compressed (IPv6AddrPreferred 0 0 0 0 0 0 0 0) = [None]" by eval
  private lemma "ipv6_preferred_to_compressed (IPv6AddrPreferred 0x2001 0xDB8 0 0 8 0x800 0x200C 0x417A) =
                [Some 0x2001, Some 0xDB8, None,           Some 8, Some 0x800, Some 0x200C, Some 0x417A]" by eval
  private lemma "ipv6_preferred_to_compressed (IPv6AddrPreferred 0x2001 0xDB8 0 3 8 0x800 0x200C 0x417A) =
                [Some 0x2001, Some 0xDB8, Some 0, Some 3, Some 8, Some 0x800, Some 0x200C, Some 0x417A]" by eval

  (*the output should even conform to RFC5952, ...*)
  lemma ipv6_preferred_to_compressed_RFC_4291_format:
    "ipv6_preferred_to_compressed ip = as \<Longrightarrow> 
          length (filter (\<lambda>p. p = None) as) = 0 \<and> length as = 8
          \<or>
          length (filter (\<lambda>p. p = None) as) = 1 \<and> length (filter (\<lambda>p. p \<noteq> None) as) \<le> 7"
  apply(cases ip)
  apply(simp add: ipv6_preferred_to_compressed_pull_out_if)
  apply(simp only: split: if_split_asm)
   subgoal for a b c d e f g h
   apply(rule disjI2)
   apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
         case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
   by(auto simp add: max_zero_streak_def) (*1min*)
  subgoal
  apply(rule disjI1)
  apply(simp)
  by force
  done

  --\<open>Idea for the following proof:\<close>
  private lemma "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = None#xs \<Longrightarrow>
      xs = map Some (dropWhile (\<lambda>x. x=0) [a,b,c,d,e,f,g,h])"
    apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
          case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
    by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*20s*)


 
  lemma ipv6_preferred_to_compressed:
    assumes "ipv6_unparsed_compressed_to_preferred (ipv6_preferred_to_compressed ip) = Some ip'"
    shows "ip = ip'"
  proof -
    from assms have 1: "\<exists>ipv6compressed.
         parse_ipv6_address_compressed (ipv6_preferred_to_compressed ip) = Some ipv6compressed \<and>
         ipv6addr_c2p ipv6compressed = ip'" using ipv6_unparsed_compressed_to_preferred_identity2 by simp
  
    obtain a b c d e f g h where ip: "ip = IPv6AddrPreferred a b c d e f g h" by(cases ip)
  
    have ipv6_preferred_to_compressed_None1:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [a,b,c,d,e,f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a b c d e f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None2:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [b,c,d,e,f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b c d e f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None3:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [c,d,e,f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c d e f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a' b'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None4:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#(Some c')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [d,e,f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c' d e f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a' b' c'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None5:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#(Some c')#(Some d')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [e,f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c' d' e f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a' b' c' d'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None6:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#(Some c')#(Some d')#(Some e')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [f,g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c' d' e' f g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a' b' c' d' e'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None7:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#(Some c')#(Some d')#(Some e')#(Some f')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [g,h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c' d' e' f' g h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'"  for xs a' b' c' d' e' f'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)
    have ipv6_preferred_to_compressed_None8:
      "ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) = (Some a')#(Some b')#(Some c')#(Some d')#(Some e')#(Some f')#(Some g')#None#xs \<Longrightarrow>
        (map Some (dropWhile (\<lambda>x. x=0) [h]) = xs \<Longrightarrow> (IPv6AddrPreferred a' b' c' d' e' f' g' h) = ip') \<Longrightarrow>
        (IPv6AddrPreferred a b c d e f g h) = ip'" for xs a' b' c' d' e' f' g'
      apply(case_tac "a=0",case_tac [!] "b=0",case_tac [!] "c=0",case_tac [!] "d=0",
            case_tac [!] "e=0",case_tac [!] "f=0",case_tac [!] "g=0",case_tac [!] "h=0")
      by(simp_all add: ipv6_preferred_to_compressed_pull_out_if max_zero_streak_def) (*5s*)

    have 2: "parse_ipv6_address_compressed (ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h))
                = Some ipv6compressed \<Longrightarrow>
       ipv6addr_c2p ipv6compressed = ip' \<Longrightarrow>
       IPv6AddrPreferred a b c d e f g h = ip'"
    for ipv6compressed
      apply(erule parse_ipv6_address_compressed_someE)
                                         apply(simp_all)
                                         apply(erule ipv6_preferred_to_compressed_None1, simp split: if_split_asm)+
                                 apply(erule ipv6_preferred_to_compressed_None2, simp split: if_split_asm)+
                         apply(erule ipv6_preferred_to_compressed_None3, simp split: if_split_asm)+
                    apply(erule ipv6_preferred_to_compressed_None4, simp split: if_split_asm)+
               apply(erule ipv6_preferred_to_compressed_None5, simp split: if_split_asm)+
           apply(erule ipv6_preferred_to_compressed_None6, simp split: if_split_asm)+
        apply(erule ipv6_preferred_to_compressed_None7, simp split: if_split_asm)+
      apply(erule ipv6_preferred_to_compressed_None8, simp split: if_split_asm)
      done
    from 1 2 ip show ?thesis by(elim exE conjE, simp)
  qed
end

end
