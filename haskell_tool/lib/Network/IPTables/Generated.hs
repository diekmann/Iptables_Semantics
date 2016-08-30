{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Network.IPTables.Generated(Int, Num, Nat(..), Word, Len, Iface(..), Bit0,
                              Num1, Match_expr(..), Action(..), Rule(..),
                              Protocol(..), Tcp_flag(..), Ctstate(..),
                              Linord_helper, Set, Ipt_tcp_flags(..), Nibble,
                              Ipt_iprange(..), Ipt_l4_ports,
                              Common_primitive(..), Ipv6addr_syntax(..),
                              Prefix_match(..), Wordinterval, Negation_type(..),
                              Simple_match_ext, Simple_action(..), Simple_rule,
                              Routing_action_ext(..), Routing_rule_ext(..),
                              Parts_connection_ext, ah, esp, gre, tcp, udp,
                              icmp, sctp, mk_Set, ipassmt_diff, iPv6ICMP,
                              zero_word, map_of_ipassmt, to_ipassmt, sort_rtbl,
                              alist_and, optimize_matches, upper_closure,
                              word_to_nat, has_default_policy, word_less_eq,
                              int_to_ipv6preferred, ipv6preferred_to_int,
                              ipassmt_sanity_defined, debug_ipassmt_ipv4,
                              debug_ipassmt_ipv6, no_spoofing_iface,
                              nat_to_8word, mk_L4Ports_pre,
                              ipv4addr_of_dotdecimal, empty_rr_hlp,
                              sanity_wf_ruleset, map_of_string, nat_to_16word,
                              ipassmt_generic_ipv4, ipassmt_generic_ipv6,
                              mk_ipv6addr, fill_l4_protocol, integer_to_16word,
                              rewrite_Goto_safe, simple_fw_valid,
                              compress_parsed_extra, prefix_match_32_toString,
                              routing_rule_32_toString, mk_parts_connection_TCP,
                              to_simple_firewall, prefix_match_128_toString,
                              routing_rule_128_toString,
                              unfold_ruleset_CHAIN_safe, metric_update,
                              access_matrix_pretty_ipv4,
                              access_matrix_pretty_ipv6, action_toString,
                              packet_assume_new, routing_action_oiface_update,
                              simple_rule_ipv4_toString,
                              simple_rule_ipv6_toString,
                              routing_action_next_hop_update,
                              abstract_for_simple_firewall,
                              ipt_ipv4range_toString, ipt_ipv6range_toString,
                              common_primitive_ipv4_toString,
                              common_primitive_ipv6_toString,
                              to_simple_firewall_without_interfaces,
                              common_primitive_match_expr_ipv4_toString,
                              common_primitive_match_expr_ipv6_toString)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Data_Bits;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

data Num = One | Bit0 Num | Bit1 Num;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

class Times a where {
  times :: a -> a -> a;
};

class (One a, Times a) => Power a where {
};

instance Times Int where {
  times = times_int;
};

instance Power Int where {
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Int where {
};

instance Order Int where {
};

class (Order a) => Linorder a where {
};

instance Linorder Int where {
};

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = zero_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Preorder Nat where {
};

instance Order Nat where {
};

instance Linorder Nat where {
};

data Itself a = Type;

class Len0 a where {
  len_of :: Itself a -> Nat;
};

newtype Word a = Word Int;

uint :: forall a. (Len0 a) => Word a -> Int;
uint (Word x) = x;

equal_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
equal_word k l = equal_int (uint k) (uint l);

instance (Len0 a) => Eq (Word a) where {
  a == b = equal_word a b;
};

sgn_integer :: Integer -> Integer;
sgn_integer k =
  (if k == (0 :: Integer) then (0 :: Integer)
    else (if k < (0 :: Integer) then (-1 :: Integer) else (1 :: Integer)));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if l == (0 :: Integer) then ((0 :: Integer), k)
           else ((apsnd . (\ a b -> a * b)) . sgn_integer) l
                  (if sgn_integer k == sgn_integer l then divMod (abs k) (abs l)
                    else let {
                           (r, s) = divMod (abs k) (abs l);
                         } in (if s == (0 :: Integer)
                                then (negate r, (0 :: Integer))
                                else (negate r - (1 :: Integer),
                                       Prelude.abs l - s)))));

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_int :: Int -> Int -> Int;
mod_int k l =
  Int_of_integer (mod_integer (integer_of_int k) (integer_of_int l));

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

word_of_int :: forall a. (Len0 a) => Int -> Word a;
word_of_int k =
  Word (mod_int k
         (power (Int_of_integer (2 :: Integer))
           ((len_of :: Itself a -> Nat) Type)));

one_word :: forall a. (Len0 a) => Word a;
one_word = word_of_int (Int_of_integer (1 :: Integer));

instance (Len0 a) => One (Word a) where {
  one = one_word;
};

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

plus_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
plus_word a b = word_of_int (plus_int (uint a) (uint b));

class Plus a where {
  plus :: a -> a -> a;
};

instance (Len0 a) => Plus (Word a) where {
  plus = plus_word;
};

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

zero_worda :: forall a. (Len0 a) => Word a;
zero_worda = word_of_int zero_int;

instance (Len0 a) => Zero (Word a) where {
  zero = zero_worda;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance (Len0 a) => Semigroup_add (Word a) where {
};

instance (Len0 a) => Numeral (Word a) where {
};

times_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
times_word a b = word_of_int (times_int (uint a) (uint b));

instance (Len0 a) => Times (Word a) where {
  times = times_word;
};

instance (Len0 a) => Power (Word a) where {
};

less_eq_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
less_eq_word a b = less_eq_int (uint a) (uint b);

less_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
less_word a b = less_int (uint a) (uint b);

instance (Len0 a) => Ord (Word a) where {
  less_eq = less_eq_word;
  less = less_word;
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

instance (Len0 a) => Ab_semigroup_add (Word a) where {
};

instance (Len0 a) => Semigroup_mult (Word a) where {
};

instance (Len0 a) => Semiring (Word a) where {
};

instance (Len0 a) => Preorder (Word a) where {
};

instance (Len0 a) => Order (Word a) where {
};

class (Times a, Zero a) => Mult_zero a where {
};

instance (Len0 a) => Mult_zero (Word a) where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

instance (Len0 a) => Monoid_add (Word a) where {
};

instance (Len0 a) => Comm_monoid_add (Word a) where {
};

instance (Len0 a) => Semiring_0 (Word a) where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Len0 a) => Len a where {
};

instance (Len0 a) => Monoid_mult (Word a) where {
};

instance (Len a) => Semiring_numeral (Word a) where {
};

instance (Len a) => Zero_neq_one (Word a) where {
};

instance (Len a) => Semiring_1 (Word a) where {
};

instance (Len0 a) => Linorder (Word a) where {
};

newtype Iface = Iface [Prelude.Char];

equal_iface :: Iface -> Iface -> Bool;
equal_iface (Iface x) (Iface ya) = x == ya;

instance Eq Iface where {
  a == b = equal_iface a b;
};

less_eq_iface :: Iface -> Iface -> Bool;
less_eq_iface (Iface []) (Iface uu) = True;
less_eq_iface (Iface (v : va)) (Iface []) = False;
less_eq_iface (Iface (a : asa)) (Iface (b : bs)) =
  (if a == b then less_eq_iface (Iface asa) (Iface bs) else a <= b);

less_iface :: Iface -> Iface -> Bool;
less_iface (Iface []) (Iface []) = False;
less_iface (Iface []) (Iface (v : va)) = True;
less_iface (Iface (v : va)) (Iface []) = False;
less_iface (Iface (a : asa)) (Iface (b : bs)) =
  (if a == b then less_iface (Iface asa) (Iface bs) else a < b);

instance Ord Iface where {
  less_eq = less_eq_iface;
  less = less_iface;
};

instance Preorder Iface where {
};

instance Order Iface where {
};

instance Linorder Iface where {
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

class Finite a where {
};

newtype Bit0 a = Abs_bit0 Int;

len_of_bit0 :: forall a. (Len0 a) => Itself (Bit0 a) -> Nat;
len_of_bit0 x =
  times_nat (nat_of_integer (2 :: Integer)) ((len_of :: Itself a -> Nat) Type);

instance (Len0 a) => Len0 (Bit0 a) where {
  len_of = len_of_bit0;
};

instance (Len a) => Len (Bit0 a) where {
};

data Num1 = One_num1;

len_of_num1 :: Itself Num1 -> Nat;
len_of_num1 x = one_nat;

instance Len0 Num1 where {
  len_of = len_of_num1;
};

instance Len Num1 where {
};

less_eq_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less_eq y1 y2;

less_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less y1 y2;

instance (Ord a, Ord b) => Ord (a, b) where {
  less_eq = less_eq_prod;
  less = less_prod;
};

instance (Preorder a, Preorder b) => Preorder (a, b) where {
};

instance (Order a, Order b) => Order (a, b) where {
};

instance (Linorder a, Linorder b) => Linorder (a, b) where {
};

data Match_expr a = Match a | MatchNot (Match_expr a)
  | MatchAnd (Match_expr a) (Match_expr a) | MatchAny;

equal_match_expr :: forall a. (Eq a) => Match_expr a -> Match_expr a -> Bool;
equal_match_expr (MatchAnd x31 x32) MatchAny = False;
equal_match_expr MatchAny (MatchAnd x31 x32) = False;
equal_match_expr (MatchNot x2) MatchAny = False;
equal_match_expr MatchAny (MatchNot x2) = False;
equal_match_expr (MatchNot x2) (MatchAnd x31 x32) = False;
equal_match_expr (MatchAnd x31 x32) (MatchNot x2) = False;
equal_match_expr (Match x1) MatchAny = False;
equal_match_expr MatchAny (Match x1) = False;
equal_match_expr (Match x1) (MatchAnd x31 x32) = False;
equal_match_expr (MatchAnd x31 x32) (Match x1) = False;
equal_match_expr (Match x1) (MatchNot x2) = False;
equal_match_expr (MatchNot x2) (Match x1) = False;
equal_match_expr (MatchAnd x31 x32) (MatchAnd y31 y32) =
  equal_match_expr x31 y31 && equal_match_expr x32 y32;
equal_match_expr (MatchNot x2) (MatchNot y2) = equal_match_expr x2 y2;
equal_match_expr (Match x1) (Match y1) = x1 == y1;
equal_match_expr MatchAny MatchAny = True;

data Action = Accept | Drop | Log | Reject | Call [Prelude.Char] | Return
  | Goto [Prelude.Char] | Empty | Unknown;

equal_action :: Action -> Action -> Bool;
equal_action Empty Unknown = False;
equal_action Unknown Empty = False;
equal_action (Goto x7) Unknown = False;
equal_action Unknown (Goto x7) = False;
equal_action (Goto x7) Empty = False;
equal_action Empty (Goto x7) = False;
equal_action Return Unknown = False;
equal_action Unknown Return = False;
equal_action Return Empty = False;
equal_action Empty Return = False;
equal_action Return (Goto x7) = False;
equal_action (Goto x7) Return = False;
equal_action (Call x5) Unknown = False;
equal_action Unknown (Call x5) = False;
equal_action (Call x5) Empty = False;
equal_action Empty (Call x5) = False;
equal_action (Call x5) (Goto x7) = False;
equal_action (Goto x7) (Call x5) = False;
equal_action (Call x5) Return = False;
equal_action Return (Call x5) = False;
equal_action Reject Unknown = False;
equal_action Unknown Reject = False;
equal_action Reject Empty = False;
equal_action Empty Reject = False;
equal_action Reject (Goto x7) = False;
equal_action (Goto x7) Reject = False;
equal_action Reject Return = False;
equal_action Return Reject = False;
equal_action Reject (Call x5) = False;
equal_action (Call x5) Reject = False;
equal_action Log Unknown = False;
equal_action Unknown Log = False;
equal_action Log Empty = False;
equal_action Empty Log = False;
equal_action Log (Goto x7) = False;
equal_action (Goto x7) Log = False;
equal_action Log Return = False;
equal_action Return Log = False;
equal_action Log (Call x5) = False;
equal_action (Call x5) Log = False;
equal_action Log Reject = False;
equal_action Reject Log = False;
equal_action Drop Unknown = False;
equal_action Unknown Drop = False;
equal_action Drop Empty = False;
equal_action Empty Drop = False;
equal_action Drop (Goto x7) = False;
equal_action (Goto x7) Drop = False;
equal_action Drop Return = False;
equal_action Return Drop = False;
equal_action Drop (Call x5) = False;
equal_action (Call x5) Drop = False;
equal_action Drop Reject = False;
equal_action Reject Drop = False;
equal_action Drop Log = False;
equal_action Log Drop = False;
equal_action Accept Unknown = False;
equal_action Unknown Accept = False;
equal_action Accept Empty = False;
equal_action Empty Accept = False;
equal_action Accept (Goto x7) = False;
equal_action (Goto x7) Accept = False;
equal_action Accept Return = False;
equal_action Return Accept = False;
equal_action Accept (Call x5) = False;
equal_action (Call x5) Accept = False;
equal_action Accept Reject = False;
equal_action Reject Accept = False;
equal_action Accept Log = False;
equal_action Log Accept = False;
equal_action Accept Drop = False;
equal_action Drop Accept = False;
equal_action (Goto x7) (Goto y7) = x7 == y7;
equal_action (Call x5) (Call y5) = x5 == y5;
equal_action Unknown Unknown = True;
equal_action Empty Empty = True;
equal_action Return Return = True;
equal_action Reject Reject = True;
equal_action Log Log = True;
equal_action Drop Drop = True;
equal_action Accept Accept = True;

data Rule a = Rule (Match_expr a) Action;

equal_rule :: forall a. (Eq a) => Rule a -> Rule a -> Bool;
equal_rule (Rule x1 x2) (Rule y1 y2) =
  equal_match_expr x1 y1 && equal_action x2 y2;

instance (Eq a) => Eq (Rule a) where {
  a == b = equal_rule a b;
};

data Protocol = ProtoAny | Proto (Word (Bit0 (Bit0 (Bit0 Num1))));

equal_protocol :: Protocol -> Protocol -> Bool;
equal_protocol ProtoAny (Proto x2) = False;
equal_protocol (Proto x2) ProtoAny = False;
equal_protocol (Proto x2) (Proto y2) = equal_word x2 y2;
equal_protocol ProtoAny ProtoAny = True;

instance Eq Protocol where {
  a == b = equal_protocol a b;
};

data Tcp_flag = TCP_SYN | TCP_ACK | TCP_FIN | TCP_RST | TCP_URG | TCP_PSH;

enum_all_tcp_flag :: (Tcp_flag -> Bool) -> Bool;
enum_all_tcp_flag p =
  p TCP_SYN && p TCP_ACK && p TCP_FIN && p TCP_RST && p TCP_URG && p TCP_PSH;

enum_ex_tcp_flag :: (Tcp_flag -> Bool) -> Bool;
enum_ex_tcp_flag p =
  p TCP_SYN ||
    (p TCP_ACK || (p TCP_FIN || (p TCP_RST || (p TCP_URG || p TCP_PSH))));

enum_tcp_flag :: [Tcp_flag];
enum_tcp_flag = [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST, TCP_URG, TCP_PSH];

class (Finite a) => Enum a where {
  enum :: [a];
  enum_all :: (a -> Bool) -> Bool;
  enum_ex :: (a -> Bool) -> Bool;
};

instance Finite Tcp_flag where {
};

instance Enum Tcp_flag where {
  enum = enum_tcp_flag;
  enum_all = enum_all_tcp_flag;
  enum_ex = enum_ex_tcp_flag;
};

equal_tcp_flag :: Tcp_flag -> Tcp_flag -> Bool;
equal_tcp_flag TCP_URG TCP_PSH = False;
equal_tcp_flag TCP_PSH TCP_URG = False;
equal_tcp_flag TCP_RST TCP_PSH = False;
equal_tcp_flag TCP_PSH TCP_RST = False;
equal_tcp_flag TCP_RST TCP_URG = False;
equal_tcp_flag TCP_URG TCP_RST = False;
equal_tcp_flag TCP_FIN TCP_PSH = False;
equal_tcp_flag TCP_PSH TCP_FIN = False;
equal_tcp_flag TCP_FIN TCP_URG = False;
equal_tcp_flag TCP_URG TCP_FIN = False;
equal_tcp_flag TCP_FIN TCP_RST = False;
equal_tcp_flag TCP_RST TCP_FIN = False;
equal_tcp_flag TCP_ACK TCP_PSH = False;
equal_tcp_flag TCP_PSH TCP_ACK = False;
equal_tcp_flag TCP_ACK TCP_URG = False;
equal_tcp_flag TCP_URG TCP_ACK = False;
equal_tcp_flag TCP_ACK TCP_RST = False;
equal_tcp_flag TCP_RST TCP_ACK = False;
equal_tcp_flag TCP_ACK TCP_FIN = False;
equal_tcp_flag TCP_FIN TCP_ACK = False;
equal_tcp_flag TCP_SYN TCP_PSH = False;
equal_tcp_flag TCP_PSH TCP_SYN = False;
equal_tcp_flag TCP_SYN TCP_URG = False;
equal_tcp_flag TCP_URG TCP_SYN = False;
equal_tcp_flag TCP_SYN TCP_RST = False;
equal_tcp_flag TCP_RST TCP_SYN = False;
equal_tcp_flag TCP_SYN TCP_FIN = False;
equal_tcp_flag TCP_FIN TCP_SYN = False;
equal_tcp_flag TCP_SYN TCP_ACK = False;
equal_tcp_flag TCP_ACK TCP_SYN = False;
equal_tcp_flag TCP_PSH TCP_PSH = True;
equal_tcp_flag TCP_URG TCP_URG = True;
equal_tcp_flag TCP_RST TCP_RST = True;
equal_tcp_flag TCP_FIN TCP_FIN = True;
equal_tcp_flag TCP_ACK TCP_ACK = True;
equal_tcp_flag TCP_SYN TCP_SYN = True;

instance Eq Tcp_flag where {
  a == b = equal_tcp_flag a b;
};

data Ctstate = CT_New | CT_Established | CT_Related | CT_Untracked | CT_Invalid;

enum_all_ctstate :: (Ctstate -> Bool) -> Bool;
enum_all_ctstate p =
  p CT_New &&
    p CT_Established && p CT_Related && p CT_Untracked && p CT_Invalid;

enum_ex_ctstate :: (Ctstate -> Bool) -> Bool;
enum_ex_ctstate p =
  p CT_New ||
    (p CT_Established || (p CT_Related || (p CT_Untracked || p CT_Invalid)));

enum_ctstate :: [Ctstate];
enum_ctstate = [CT_New, CT_Established, CT_Related, CT_Untracked, CT_Invalid];

instance Finite Ctstate where {
};

instance Enum Ctstate where {
  enum = enum_ctstate;
  enum_all = enum_all_ctstate;
  enum_ex = enum_ex_ctstate;
};

equal_ctstate :: Ctstate -> Ctstate -> Bool;
equal_ctstate CT_Untracked CT_Invalid = False;
equal_ctstate CT_Invalid CT_Untracked = False;
equal_ctstate CT_Related CT_Invalid = False;
equal_ctstate CT_Invalid CT_Related = False;
equal_ctstate CT_Related CT_Untracked = False;
equal_ctstate CT_Untracked CT_Related = False;
equal_ctstate CT_Established CT_Invalid = False;
equal_ctstate CT_Invalid CT_Established = False;
equal_ctstate CT_Established CT_Untracked = False;
equal_ctstate CT_Untracked CT_Established = False;
equal_ctstate CT_Established CT_Related = False;
equal_ctstate CT_Related CT_Established = False;
equal_ctstate CT_New CT_Invalid = False;
equal_ctstate CT_Invalid CT_New = False;
equal_ctstate CT_New CT_Untracked = False;
equal_ctstate CT_Untracked CT_New = False;
equal_ctstate CT_New CT_Related = False;
equal_ctstate CT_Related CT_New = False;
equal_ctstate CT_New CT_Established = False;
equal_ctstate CT_Established CT_New = False;
equal_ctstate CT_Invalid CT_Invalid = True;
equal_ctstate CT_Untracked CT_Untracked = True;
equal_ctstate CT_Related CT_Related = True;
equal_ctstate CT_Established CT_Established = True;
equal_ctstate CT_New CT_New = True;

instance Eq Ctstate where {
  a == b = equal_ctstate a b;
};

instance (Eq a) => Eq (Match_expr a) where {
  a == b = equal_match_expr a b;
};

data Linord_helper a b = LinordHelper a b;

linord_helper_less_eq1 ::
  forall a b.
    (Eq a, Ord a, Ord b) => Linord_helper a b -> Linord_helper a b -> Bool;
linord_helper_less_eq1 a b = let {
                               (LinordHelper a1 a2) = a;
                               (LinordHelper b1 b2) = b;
                             } in less a1 b1 || a1 == b1 && less_eq a2 b2;

less_eq_linord_helper ::
  forall a b.
    (Eq a, Linorder a,
      Linorder b) => Linord_helper a b -> Linord_helper a b -> Bool;
less_eq_linord_helper a b = linord_helper_less_eq1 a b;

equal_linord_helper ::
  forall a b. (Eq a, Eq b) => Linord_helper a b -> Linord_helper a b -> Bool;
equal_linord_helper (LinordHelper x1 x2) (LinordHelper y1 y2) =
  x1 == y1 && x2 == y2;

less_linord_helper ::
  forall a b.
    (Eq a, Linorder a, Eq b,
      Linorder b) => Linord_helper a b -> Linord_helper a b -> Bool;
less_linord_helper a b =
  not (equal_linord_helper a b) && linord_helper_less_eq1 a b;

instance (Eq a, Linorder a, Eq b, Linorder b) => Ord (Linord_helper a b) where {
  less_eq = less_eq_linord_helper;
  less = less_linord_helper;
};

instance (Eq a, Linorder a, Eq b,
           Linorder b) => Preorder (Linord_helper a b) where {
};

instance (Eq a, Linorder a, Eq b,
           Linorder b) => Order (Linord_helper a b) where {
};

instance (Eq a, Linorder a, Eq b,
           Linorder b) => Linorder (Linord_helper a b) where {
};

data Final_decision = FinalAllow | FinalDeny;

equal_final_decision :: Final_decision -> Final_decision -> Bool;
equal_final_decision FinalAllow FinalDeny = False;
equal_final_decision FinalDeny FinalAllow = False;
equal_final_decision FinalDeny FinalDeny = True;
equal_final_decision FinalAllow FinalAllow = True;

data State = Undecided | Decision Final_decision;

equal_state :: State -> State -> Bool;
equal_state Undecided (Decision x2) = False;
equal_state (Decision x2) Undecided = False;
equal_state (Decision x2) (Decision y2) = equal_final_decision x2 y2;
equal_state Undecided Undecided = True;

instance Eq State where {
  a == b = equal_state a b;
};

data Set a = Set [a] | Coset [a];

data Ipt_tcp_flags = TCP_Flags (Set Tcp_flag) (Set Tcp_flag);

data Nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5
  | Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC
  | NibbleD | NibbleE | NibbleF;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset xs) (Set ys) =
  (if null xs && null ys then False
    else (error :: forall a. String -> (() -> a) -> a)
           "subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV"
           (\ _ -> less_eq_set (Coset xs) (Set ys)));
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

equal_ipt_tcp_flags :: Ipt_tcp_flags -> Ipt_tcp_flags -> Bool;
equal_ipt_tcp_flags (TCP_Flags x1 x2) (TCP_Flags y1 y2) =
  equal_set x1 y1 && equal_set x2 y2;

data Ipt_iprange a = IpAddr (Word a) | IpAddrNetmask (Word a) Nat
  | IpAddrRange (Word a) (Word a);

equal_ipt_iprange ::
  forall a. (Len a) => Ipt_iprange a -> Ipt_iprange a -> Bool;
equal_ipt_iprange (IpAddrNetmask x21 x22) (IpAddrRange x31 x32) = False;
equal_ipt_iprange (IpAddrRange x31 x32) (IpAddrNetmask x21 x22) = False;
equal_ipt_iprange (IpAddr x1) (IpAddrRange x31 x32) = False;
equal_ipt_iprange (IpAddrRange x31 x32) (IpAddr x1) = False;
equal_ipt_iprange (IpAddr x1) (IpAddrNetmask x21 x22) = False;
equal_ipt_iprange (IpAddrNetmask x21 x22) (IpAddr x1) = False;
equal_ipt_iprange (IpAddrRange x31 x32) (IpAddrRange y31 y32) =
  equal_word x31 y31 && equal_word x32 y32;
equal_ipt_iprange (IpAddrNetmask x21 x22) (IpAddrNetmask y21 y22) =
  equal_word x21 y21 && equal_nat x22 y22;
equal_ipt_iprange (IpAddr x1) (IpAddr y1) = equal_word x1 y1;

data Ipt_l4_ports =
  L4Ports (Word (Bit0 (Bit0 (Bit0 Num1))))
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];

data Common_primitive a = Src (Ipt_iprange a) | Dst (Ipt_iprange a)
  | IIface Iface | OIface Iface | Prot Protocol | Src_Ports Ipt_l4_ports
  | Dst_Ports Ipt_l4_ports | L4_Flags Ipt_tcp_flags | CT_State (Set Ctstate)
  | Extra [Prelude.Char];

equal_ipt_l4_ports :: Ipt_l4_ports -> Ipt_l4_ports -> Bool;
equal_ipt_l4_ports (L4Ports x1 x2) (L4Ports y1 y2) =
  equal_word x1 y1 && x2 == y2;

equal_common_primitive ::
  forall a. (Len a) => Common_primitive a -> Common_primitive a -> Bool;
equal_common_primitive (CT_State x9) (Extra x10) = False;
equal_common_primitive (Extra x10) (CT_State x9) = False;
equal_common_primitive (L4_Flags x8) (Extra x10) = False;
equal_common_primitive (Extra x10) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (L4_Flags x8) = False;
equal_common_primitive (Dst_Ports x7) (Extra x10) = False;
equal_common_primitive (Extra x10) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (Dst_Ports x7) = False;
equal_common_primitive (Src_Ports x6) (Extra x10) = False;
equal_common_primitive (Extra x10) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (Src_Ports x6) = False;
equal_common_primitive (Prot x5) (Extra x10) = False;
equal_common_primitive (Extra x10) (Prot x5) = False;
equal_common_primitive (Prot x5) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (Prot x5) = False;
equal_common_primitive (Prot x5) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (Prot x5) = False;
equal_common_primitive (Prot x5) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (Prot x5) = False;
equal_common_primitive (Prot x5) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (Prot x5) = False;
equal_common_primitive (OIface x4) (Extra x10) = False;
equal_common_primitive (Extra x10) (OIface x4) = False;
equal_common_primitive (OIface x4) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (OIface x4) = False;
equal_common_primitive (OIface x4) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (OIface x4) = False;
equal_common_primitive (OIface x4) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (OIface x4) = False;
equal_common_primitive (OIface x4) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (OIface x4) = False;
equal_common_primitive (OIface x4) (Prot x5) = False;
equal_common_primitive (Prot x5) (OIface x4) = False;
equal_common_primitive (IIface x3) (Extra x10) = False;
equal_common_primitive (Extra x10) (IIface x3) = False;
equal_common_primitive (IIface x3) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (IIface x3) = False;
equal_common_primitive (IIface x3) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (IIface x3) = False;
equal_common_primitive (IIface x3) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (IIface x3) = False;
equal_common_primitive (IIface x3) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (IIface x3) = False;
equal_common_primitive (IIface x3) (Prot x5) = False;
equal_common_primitive (Prot x5) (IIface x3) = False;
equal_common_primitive (IIface x3) (OIface x4) = False;
equal_common_primitive (OIface x4) (IIface x3) = False;
equal_common_primitive (Dst x2) (Extra x10) = False;
equal_common_primitive (Extra x10) (Dst x2) = False;
equal_common_primitive (Dst x2) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (Dst x2) = False;
equal_common_primitive (Dst x2) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (Dst x2) = False;
equal_common_primitive (Dst x2) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (Dst x2) = False;
equal_common_primitive (Dst x2) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (Dst x2) = False;
equal_common_primitive (Dst x2) (Prot x5) = False;
equal_common_primitive (Prot x5) (Dst x2) = False;
equal_common_primitive (Dst x2) (OIface x4) = False;
equal_common_primitive (OIface x4) (Dst x2) = False;
equal_common_primitive (Dst x2) (IIface x3) = False;
equal_common_primitive (IIface x3) (Dst x2) = False;
equal_common_primitive (Src x1) (Extra x10) = False;
equal_common_primitive (Extra x10) (Src x1) = False;
equal_common_primitive (Src x1) (CT_State x9) = False;
equal_common_primitive (CT_State x9) (Src x1) = False;
equal_common_primitive (Src x1) (L4_Flags x8) = False;
equal_common_primitive (L4_Flags x8) (Src x1) = False;
equal_common_primitive (Src x1) (Dst_Ports x7) = False;
equal_common_primitive (Dst_Ports x7) (Src x1) = False;
equal_common_primitive (Src x1) (Src_Ports x6) = False;
equal_common_primitive (Src_Ports x6) (Src x1) = False;
equal_common_primitive (Src x1) (Prot x5) = False;
equal_common_primitive (Prot x5) (Src x1) = False;
equal_common_primitive (Src x1) (OIface x4) = False;
equal_common_primitive (OIface x4) (Src x1) = False;
equal_common_primitive (Src x1) (IIface x3) = False;
equal_common_primitive (IIface x3) (Src x1) = False;
equal_common_primitive (Src x1) (Dst x2) = False;
equal_common_primitive (Dst x2) (Src x1) = False;
equal_common_primitive (Extra x10) (Extra y10) = x10 == y10;
equal_common_primitive (CT_State x9) (CT_State y9) = equal_set x9 y9;
equal_common_primitive (L4_Flags x8) (L4_Flags y8) = equal_ipt_tcp_flags x8 y8;
equal_common_primitive (Dst_Ports x7) (Dst_Ports y7) = equal_ipt_l4_ports x7 y7;
equal_common_primitive (Src_Ports x6) (Src_Ports y6) = equal_ipt_l4_ports x6 y6;
equal_common_primitive (Prot x5) (Prot y5) = equal_protocol x5 y5;
equal_common_primitive (OIface x4) (OIface y4) = equal_iface x4 y4;
equal_common_primitive (IIface x3) (IIface y3) = equal_iface x3 y3;
equal_common_primitive (Dst x2) (Dst y2) = equal_ipt_iprange x2 y2;
equal_common_primitive (Src x1) (Src y1) = equal_ipt_iprange x1 y1;

instance (Len a) => Eq (Common_primitive a) where {
  a == b = equal_common_primitive a b;
};

data Ipv6addr_syntax =
  IPv6AddrPreferred (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));

data Prefix_match a = PrefixMatch (Word a) Nat;

data Wordinterval a = WordInterval (Word a) (Word a)
  | RangeUnion (Wordinterval a) (Wordinterval a);

data Negation_type a = Pos a | Neg a;

data Simple_match_ext a b =
  Simple_match_ext Iface Iface (Word a, Nat) (Word a, Nat) Protocol
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    b;

data Simple_action = Accepta | Dropa;

data Simple_rule a = SimpleRule (Simple_match_ext a ()) Simple_action;

data Match_compress a = CannotMatch | MatchesAll | MatchExpr a;

data Routing_action_ext a b =
  Routing_action_ext [Prelude.Char] (Maybe (Word a)) b;

data Routing_rule_ext a b =
  Routing_rule_ext (Prefix_match a) Nat (Routing_action_ext a ()) b;

data Simple_packet_ext a b =
  Simple_packet_ext [Prelude.Char] [Prelude.Char] (Word a) (Word a)
    (Word (Bit0 (Bit0 (Bit0 Num1)))) (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) (Set Tcp_flag) [Prelude.Char] b;

data Parts_connection_ext a =
  Parts_connection_ext [Prelude.Char] [Prelude.Char]
    (Word (Bit0 (Bit0 (Bit0 Num1)))) (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) a;

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

upto_aux :: Int -> Int -> [Int] -> [Int];
upto_aux i j js =
  (if less_int j i then js
    else upto_aux i (minus_int j (Int_of_integer (1 :: Integer))) (j : js));

upto :: Int -> Int -> [Int];
upto i j = upto_aux i j [];

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

minus_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
minus_word a b = word_of_int (minus_int (uint a) (uint b));

shiftl_integer :: Integer -> Nat -> Integer;
shiftl_integer x n =
  (Data_Bits.shiftlUnbounded :: Integer -> Integer -> Integer) x
    (integer_of_nat n);

bit_integer :: Integer -> Bool -> Integer;
bit_integer i True = shiftl_integer i one_nat + (1 :: Integer);
bit_integer i False = shiftl_integer i one_nat;

bit :: Int -> Bool -> Int;
bit (Int_of_integer i) b = Int_of_integer (bit_integer i b);

shiftl1 :: forall a. (Len0 a) => Word a -> Word a;
shiftl1 w = word_of_int (bit (uint w) False);

funpow :: forall a. Nat -> (a -> a) -> a -> a;
funpow n f =
  (if equal_nat n zero_nat then id else f . funpow (minus_nat n one_nat) f);

shiftl_word :: forall a. (Len0 a) => Word a -> Nat -> Word a;
shiftl_word w n = funpow n shiftl1 w;

mask :: forall a. (Len a) => Nat -> Word a;
mask n = minus_word (shiftl_word one_word n) one_word;

unat :: forall a. (Len0 a) => Word a -> Nat;
unat w = nat (uint w);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);
map_of [] k = Nothing;

merge :: forall a. (Eq a, Linorder a) => [a] -> [a] -> [a];
merge [] l2 = l2;
merge (v : va) [] = v : va;
merge (x1 : l1) (x2 : l2) =
  (if less x1 x2 then x1 : merge l1 (x2 : l2)
    else (if x1 == x2 then x1 : merge l1 l2 else x2 : merge (x1 : l1) l2));

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

ucast :: forall a b. (Len0 a, Len0 b) => Word a -> Word b;
ucast w = word_of_int (uint w);

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice [] ys = ys;
splice xs [] = xs;

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

product :: forall a b. [a] -> [b] -> [(a, b)];
product [] uu = [];
product (x : xs) ys = map (\ a -> (x, a)) ys ++ product xs ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

bin_rest :: Int -> Int;
bin_rest (Int_of_integer i) =
  Int_of_integer ((Data_Bits.shiftrUnbounded i 1 :: Integer));

shiftr1 :: forall a. (Len0 a) => Word a -> Word a;
shiftr1 w = word_of_int (bin_rest (uint w));

select_p_tuple :: forall a. (a -> Bool) -> a -> ([a], [a]) -> ([a], [a]);
select_p_tuple p x (ts, fs) = (if p x then (x : ts, fs) else (ts, x : fs));

partition_tailrec :: forall a. (a -> Bool) -> [a] -> ([a], [a]);
partition_tailrec p xs = foldr (select_p_tuple p) xs ([], []);

groupF_code :: forall a b. (Eq b) => (a -> b) -> [a] -> [[a]];
groupF_code f [] = [];
groupF_code f (x : xs) = let {
                           (ts, fs) = partition_tailrec (\ y -> f x == f y) xs;
                         } in (x : ts) : groupF_code f fs;

groupF :: forall a b. (Eq b) => (a -> b) -> [a] -> [[a]];
groupF f asa = groupF_code f asa;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (membera xs x) && distinct xs;

max_word :: forall a. (Len a) => Word a;
max_word =
  word_of_int
    (minus_int
      (power (Int_of_integer (2 :: Integer)) ((len_of :: Itself a -> Nat) Type))
      (Int_of_integer (1 :: Integer)));

ifaceAny :: Iface;
ifaceAny = Iface "+";

ah :: Word (Bit0 (Bit0 (Bit0 Num1)));
ah = word_of_int (Int_of_integer (51 :: Integer));

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

esp :: Word (Bit0 (Bit0 (Bit0 Num1)));
esp = word_of_int (Int_of_integer (50 :: Integer));

gre :: Word (Bit0 (Bit0 (Bit0 Num1)));
gre = word_of_int (Int_of_integer (47 :: Integer));

tcp :: Word (Bit0 (Bit0 (Bit0 Num1)));
tcp = word_of_int (Int_of_integer (6 :: Integer));

udp :: Word (Bit0 (Bit0 (Bit0 Num1)));
udp = word_of_int (Int_of_integer (17 :: Integer));

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

merge_list :: forall a. (Eq a, Linorder a) => [[a]] -> [[a]] -> [a];
merge_list [] [] = [];
merge_list [] [l] = l;
merge_list (la : acc2) [] = merge_list [] (la : acc2);
merge_list (la : acc2) [l] = merge_list [] (l : la : acc2);
merge_list acc2 (l1 : l2 : ls) = merge_list (merge l1 l2 : acc2) ls;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

pfxes :: forall a. (Len0 a) => Itself a -> [Nat];
pfxes uu =
  map nat (upto zero_int (int_of_nat ((len_of :: Itself a -> Nat) Type)));

icmp :: Word (Bit0 (Bit0 (Bit0 Num1)));
icmp = one_word;

igmp :: Word (Bit0 (Bit0 (Bit0 Num1)));
igmp = word_of_int (Int_of_integer (2 :: Integer));

sctp :: Word (Bit0 (Bit0 (Bit0 Num1)));
sctp = word_of_int (Int_of_integer (132 :: Integer));

uncurry :: forall a b c. (a -> b -> c) -> (a, b) -> c;
uncurry f a = let {
                (aa, b) = a;
              } in f aa b;

list_explode :: forall a. [[a]] -> [Maybe a];
list_explode [] = [];
list_explode ([] : xs) = Nothing : list_explode xs;
list_explode ((v : va) : xs2) = map Just (v : va) ++ list_explode xs2;

internal_iface_name_match :: [Prelude.Char] -> [Prelude.Char] -> Bool;
internal_iface_name_match [] [] = True;
internal_iface_name_match (i : is) [] = i == '+' && null is;
internal_iface_name_match [] (uu : uv) = False;
internal_iface_name_match (i : is) (p_i : p_is) =
  (if i == '+' && null is then True
    else p_i == i && internal_iface_name_match is p_is);

match_iface :: Iface -> [Prelude.Char] -> Bool;
match_iface (Iface i) p_iface = internal_iface_name_match i p_iface;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

empty_WordInterval :: forall a. (Len a) => Wordinterval a;
empty_WordInterval = WordInterval one_word zero_worda;

l2wi :: forall a. (Len a) => [(Word a, Word a)] -> Wordinterval a;
l2wi [] = empty_WordInterval;
l2wi [(s, e)] = WordInterval s e;
l2wi ((s, e) : v : va) = RangeUnion (WordInterval s e) (l2wi (v : va));

wi2l :: forall a. (Len0 a) => Wordinterval a -> [(Word a, Word a)];
wi2l (RangeUnion r1 r2) = wi2l r1 ++ wi2l r2;
wi2l (WordInterval s e) = (if less_word e s then [] else [(s, e)]);

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

mod_nat :: Nat -> Nat -> Nat;
mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n = (divide_nat m n, mod_nat m n);

list_replace1 :: forall a. (Eq a) => a -> a -> [a] -> [a];
list_replace1 uu uv [] = [];
list_replace1 a b (x : xs) =
  (if a == x then b : xs else x : list_replace1 a b xs);

goup_by_zeros ::
  [Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))] ->
    [[Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))]];
goup_by_zeros [] = [];
goup_by_zeros (x : xs) =
  (if equal_word x zero_worda
    then takeWhile (\ xa -> equal_word xa zero_worda) (x : xs) :
           goup_by_zeros (dropWhile (\ xa -> equal_word xa zero_worda) xs)
    else [x] : goup_by_zeros xs);

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

iface_name_is_wildcard :: [Prelude.Char] -> Bool;
iface_name_is_wildcard [] = False;
iface_name_is_wildcard [s] = s == '+';
iface_name_is_wildcard (uu : v : va) = iface_name_is_wildcard (v : va);

internal_iface_name_subset :: [Prelude.Char] -> [Prelude.Char] -> Bool;
internal_iface_name_subset i1 i2 =
  (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of {
    (True, True) ->
      less_eq_nat (size_list i2) (size_list i1) &&
        take (minus_nat (size_list i2) one_nat) i1 == butlast i2;
    (True, False) -> False;
    (False, True) -> take (minus_nat (size_list i2) one_nat) i1 == butlast i2;
    (False, False) -> i1 == i2;
  });

iface_sel :: Iface -> [Prelude.Char];
iface_sel (Iface x) = x;

iface_subset :: Iface -> Iface -> Bool;
iface_subset i1 i2 = internal_iface_name_subset (iface_sel i1) (iface_sel i2);

add_match :: forall a. Match_expr a -> [Rule a] -> [Rule a];
add_match m rs = map (\ (Rule ma a) -> Rule (MatchAnd m ma) a) rs;

apfst :: forall a b c. (a -> b) -> (a, c) -> (b, c);
apfst f (x, y) = (f x, y);

char_of_nat :: Nat -> Prelude.Char;
char_of_nat =
  (let chr k | (0 <= k && k < 256) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger) .
    integer_of_nat;

mk_Set :: forall a. [a] -> Set a;
mk_Set = Set;

word_next :: forall a. (Len a) => Word a -> Word a;
word_next a =
  (if equal_word a max_word then max_word else plus_word a one_word);

word_prev :: forall a. (Len a) => Word a -> Word a;
word_prev a =
  (if equal_word a zero_worda then zero_worda else minus_word a one_word);

word_uptoa :: forall a. (Len0 a) => Word a -> Word a -> [Word a];
word_uptoa a b =
  (if equal_word a b then [a] else a : word_uptoa (plus_word a one_word) b);

word_upto :: forall a. (Len0 a) => Word a -> Word a -> [Word a];
word_upto a b = word_uptoa a b;

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n =
  (if equal_nat n zero_nat then zero
    else let {
           (m, q) = divmod_nat n (nat_of_integer (2 :: Integer));
           ma = times (numeral (Bit0 One)) (of_nat m);
         } in (if equal_nat q zero_nat then ma else plus ma one));

ipv4addr_of_nat :: Nat -> Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4addr_of_nat n = of_nat n;

nat_of_ipv4addr :: Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> Nat;
nat_of_ipv4addr a = unat a;

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

internal_iface_name_wildcard_longest ::
  [Prelude.Char] -> [Prelude.Char] -> Maybe [Prelude.Char];
internal_iface_name_wildcard_longest i1 i2 =
  (if take (min (minus_nat (size_list i1) one_nat)
             (minus_nat (size_list i2) one_nat))
        i1 ==
        take (min (minus_nat (size_list i1) one_nat)
               (minus_nat (size_list i2) one_nat))
          i2
    then Just (if less_eq_nat (size_list i1) (size_list i2) then i2 else i1)
    else Nothing);

map_option :: forall a b. (a -> b) -> Maybe a -> Maybe b;
map_option f Nothing = Nothing;
map_option f (Just x2) = Just (f x2);

iface_conjunct :: Iface -> Iface -> Maybe Iface;
iface_conjunct (Iface i1) (Iface i2) =
  (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2) of {
    (True, True) ->
      map_option Iface (internal_iface_name_wildcard_longest i1 i2);
    (True, False) ->
      (if match_iface (Iface i1) i2 then Just (Iface i2) else Nothing);
    (False, True) ->
      (if match_iface (Iface i2) i1 then Just (Iface i1) else Nothing);
    (False, False) -> (if i1 == i2 then Just (Iface i1) else Nothing);
  });

bitAND_int :: Int -> Int -> Int;
bitAND_int (Int_of_integer i) (Int_of_integer j) =
  Int_of_integer (((Data_Bits..&.) :: Integer -> Integer -> Integer) i j);

bitAND_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
bitAND_word a b = word_of_int (bitAND_int (uint a) (uint b));

ipcidr_to_interval_start :: forall a. (Len a) => (Word a, Nat) -> Word a;
ipcidr_to_interval_start (pre, len) =
  let {
    netmask =
      shiftl_word (mask len) (minus_nat ((len_of :: Itself a -> Nat) Type) len);
    network_prefix = bitAND_word pre netmask;
  } in network_prefix;

bitNOT_int :: Int -> Int;
bitNOT_int (Int_of_integer i) =
  Int_of_integer ((Data_Bits.complement :: Integer -> Integer) i);

bitNOT_word :: forall a. (Len0 a) => Word a -> Word a;
bitNOT_word a = word_of_int (bitNOT_int (uint a));

bitOR_int :: Int -> Int -> Int;
bitOR_int (Int_of_integer i) (Int_of_integer j) =
  Int_of_integer (((Data_Bits..|.) :: Integer -> Integer -> Integer) i j);

bitOR_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
bitOR_word a b = word_of_int (bitOR_int (uint a) (uint b));

ipcidr_to_interval_end :: forall a. (Len a) => (Word a, Nat) -> Word a;
ipcidr_to_interval_end (pre, len) =
  let {
    netmask =
      shiftl_word (mask len) (minus_nat ((len_of :: Itself a -> Nat) Type) len);
    network_prefix = bitAND_word pre netmask;
  } in bitOR_word network_prefix (bitNOT_word netmask);

ipcidr_to_interval :: forall a. (Len a) => (Word a, Nat) -> (Word a, Word a);
ipcidr_to_interval cidr =
  (ipcidr_to_interval_start cidr, ipcidr_to_interval_end cidr);

iprange_interval :: forall a. (Len a) => (Word a, Word a) -> Wordinterval a;
iprange_interval (ip_start, ip_end) = WordInterval ip_start ip_end;

ipcidr_tuple_to_wordinterval ::
  forall a. (Len a) => (Word a, Nat) -> Wordinterval a;
ipcidr_tuple_to_wordinterval iprng =
  iprange_interval (ipcidr_to_interval iprng);

wordinterval_setminusa ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_setminusa (WordInterval s e) (WordInterval ms me) =
  (if less_word e s || less_word me ms then WordInterval s e
    else (if less_eq_word e me
           then WordInterval (if equal_word ms zero_worda then one_word else s)
                  (min e (word_prev ms))
           else (if less_eq_word ms s
                  then WordInterval (max s (word_next me))
                         (if equal_word me max_word then zero_worda else e)
                  else RangeUnion
                         (WordInterval
                           (if equal_word ms zero_worda then one_word else s)
                           (word_prev ms))
                         (WordInterval (word_next me)
                           (if equal_word me max_word then zero_worda
                             else e)))));
wordinterval_setminusa (RangeUnion r1 r2) t =
  RangeUnion (wordinterval_setminusa r1 t) (wordinterval_setminusa r2 t);
wordinterval_setminusa (WordInterval v va) (RangeUnion r1 r2) =
  wordinterval_setminusa (wordinterval_setminusa (WordInterval v va) r1) r2;

wordinterval_empty_shallow :: forall a. (Len0 a) => Wordinterval a -> Bool;
wordinterval_empty_shallow (WordInterval s e) = less_word e s;
wordinterval_empty_shallow (RangeUnion uu uv) = False;

wordinterval_optimize_empty2 ::
  forall a. (Len0 a) => Wordinterval a -> Wordinterval a;
wordinterval_optimize_empty2 (RangeUnion r1 r2) =
  let {
    r1o = wordinterval_optimize_empty2 r1;
    r2o = wordinterval_optimize_empty2 r2;
  } in (if wordinterval_empty_shallow r1o then r2o
         else (if wordinterval_empty_shallow r2o then r1o
                else RangeUnion r1o r2o));
wordinterval_optimize_empty2 (WordInterval v va) = WordInterval v va;

disjoint_intervals ::
  forall a. (Len0 a) => (Word a, Word a) -> (Word a, Word a) -> Bool;
disjoint_intervals a b =
  let {
    (s, e) = a;
    (sa, ea) = b;
  } in less_word ea s || (less_word e sa || (less_word e s || less_word ea sa));

not_disjoint_intervals ::
  forall a. (Len0 a) => (Word a, Word a) -> (Word a, Word a) -> Bool;
not_disjoint_intervals a b =
  let {
    (s, e) = a;
    (sa, ea) = b;
  } in less_eq_word s ea &&
         less_eq_word sa e && less_eq_word s e && less_eq_word sa ea;

merge_overlap ::
  forall a.
    (Len0 a) => (Word a, Word a) -> [(Word a, Word a)] -> [(Word a, Word a)];
merge_overlap s [] = [s];
merge_overlap (sa, ea) ((s, e) : ss) =
  (if not_disjoint_intervals (sa, ea) (s, e) then (min sa s, max ea e) : ss
    else (s, e) : merge_overlap (sa, ea) ss);

listwordinterval_compress ::
  forall a. (Len0 a) => [(Word a, Word a)] -> [(Word a, Word a)];
listwordinterval_compress [] = [];
listwordinterval_compress (s : ss) =
  (if all (disjoint_intervals s) ss then s : listwordinterval_compress ss
    else listwordinterval_compress (merge_overlap s ss));

merge_adjacent ::
  forall a.
    (Len a) => (Word a, Word a) -> [(Word a, Word a)] -> [(Word a, Word a)];
merge_adjacent s [] = [s];
merge_adjacent (sa, ea) ((s, e) : ss) =
  (if less_eq_word sa ea && less_eq_word s e && equal_word (word_next ea) s
    then (sa, e) : ss
    else (if less_eq_word sa ea &&
               less_eq_word s e && equal_word (word_next e) sa
           then (s, ea) : ss else (s, e) : merge_adjacent (sa, ea) ss));

listwordinterval_adjacent ::
  forall a. (Len a) => [(Word a, Word a)] -> [(Word a, Word a)];
listwordinterval_adjacent [] = [];
listwordinterval_adjacent ((s, e) : ss) =
  (if all (\ (sa, ea) ->
            not (less_eq_word s e &&
                  less_eq_word sa ea &&
                    (equal_word (word_next e) sa ||
                      equal_word (word_next ea) s)))
        ss
    then (s, e) : listwordinterval_adjacent ss
    else listwordinterval_adjacent (merge_adjacent (s, e) ss));

wordinterval_compress :: forall a. (Len a) => Wordinterval a -> Wordinterval a;
wordinterval_compress r =
  l2wi (remdups
         (listwordinterval_adjacent
           (listwordinterval_compress
             (wi2l (wordinterval_optimize_empty2 r)))));

wordinterval_setminus ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_setminus r1 r2 =
  wordinterval_compress (wordinterval_setminusa r1 r2);

wordinterval_union ::
  forall a. (Len0 a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_union r1 r2 = RangeUnion r1 r2;

wordinterval_Union :: forall a. (Len a) => [Wordinterval a] -> Wordinterval a;
wordinterval_Union ws =
  wordinterval_compress (foldr wordinterval_union ws empty_WordInterval);

wordinterval_lowest_element ::
  forall a. (Len0 a) => Wordinterval a -> Maybe (Word a);
wordinterval_lowest_element (WordInterval s e) =
  (if less_eq_word s e then Just s else Nothing);
wordinterval_lowest_element (RangeUnion a b) =
  (case (wordinterval_lowest_element a, wordinterval_lowest_element b) of {
    (Nothing, Nothing) -> Nothing;
    (Nothing, Just aa) -> Just aa;
    (Just aa, Nothing) -> Just aa;
    (Just aa, Just ba) -> Just (if less_word aa ba then aa else ba);
  });

pfxm_prefix :: forall a. (Len a) => Prefix_match a -> Word a;
pfxm_prefix (PrefixMatch x1 x2) = x1;

pfxm_length :: forall a. (Len a) => Prefix_match a -> Nat;
pfxm_length (PrefixMatch x1 x2) = x2;

pfxm_mask :: forall a. (Len a) => Prefix_match a -> Word a;
pfxm_mask x =
  mask (minus_nat ((len_of :: Itself a -> Nat) Type) (pfxm_length x));

prefix_to_wordinterval :: forall a. (Len a) => Prefix_match a -> Wordinterval a;
prefix_to_wordinterval pfx =
  WordInterval (pfxm_prefix pfx) (bitOR_word (pfxm_prefix pfx) (pfxm_mask pfx));

wordinterval_empty :: forall a. (Len0 a) => Wordinterval a -> Bool;
wordinterval_empty (WordInterval s e) = less_word e s;
wordinterval_empty (RangeUnion r1 r2) =
  wordinterval_empty r1 && wordinterval_empty r2;

wordinterval_subset ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Bool;
wordinterval_subset r1 r2 = wordinterval_empty (wordinterval_setminus r1 r2);

valid_prefix :: forall a. (Len a) => Prefix_match a -> Bool;
valid_prefix pf =
  equal_word (bitAND_word (pfxm_mask pf) (pfxm_prefix pf)) zero_worda;

largest_contained_prefix ::
  forall a. (Len a) => Word a -> Wordinterval a -> Maybe (Prefix_match a);
largest_contained_prefix a r =
  let {
    cs = map (PrefixMatch a) ((pfxes :: Itself a -> [Nat]) Type);
    cfs = find (\ s ->
                 valid_prefix s &&
                   wordinterval_subset (prefix_to_wordinterval s) r)
            cs;
  } in cfs;

wordinterval_CIDR_split1 ::
  forall a.
    (Len a) => Wordinterval a -> (Maybe (Prefix_match a), Wordinterval a);
wordinterval_CIDR_split1 r =
  let {
    a = wordinterval_lowest_element r;
  } in (case a of {
         Nothing -> (Nothing, r);
         Just aa ->
           (case largest_contained_prefix aa r of {
             Nothing -> (Nothing, r);
             Just m ->
               (Just m, wordinterval_setminus r (prefix_to_wordinterval m));
           });
       });

wordinterval_CIDR_split_prefixmatch ::
  forall a. (Len a) => Wordinterval a -> [Prefix_match a];
wordinterval_CIDR_split_prefixmatch rs =
  (if not (wordinterval_empty rs)
    then (case wordinterval_CIDR_split1 rs of {
           (Nothing, _) -> [];
           (Just s, u) -> s : wordinterval_CIDR_split_prefixmatch u;
         })
    else []);

prefix_match_to_CIDR :: forall a. (Len a) => Prefix_match a -> (Word a, Nat);
prefix_match_to_CIDR pfx = (pfxm_prefix pfx, pfxm_length pfx);

cidr_split :: forall a. (Len a) => Wordinterval a -> [(Word a, Nat)];
cidr_split rs =
  map prefix_match_to_CIDR (wordinterval_CIDR_split_prefixmatch rs);

ipassmt_diff ::
  forall a.
    (Len a) => [(Iface, [(Word a, Nat)])] ->
                 [(Iface, [(Word a, Nat)])] ->
                   [(Iface, ([(Word a, Nat)], [(Word a, Nat)]))];
ipassmt_diff a b =
  let {
    t = (\ aa ->
          (case aa of {
            Nothing -> empty_WordInterval;
            Just s -> wordinterval_Union (map ipcidr_tuple_to_wordinterval s);
          }));
    k = (\ x y d ->
          cidr_split (wordinterval_setminus (t (map_of x d)) (t (map_of y d))));
  } in map (\ d -> (d, (k a b d, k b a d))) (remdups (map fst (a ++ b)));

iPv6ICMP :: Word (Bit0 (Bit0 (Bit0 Num1)));
iPv6ICMP = word_of_int (Int_of_integer (58 :: Integer));

getNeg :: forall a. [Negation_type a] -> [a];
getNeg [] = [];
getNeg (Neg x : xs) = x : getNeg xs;
getNeg (Pos v : xs) = getNeg xs;

getPos :: forall a. [Negation_type a] -> [a];
getPos [] = [];
getPos (Pos x : xs) = x : getPos xs;
getPos (Neg v : xs) = getPos xs;

pc_oiface :: forall a. Parts_connection_ext a -> [Prelude.Char];
pc_oiface
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport more) =
  pc_oiface;

pc_iiface :: forall a. Parts_connection_ext a -> [Prelude.Char];
pc_iiface
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport more) =
  pc_iiface;

pc_sport ::
  forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
pc_sport
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport more) =
  pc_sport;

pc_proto :: forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 Num1)));
pc_proto
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport more) =
  pc_proto;

pc_dport ::
  forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
pc_dport
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport more) =
  pc_dport;

p_oiface :: forall a b. (Len a) => Simple_packet_ext a b -> [Prelude.Char];
p_oiface
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_payload more)
  = p_oiface;

p_iiface :: forall a b. (Len a) => Simple_packet_ext a b -> [Prelude.Char];
p_iiface
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_payload more)
  = p_iiface;

simple_match_port ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
    Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
    Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) -> Bool;
simple_match_port (s, e) p_p = less_eq_word s p_p && less_eq_word p_p e;

p_sport ::
  forall a b.
    (Len a) => Simple_packet_ext a b -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
p_sport
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_payload more)
  = p_sport;

p_proto ::
  forall a b.
    (Len a) => Simple_packet_ext a b -> Word (Bit0 (Bit0 (Bit0 Num1)));
p_proto
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_payload more)
  = p_proto;

p_dport ::
  forall a b.
    (Len a) => Simple_packet_ext a b -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
p_dport
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_payload more)
  = p_dport;

sports ::
  forall a b.
    (Len a) => Simple_match_ext a b ->
                 (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                   Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
sports (Simple_match_ext iiface oiface src dst proto sports dports more) =
  sports;

oiface :: forall a b. (Len a) => Simple_match_ext a b -> Iface;
oiface (Simple_match_ext iiface oiface src dst proto sports dports more) =
  oiface;

iiface :: forall a b. (Len a) => Simple_match_ext a b -> Iface;
iiface (Simple_match_ext iiface oiface src dst proto sports dports more) =
  iiface;

dports ::
  forall a b.
    (Len a) => Simple_match_ext a b ->
                 (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                   Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
dports (Simple_match_ext iiface oiface src dst proto sports dports more) =
  dports;

proto :: forall a b. (Len a) => Simple_match_ext a b -> Protocol;
proto (Simple_match_ext iiface oiface src dst proto sports dports more) = proto;

simple_match_ip :: forall a. (Len a) => (Word a, Nat) -> Word a -> Bool;
simple_match_ip (base, len) p_ip =
  less_eq_word
    (bitAND_word base
      (shiftl_word (mask len)
        (minus_nat ((len_of :: Itself a -> Nat) Type) len)))
    p_ip &&
    less_eq_word p_ip
      (bitOR_word base
        (mask (minus_nat ((len_of :: Itself a -> Nat) Type) len)));

p_src :: forall a b. (Len a) => Simple_packet_ext a b -> Word a;
p_src (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
        p_tcp_flags p_payload more)
  = p_src;

p_dst :: forall a b. (Len a) => Simple_packet_ext a b -> Word a;
p_dst (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
        p_tcp_flags p_payload more)
  = p_dst;

src :: forall a b. (Len a) => Simple_match_ext a b -> (Word a, Nat);
src (Simple_match_ext iiface oiface src dst proto sports dports more) = src;

dst :: forall a b. (Len a) => Simple_match_ext a b -> (Word a, Nat);
dst (Simple_match_ext iiface oiface src dst proto sports dports more) = dst;

match_proto :: Protocol -> Word (Bit0 (Bit0 (Bit0 Num1))) -> Bool;
match_proto ProtoAny uu = True;
match_proto (Proto p) p_p = equal_word p_p p;

simple_matches ::
  forall a b. (Len a) => Simple_match_ext a () -> Simple_packet_ext a b -> Bool;
simple_matches m p =
  match_iface (iiface m) (p_iiface p) &&
    match_iface (oiface m) (p_oiface p) &&
      simple_match_ip (src m) (p_src p) &&
        simple_match_ip (dst m) (p_dst p) &&
          match_proto (proto m) (p_proto p) &&
            simple_match_port (sports m) (p_sport p) &&
              simple_match_port (dports m) (p_dport p);

simple_fw ::
  forall a b. (Len a) => [Simple_rule a] -> Simple_packet_ext a b -> State;
simple_fw [] uu = Undecided;
simple_fw (SimpleRule m Accepta : rs) p =
  (if simple_matches m p then Decision FinalAllow else simple_fw rs p);
simple_fw (SimpleRule m Dropa : rs) p =
  (if simple_matches m p then Decision FinalDeny else simple_fw rs p);

bot_set :: forall a. Set a;
bot_set = Set [];

runFw ::
  forall a b.
    (Len a) => Word a ->
                 Word a -> Parts_connection_ext b -> [Simple_rule a] -> State;
runFw s d c rs =
  simple_fw rs
    (Simple_packet_ext (pc_iiface c) (pc_oiface c) s d (pc_proto c) (pc_sport c)
      (pc_dport c) (insert TCP_SYN bot_set) [] ());

zero_word :: forall a. (Len a) => Word a;
zero_word = zero_worda;

oiface_sel :: forall a. (Len a) => Common_primitive a -> Iface;
oiface_sel (OIface x4) = x4;

iiface_sel :: forall a. (Len a) => Common_primitive a -> Iface;
iiface_sel (IIface x3) = x3;

is_Oiface :: forall a. (Len a) => Common_primitive a -> Bool;
is_Oiface (Src x1) = False;
is_Oiface (Dst x2) = False;
is_Oiface (IIface x3) = False;
is_Oiface (OIface x4) = True;
is_Oiface (Prot x5) = False;
is_Oiface (Src_Ports x6) = False;
is_Oiface (Dst_Ports x7) = False;
is_Oiface (L4_Flags x8) = False;
is_Oiface (CT_State x9) = False;
is_Oiface (Extra x10) = False;

is_Iiface :: forall a. (Len a) => Common_primitive a -> Bool;
is_Iiface (Src x1) = False;
is_Iiface (Dst x2) = False;
is_Iiface (IIface x3) = True;
is_Iiface (OIface x4) = False;
is_Iiface (Prot x5) = False;
is_Iiface (Src_Ports x6) = False;
is_Iiface (Dst_Ports x7) = False;
is_Iiface (L4_Flags x8) = False;
is_Iiface (CT_State x9) = False;
is_Iiface (Extra x10) = False;

primitive_extractor ::
  forall a b.
    (a -> Bool, a -> b) -> Match_expr a -> ([Negation_type b], Match_expr a);
primitive_extractor uu MatchAny = ([], MatchAny);
primitive_extractor (disc, sel) (Match a) =
  (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a));
primitive_extractor (disc, sel) (MatchNot (Match a)) =
  (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)));
primitive_extractor c (MatchAnd ms1 ms2) =
  let {
    (a1, ms1a) = primitive_extractor c ms1;
    (a2, ms2a) = primitive_extractor c ms2;
  } in (a1 ++ a2, MatchAnd ms1a ms2a);
primitive_extractor uv (MatchNot (MatchNot va)) = error "undefined";
primitive_extractor uv (MatchNot (MatchAnd va vb)) = error "undefined";
primitive_extractor uv (MatchNot MatchAny) = error "undefined";

collect_ifacesa :: forall a. (Len a) => [Rule (Common_primitive a)] -> [Iface];
collect_ifacesa [] = [];
collect_ifacesa (Rule m a : rs) =
  filter (\ iface -> not (equal_iface iface ifaceAny))
    (map (\ aa -> (case aa of {
                    Pos i -> i;
                    Neg i -> i;
                  }))
       (fst (primitive_extractor (is_Iiface, iiface_sel) m)) ++
      map (\ aa -> (case aa of {
                     Pos i -> i;
                     Neg i -> i;
                   }))
        (fst (primitive_extractor (is_Oiface, oiface_sel) m)) ++
        collect_ifacesa rs);

mergesort_remdups :: forall a. (Eq a, Linorder a) => [a] -> [a];
mergesort_remdups xs = merge_list [] (map (\ x -> [x]) xs);

collect_ifaces :: forall a. (Len a) => [Rule (Common_primitive a)] -> [Iface];
collect_ifaces rs = mergesort_remdups (collect_ifacesa rs);

iface_is_wildcard :: Iface -> Bool;
iface_is_wildcard ifce = iface_name_is_wildcard (iface_sel ifce);

map_of_ipassmt ::
  forall a. [(Iface, [(Word a, Nat)])] -> Iface -> Maybe [(Word a, Nat)];
map_of_ipassmt ipassmt =
  (if distinct (map fst ipassmt) &&
        ball (image fst (Set ipassmt))
          (\ iface -> not (iface_is_wildcard iface))
    then map_of ipassmt else error "undefined");

wordinterval_UNIV :: forall a. (Len a) => Wordinterval a;
wordinterval_UNIV = WordInterval zero_worda max_word;

wordinterval_invert :: forall a. (Len a) => Wordinterval a -> Wordinterval a;
wordinterval_invert r = wordinterval_setminus wordinterval_UNIV r;

raw_ports_invert ::
  [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
     Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
raw_ports_invert ps = wi2l (wordinterval_invert (l2wi ps));

wordinterval_intersectiona ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_intersectiona (WordInterval sa ea) (WordInterval s e) =
  (if less_word ea sa ||
        (less_word e s ||
          (less_word e sa ||
            (less_word ea s || (less_word ea sa || less_word e s))))
    then empty_WordInterval else WordInterval (max sa s) (min ea e));
wordinterval_intersectiona (RangeUnion r1 r2) t =
  RangeUnion (wordinterval_intersectiona r1 t)
    (wordinterval_intersectiona r2 t);
wordinterval_intersectiona (WordInterval v va) (RangeUnion r1 r2) =
  RangeUnion (wordinterval_intersectiona (WordInterval v va) r1)
    (wordinterval_intersectiona (WordInterval v va) r2);

wordinterval_intersection ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_intersection r1 r2 =
  wordinterval_compress (wordinterval_intersectiona r1 r2);

partIps ::
  forall a. (Len a) => Wordinterval a -> [Wordinterval a] -> [Wordinterval a];
partIps uu [] = [];
partIps s (t : ts) =
  (if wordinterval_empty s then t : ts
    else (if wordinterval_empty (wordinterval_intersection s t)
           then t : partIps s ts
           else (if wordinterval_empty (wordinterval_setminus t s)
                  then t : partIps (wordinterval_setminus s t) ts
                  else wordinterval_intersection t s :
                         wordinterval_setminus t s :
                           partIps (wordinterval_setminus s t) ts)));

ipt_iprange_to_interval ::
  forall a. (Len a) => Ipt_iprange a -> (Word a, Word a);
ipt_iprange_to_interval (IpAddr addr) = (addr, addr);
ipt_iprange_to_interval (IpAddrNetmask pre len) = ipcidr_to_interval (pre, len);
ipt_iprange_to_interval (IpAddrRange ip1 ip2) = (ip1, ip2);

ipt_iprange_to_cidr :: forall a. (Len a) => Ipt_iprange a -> [(Word a, Nat)];
ipt_iprange_to_cidr ips =
  cidr_split (iprange_interval (ipt_iprange_to_interval ips));

all_but_those_ips :: forall a. (Len a) => [(Word a, Nat)] -> [(Word a, Nat)];
all_but_those_ips cidrips =
  cidr_split (wordinterval_invert (l2wi (map ipcidr_to_interval cidrips)));

ipassmt_iprange_translate ::
  forall a. (Len a) => Negation_type [Ipt_iprange a] -> [(Word a, Nat)];
ipassmt_iprange_translate (Pos ips) = concatMap ipt_iprange_to_cidr ips;
ipassmt_iprange_translate (Neg ips) =
  all_but_those_ips (concatMap ipt_iprange_to_cidr ips);

to_ipassmt ::
  forall a.
    (Len a) => [(Iface, Negation_type [Ipt_iprange a])] ->
                 [(Iface, [(Word a, Nat)])];
to_ipassmt assmt =
  map (\ (ifce, ips) -> (ifce, ipassmt_iprange_translate ips)) assmt;

matchOr :: forall a. Match_expr a -> Match_expr a -> Match_expr a;
matchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2));

routing_match :: forall a b. (Len a) => Routing_rule_ext a b -> Prefix_match a;
routing_match (Routing_rule_ext routing_match metric routing_action more) =
  routing_match;

metric :: forall a b. (Len a) => Routing_rule_ext a b -> Nat;
metric (Routing_rule_ext routing_match metric routing_action more) = metric;

routing_rule_sort_key ::
  forall a b. (Len a) => Routing_rule_ext a b -> Linord_helper Int Nat;
routing_rule_sort_key =
  (\ r ->
    LinordHelper
      (minus_int zero_int (int_of_nat (pfxm_length (routing_match r))))
      (metric r));

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  let {
    (lts, (eqs, gts)) = part f pivot xs;
    xa = f x;
  } in (if less xa pivot then (x : lts, (eqs, gts))
         else (if less pivot xa then (lts, (eqs, x : gts))
                else (lts, (x : eqs, gts))));
part f pivot [] = ([], ([], []));

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      let {
        (lts, (eqs, gts)) =
          part f
            (f (nth xs
                 (divide_nat (size_list xs) (nat_of_integer (2 :: Integer)))))
            xs;
      } in sort_key f lts ++ eqs ++ sort_key f gts;
  });

sort_rtbl ::
  forall a. (Len a) => [Routing_rule_ext a ()] -> [Routing_rule_ext a ()];
sort_rtbl = sort_key routing_rule_sort_key;

getOneIp :: forall a. (Len a) => Wordinterval a -> Word a;
getOneIp (WordInterval b uu) = b;
getOneIp (RangeUnion r1 r2) =
  (if wordinterval_empty r1 then getOneIp r2 else getOneIp r1);

partitioningIps ::
  forall a. (Len a) => [Wordinterval a] -> [Wordinterval a] -> [Wordinterval a];
partitioningIps [] ts = ts;
partitioningIps (s : ss) ts = partIps s (partitioningIps ss ts);

extract_src_dst_ips ::
  forall a. (Len a) => [Simple_rule a] -> [(Word a, Nat)] -> [(Word a, Nat)];
extract_src_dst_ips [] ts = ts;
extract_src_dst_ips (SimpleRule m uu : ss) ts =
  extract_src_dst_ips ss (src m : dst m : ts);

extract_IPSets :: forall a. (Len a) => [Simple_rule a] -> [Wordinterval a];
extract_IPSets rs =
  map ipcidr_tuple_to_wordinterval
    (mergesort_remdups (extract_src_dst_ips rs []));

getParts :: forall a. (Len a) => [Simple_rule a] -> [Wordinterval a];
getParts rs = partitioningIps (extract_IPSets rs) [wordinterval_UNIV];

upper_closure_matchexpr ::
  forall a.
    (Len a) => Action ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
upper_closure_matchexpr uu MatchAny = MatchAny;
upper_closure_matchexpr Accept (Match (Extra uv)) = MatchAny;
upper_closure_matchexpr Reject (Match (Extra uw)) = MatchNot MatchAny;
upper_closure_matchexpr Drop (Match (Extra ux)) = MatchNot MatchAny;
upper_closure_matchexpr Drop (Match (Src v)) = Match (Src v);
upper_closure_matchexpr Drop (Match (Dst v)) = Match (Dst v);
upper_closure_matchexpr Drop (Match (IIface v)) = Match (IIface v);
upper_closure_matchexpr Drop (Match (OIface v)) = Match (OIface v);
upper_closure_matchexpr Drop (Match (Prot v)) = Match (Prot v);
upper_closure_matchexpr Drop (Match (Src_Ports v)) = Match (Src_Ports v);
upper_closure_matchexpr Drop (Match (Dst_Ports v)) = Match (Dst_Ports v);
upper_closure_matchexpr Drop (Match (L4_Flags v)) = Match (L4_Flags v);
upper_closure_matchexpr Drop (Match (CT_State v)) = Match (CT_State v);
upper_closure_matchexpr Log (Match m) = Match m;
upper_closure_matchexpr Reject (Match (Src v)) = Match (Src v);
upper_closure_matchexpr Reject (Match (Dst v)) = Match (Dst v);
upper_closure_matchexpr Reject (Match (IIface v)) = Match (IIface v);
upper_closure_matchexpr Reject (Match (OIface v)) = Match (OIface v);
upper_closure_matchexpr Reject (Match (Prot v)) = Match (Prot v);
upper_closure_matchexpr Reject (Match (Src_Ports v)) = Match (Src_Ports v);
upper_closure_matchexpr Reject (Match (Dst_Ports v)) = Match (Dst_Ports v);
upper_closure_matchexpr Reject (Match (L4_Flags v)) = Match (L4_Flags v);
upper_closure_matchexpr Reject (Match (CT_State v)) = Match (CT_State v);
upper_closure_matchexpr (Call v) (Match m) = Match m;
upper_closure_matchexpr Return (Match m) = Match m;
upper_closure_matchexpr (Goto v) (Match m) = Match m;
upper_closure_matchexpr Empty (Match m) = Match m;
upper_closure_matchexpr Unknown (Match m) = Match m;
upper_closure_matchexpr uy (Match (Src v)) = Match (Src v);
upper_closure_matchexpr uy (Match (Dst v)) = Match (Dst v);
upper_closure_matchexpr uy (Match (IIface v)) = Match (IIface v);
upper_closure_matchexpr uy (Match (OIface v)) = Match (OIface v);
upper_closure_matchexpr uy (Match (Prot v)) = Match (Prot v);
upper_closure_matchexpr uy (Match (Src_Ports v)) = Match (Src_Ports v);
upper_closure_matchexpr uy (Match (Dst_Ports v)) = Match (Dst_Ports v);
upper_closure_matchexpr uy (Match (L4_Flags v)) = Match (L4_Flags v);
upper_closure_matchexpr uy (Match (CT_State v)) = Match (CT_State v);
upper_closure_matchexpr Accept (MatchNot (Match (Extra uz))) = MatchAny;
upper_closure_matchexpr Drop (MatchNot (Match (Extra va))) = MatchNot MatchAny;
upper_closure_matchexpr Reject (MatchNot (Match (Extra vb))) =
  MatchNot MatchAny;
upper_closure_matchexpr a (MatchNot (MatchNot m)) = upper_closure_matchexpr a m;
upper_closure_matchexpr a (MatchNot (MatchAnd m1 m2)) =
  let {
    m1a = upper_closure_matchexpr a (MatchNot m1);
    m2a = upper_closure_matchexpr a (MatchNot m2);
  } in (if equal_match_expr m1a MatchAny || equal_match_expr m2a MatchAny
         then MatchAny
         else (if equal_match_expr m1a (MatchNot MatchAny) then m2a
                else (if equal_match_expr m2a (MatchNot MatchAny) then m1a
                       else MatchNot
                              (MatchAnd (MatchNot m1a) (MatchNot m2a)))));
upper_closure_matchexpr Drop (MatchNot (Match (Src va))) =
  MatchNot (Match (Src va));
upper_closure_matchexpr Drop (MatchNot (Match (Dst va))) =
  MatchNot (Match (Dst va));
upper_closure_matchexpr Drop (MatchNot (Match (IIface va))) =
  MatchNot (Match (IIface va));
upper_closure_matchexpr Drop (MatchNot (Match (OIface va))) =
  MatchNot (Match (OIface va));
upper_closure_matchexpr Drop (MatchNot (Match (Prot va))) =
  MatchNot (Match (Prot va));
upper_closure_matchexpr Drop (MatchNot (Match (Src_Ports va))) =
  MatchNot (Match (Src_Ports va));
upper_closure_matchexpr Drop (MatchNot (Match (Dst_Ports va))) =
  MatchNot (Match (Dst_Ports va));
upper_closure_matchexpr Drop (MatchNot (Match (L4_Flags va))) =
  MatchNot (Match (L4_Flags va));
upper_closure_matchexpr Drop (MatchNot (Match (CT_State va))) =
  MatchNot (Match (CT_State va));
upper_closure_matchexpr Drop (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr Log (MatchNot (Match v)) = MatchNot (Match v);
upper_closure_matchexpr Log (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr Reject (MatchNot (Match (Src va))) =
  MatchNot (Match (Src va));
upper_closure_matchexpr Reject (MatchNot (Match (Dst va))) =
  MatchNot (Match (Dst va));
upper_closure_matchexpr Reject (MatchNot (Match (IIface va))) =
  MatchNot (Match (IIface va));
upper_closure_matchexpr Reject (MatchNot (Match (OIface va))) =
  MatchNot (Match (OIface va));
upper_closure_matchexpr Reject (MatchNot (Match (Prot va))) =
  MatchNot (Match (Prot va));
upper_closure_matchexpr Reject (MatchNot (Match (Src_Ports va))) =
  MatchNot (Match (Src_Ports va));
upper_closure_matchexpr Reject (MatchNot (Match (Dst_Ports va))) =
  MatchNot (Match (Dst_Ports va));
upper_closure_matchexpr Reject (MatchNot (Match (L4_Flags va))) =
  MatchNot (Match (L4_Flags va));
upper_closure_matchexpr Reject (MatchNot (Match (CT_State va))) =
  MatchNot (Match (CT_State va));
upper_closure_matchexpr Reject (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr (Call v) (MatchNot (Match va)) = MatchNot (Match va);
upper_closure_matchexpr (Call v) (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr Return (MatchNot (Match v)) = MatchNot (Match v);
upper_closure_matchexpr Return (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr (Goto v) (MatchNot (Match va)) = MatchNot (Match va);
upper_closure_matchexpr (Goto v) (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr Empty (MatchNot (Match v)) = MatchNot (Match v);
upper_closure_matchexpr Empty (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr Unknown (MatchNot (Match v)) = MatchNot (Match v);
upper_closure_matchexpr Unknown (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr vc (MatchNot (Match (Src va))) =
  MatchNot (Match (Src va));
upper_closure_matchexpr vc (MatchNot (Match (Dst va))) =
  MatchNot (Match (Dst va));
upper_closure_matchexpr vc (MatchNot (Match (IIface va))) =
  MatchNot (Match (IIface va));
upper_closure_matchexpr vc (MatchNot (Match (OIface va))) =
  MatchNot (Match (OIface va));
upper_closure_matchexpr vc (MatchNot (Match (Prot va))) =
  MatchNot (Match (Prot va));
upper_closure_matchexpr vc (MatchNot (Match (Src_Ports va))) =
  MatchNot (Match (Src_Ports va));
upper_closure_matchexpr vc (MatchNot (Match (Dst_Ports va))) =
  MatchNot (Match (Dst_Ports va));
upper_closure_matchexpr vc (MatchNot (Match (L4_Flags va))) =
  MatchNot (Match (L4_Flags va));
upper_closure_matchexpr vc (MatchNot (Match (CT_State va))) =
  MatchNot (Match (CT_State va));
upper_closure_matchexpr vc (MatchNot MatchAny) = MatchNot MatchAny;
upper_closure_matchexpr a (MatchAnd m1 m2) =
  MatchAnd (upper_closure_matchexpr a m1) (upper_closure_matchexpr a m2);

compress_normalize_primitive_monad ::
  forall a.
    [Match_expr a -> Maybe (Match_expr a)] ->
      Match_expr a -> Maybe (Match_expr a);
compress_normalize_primitive_monad [] m = Just m;
compress_normalize_primitive_monad (f : fs) m =
  (case f m of {
    Nothing -> Nothing;
    Just a -> compress_normalize_primitive_monad fs a;
  });

alist_and :: forall a. [Negation_type a] -> Match_expr a;
alist_and [] = MatchAny;
alist_and [Pos e] = Match e;
alist_and [Neg e] = MatchNot (Match e);
alist_and (Pos e : v : va) = MatchAnd (Match e) (alist_and (v : va));
alist_and (Neg e : v : va) = MatchAnd (MatchNot (Match e)) (alist_and (v : va));

negPos_map :: forall a b. (a -> b) -> [Negation_type a] -> [Negation_type b];
negPos_map uu [] = [];
negPos_map f (Pos a : asa) = Pos (f a) : negPos_map f asa;
negPos_map f (Neg a : asa) = Neg (f a) : negPos_map f asa;

compress_normalize_primitive ::
  forall a b.
    (a -> Bool, a -> b) ->
      (b -> a) ->
        ([Negation_type b] -> Maybe ([b], [b])) ->
          Match_expr a -> Maybe (Match_expr a);
compress_normalize_primitive disc_sel c f m =
  let {
    (asa, rst) = primitive_extractor disc_sel m;
  } in map_option
         (\ (as_pos, as_neg) ->
           MatchAnd
             (alist_and (negPos_map c (map Pos as_pos ++ map Neg as_neg))) rst)
         (f asa);

compress_pos_interfaces :: [Iface] -> Maybe Iface;
compress_pos_interfaces [] = Just ifaceAny;
compress_pos_interfaces [i] = Just i;
compress_pos_interfaces (i1 : i2 : is) =
  (case iface_conjunct i1 i2 of {
    Nothing -> Nothing;
    Just i -> compress_pos_interfaces (i : is);
  });

compress_interfaces :: [Negation_type Iface] -> Maybe ([Iface], [Iface]);
compress_interfaces ifces =
  (case compress_pos_interfaces (getPos ifces) of {
    Nothing -> Nothing;
    Just i ->
      (if any (iface_subset i) (getNeg ifces) then Nothing
        else (if not (iface_is_wildcard i) then Just ([i], [])
               else Just ((if equal_iface i ifaceAny then [] else [i]),
                           getNeg ifces)));
  });

compress_normalize_output_interfaces ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Maybe (Match_expr (Common_primitive a));
compress_normalize_output_interfaces m =
  compress_normalize_primitive (is_Oiface, oiface_sel) OIface
    compress_interfaces m;

compress_normalize_input_interfaces ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Maybe (Match_expr (Common_primitive a));
compress_normalize_input_interfaces m =
  compress_normalize_primitive (is_Iiface, iiface_sel) IIface
    compress_interfaces m;

prot_sel :: forall a. (Len a) => Common_primitive a -> Protocol;
prot_sel (Prot x5) = x5;

is_Prot :: forall a. (Len a) => Common_primitive a -> Bool;
is_Prot (Src x1) = False;
is_Prot (Dst x2) = False;
is_Prot (IIface x3) = False;
is_Prot (OIface x4) = False;
is_Prot (Prot x5) = True;
is_Prot (Src_Ports x6) = False;
is_Prot (Dst_Ports x7) = False;
is_Prot (L4_Flags x8) = False;
is_Prot (CT_State x9) = False;
is_Prot (Extra x10) = False;

simple_proto_conjunct :: Protocol -> Protocol -> Maybe Protocol;
simple_proto_conjunct ProtoAny proto = Just proto;
simple_proto_conjunct (Proto v) ProtoAny = Just (Proto v);
simple_proto_conjunct (Proto p1) (Proto p2) =
  (if equal_word p1 p2 then Just (Proto p1) else Nothing);

compress_pos_protocols :: [Protocol] -> Maybe Protocol;
compress_pos_protocols [] = Just ProtoAny;
compress_pos_protocols [p] = Just p;
compress_pos_protocols (p1 : p2 : ps) =
  (case simple_proto_conjunct p1 p2 of {
    Nothing -> Nothing;
    Just p -> compress_pos_protocols (p : ps);
  });

compress_protocols ::
  [Negation_type Protocol] -> Maybe ([Protocol], [Protocol]);
compress_protocols ps =
  (case compress_pos_protocols (getPos ps) of {
    Nothing -> Nothing;
    Just proto ->
      (if membera (getNeg ps) ProtoAny ||
            all (\ p -> membera (getNeg ps) (Proto p))
              (word_upto zero_worda
                (word_of_int (Int_of_integer (255 :: Integer))))
        then Nothing
        else (if equal_protocol proto ProtoAny then Just ([], getNeg ps)
               else (if any (\ p ->
                              not (is_none (simple_proto_conjunct proto p)))
                          (getNeg ps)
                      then Nothing else Just ([proto], []))));
  });

compress_normalize_protocols_step ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Maybe (Match_expr (Common_primitive a));
compress_normalize_protocols_step m =
  compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m;

src_ports_sel :: forall a. (Len a) => Common_primitive a -> Ipt_l4_ports;
src_ports_sel (Src_Ports x6) = x6;

dst_ports_sel :: forall a. (Len a) => Common_primitive a -> Ipt_l4_ports;
dst_ports_sel (Dst_Ports x7) = x7;

is_Src_Ports :: forall a. (Len a) => Common_primitive a -> Bool;
is_Src_Ports (Src x1) = False;
is_Src_Ports (Dst x2) = False;
is_Src_Ports (IIface x3) = False;
is_Src_Ports (OIface x4) = False;
is_Src_Ports (Prot x5) = False;
is_Src_Ports (Src_Ports x6) = True;
is_Src_Ports (Dst_Ports x7) = False;
is_Src_Ports (L4_Flags x8) = False;
is_Src_Ports (CT_State x9) = False;
is_Src_Ports (Extra x10) = False;

is_Dst_Ports :: forall a. (Len a) => Common_primitive a -> Bool;
is_Dst_Ports (Src x1) = False;
is_Dst_Ports (Dst x2) = False;
is_Dst_Ports (IIface x3) = False;
is_Dst_Ports (OIface x4) = False;
is_Dst_Ports (Prot x5) = False;
is_Dst_Ports (Src_Ports x6) = False;
is_Dst_Ports (Dst_Ports x7) = True;
is_Dst_Ports (L4_Flags x8) = False;
is_Dst_Ports (CT_State x9) = False;
is_Dst_Ports (Extra x10) = False;

andfold_MatchExp :: forall a. [Match_expr a] -> Match_expr a;
andfold_MatchExp [] = MatchAny;
andfold_MatchExp [e] = e;
andfold_MatchExp (e : v : va) = MatchAnd e (andfold_MatchExp (v : va));

import_protocols_from_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Match_expr (Common_primitive a);
import_protocols_from_ports m =
  let {
    (srcpts, rst1) = primitive_extractor (is_Src_Ports, src_ports_sel) m;
    (dstpts, a) = primitive_extractor (is_Dst_Ports, dst_ports_sel) rst1;
  } in MatchAnd
         (MatchAnd
           (MatchAnd
             (andfold_MatchExp
               (map (Match . Prot . (\ (L4Ports proto _) -> Proto proto))
                 (getPos srcpts)))
             (andfold_MatchExp
               (map (Match . Prot . (\ (L4Ports proto _) -> Proto proto))
                 (getPos dstpts))))
           (alist_and
             (negPos_map Src_Ports srcpts ++ negPos_map Dst_Ports dstpts)))
         a;

compress_normalize_protocols ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Maybe (Match_expr (Common_primitive a));
compress_normalize_protocols m =
  compress_normalize_protocols_step (import_protocols_from_ports m);

compress_normalize_besteffort ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Maybe (Match_expr (Common_primitive a));
compress_normalize_besteffort m =
  compress_normalize_primitive_monad
    [compress_normalize_protocols, compress_normalize_input_interfaces,
      compress_normalize_output_interfaces]
    m;

normalize_primitive_extract ::
  forall a b.
    (a -> Bool, a -> b) ->
      (b -> a) -> ([Negation_type b] -> [b]) -> Match_expr a -> [Match_expr a];
normalize_primitive_extract disc_sel c f m =
  let {
    (spts, rst) = primitive_extractor disc_sel m;
  } in map (\ spt -> MatchAnd (Match (c spt)) rst) (f spts);

src_sel :: forall a. (Len a) => Common_primitive a -> Ipt_iprange a;
src_sel (Src x1) = x1;

is_Src :: forall a. (Len a) => Common_primitive a -> Bool;
is_Src (Src x1) = True;
is_Src (Dst x2) = False;
is_Src (IIface x3) = False;
is_Src (OIface x4) = False;
is_Src (Prot x5) = False;
is_Src (Src_Ports x6) = False;
is_Src (Dst_Ports x7) = False;
is_Src (L4_Flags x8) = False;
is_Src (CT_State x9) = False;
is_Src (Extra x10) = False;

l2wi_negation_type_intersect ::
  forall a. (Len a) => [Negation_type (Word a, Word a)] -> Wordinterval a;
l2wi_negation_type_intersect [] = wordinterval_UNIV;
l2wi_negation_type_intersect (Pos (s, e) : ls) =
  wordinterval_intersection (WordInterval s e)
    (l2wi_negation_type_intersect ls);
l2wi_negation_type_intersect (Neg (s, e) : ls) =
  wordinterval_intersection (wordinterval_invert (WordInterval s e))
    (l2wi_negation_type_intersect ls);

ipt_iprange_negation_type_to_br_intersect ::
  forall a. (Len a) => [Negation_type (Ipt_iprange a)] -> Wordinterval a;
ipt_iprange_negation_type_to_br_intersect l =
  l2wi_negation_type_intersect (negPos_map ipt_iprange_to_interval l);

wi_2_cidr_ipt_iprange_list ::
  forall a. (Len a) => Wordinterval a -> [Ipt_iprange a];
wi_2_cidr_ipt_iprange_list r = map (uncurry IpAddrNetmask) (cidr_split r);

ipt_iprange_compress ::
  forall a. (Len a) => [Negation_type (Ipt_iprange a)] -> [Ipt_iprange a];
ipt_iprange_compress =
  wi_2_cidr_ipt_iprange_list . ipt_iprange_negation_type_to_br_intersect;

normalize_src_ips ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_src_ips =
  normalize_primitive_extract (is_Src, src_sel) Src ipt_iprange_compress;

dst_sel :: forall a. (Len a) => Common_primitive a -> Ipt_iprange a;
dst_sel (Dst x2) = x2;

is_Dst :: forall a. (Len a) => Common_primitive a -> Bool;
is_Dst (Src x1) = False;
is_Dst (Dst x2) = True;
is_Dst (IIface x3) = False;
is_Dst (OIface x4) = False;
is_Dst (Prot x5) = False;
is_Dst (Src_Ports x6) = False;
is_Dst (Dst_Ports x7) = False;
is_Dst (L4_Flags x8) = False;
is_Dst (CT_State x9) = False;
is_Dst (Extra x10) = False;

normalize_dst_ips ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_dst_ips =
  normalize_primitive_extract (is_Dst, dst_sel) Dst ipt_iprange_compress;

optimize_matches_option ::
  forall a. (Match_expr a -> Maybe (Match_expr a)) -> [Rule a] -> [Rule a];
optimize_matches_option uu [] = [];
optimize_matches_option f (Rule m a : rs) =
  (case f m of {
    Nothing -> optimize_matches_option f rs;
    Just ma -> Rule ma a : optimize_matches_option f rs;
  });

singletonize_L4Ports :: Ipt_l4_ports -> [Ipt_l4_ports];
singletonize_L4Ports (L4Ports proto pts) = map (\ p -> L4Ports proto [p]) pts;

l4_ports_compress :: [Ipt_l4_ports] -> Match_compress Ipt_l4_ports;
l4_ports_compress [] = MatchesAll;
l4_ports_compress [L4Ports proto ps] =
  MatchExpr (L4Ports proto (wi2l (wordinterval_compress (l2wi ps))));
l4_ports_compress (L4Ports proto1 ps1 : L4Ports proto2 ps2 : pss) =
  (if not (equal_word proto1 proto2) then CannotMatch
    else l4_ports_compress
           (L4Ports proto1
              (wi2l (wordinterval_intersection (l2wi ps1) (l2wi ps2))) :
             pss));

normalize_positive_ports_step ::
  forall a.
    (Len a) => (Common_primitive a -> Bool,
                 Common_primitive a -> Ipt_l4_ports) ->
                 (Ipt_l4_ports -> Common_primitive a) ->
                   Match_expr (Common_primitive a) ->
                     [Match_expr (Common_primitive a)];
normalize_positive_ports_step disc_sel c m =
  let {
    (spts, rst) = primitive_extractor disc_sel m;
    (pspts, []) = (getPos spts, getNeg spts);
  } in (case l4_ports_compress pspts of {
         CannotMatch -> [];
         MatchesAll -> [rst];
         MatchExpr ma ->
           map (\ spt -> MatchAnd (Match (c spt)) rst)
             (singletonize_L4Ports ma);
       });

normalize_positive_src_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_positive_src_ports =
  normalize_positive_ports_step (is_Src_Ports, src_ports_sel) Src_Ports;

rewrite_negated_primitives ::
  forall a b.
    (a -> Bool, a -> b) ->
      (b -> a) ->
        ((b -> a) -> b -> Match_expr a) -> Match_expr a -> Match_expr a;
rewrite_negated_primitives disc_sel c negatea m =
  let {
    (spts, rst) = primitive_extractor disc_sel m;
  } in (if null (getNeg spts) then m
         else MatchAnd (andfold_MatchExp (map (negatea c) (getNeg spts)))
                (MatchAnd (andfold_MatchExp (map (Match . c) (getPos spts)))
                  rst));

l4_ports_negate_one ::
  forall a.
    (Len a) => (Ipt_l4_ports -> Common_primitive a) ->
                 Ipt_l4_ports -> Match_expr (Common_primitive a);
l4_ports_negate_one c (L4Ports proto pts) =
  matchOr (MatchNot (Match (Prot (Proto proto))))
    (Match (c (L4Ports proto (raw_ports_invert pts))));

rewrite_negated_src_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Match_expr (Common_primitive a);
rewrite_negated_src_ports m =
  rewrite_negated_primitives (is_Src_Ports, src_ports_sel) Src_Ports
    l4_ports_negate_one m;

normalize_match :: forall a. Match_expr a -> [Match_expr a];
normalize_match MatchAny = [MatchAny];
normalize_match (Match m) = [Match m];
normalize_match (MatchAnd m1 m2) =
  concatMap (\ x -> map (MatchAnd x) (normalize_match m2)) (normalize_match m1);
normalize_match (MatchNot (MatchAnd m1 m2)) =
  normalize_match (MatchNot m1) ++ normalize_match (MatchNot m2);
normalize_match (MatchNot (MatchNot m)) = normalize_match m;
normalize_match (MatchNot MatchAny) = [];
normalize_match (MatchNot (Match m)) = [MatchNot (Match m)];

normalize_ports_generic ::
  forall a.
    (Len a) => (Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)]) ->
                 (Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a)) ->
                   Match_expr (Common_primitive a) ->
                     [Match_expr (Common_primitive a)];
normalize_ports_generic normalize_pos rewrite_neg m =
  concatMap normalize_pos (normalize_match (rewrite_neg m));

normalize_src_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_src_ports m =
  normalize_ports_generic normalize_positive_src_ports rewrite_negated_src_ports
    m;

normalize_positive_dst_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_positive_dst_ports =
  normalize_positive_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports;

rewrite_negated_dst_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Match_expr (Common_primitive a);
rewrite_negated_dst_ports m =
  rewrite_negated_primitives (is_Dst_Ports, dst_ports_sel) Dst_Ports
    l4_ports_negate_one m;

normalize_dst_ports ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 [Match_expr (Common_primitive a)];
normalize_dst_ports m =
  normalize_ports_generic normalize_positive_dst_ports rewrite_negated_dst_ports
    m;

normalize_rules ::
  forall a. (Match_expr a -> [Match_expr a]) -> [Rule a] -> [Rule a];
normalize_rules uu [] = [];
normalize_rules f (Rule m a : rs) =
  map (\ ma -> Rule ma a) (f m) ++ normalize_rules f rs;

transform_normalize_primitives ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
transform_normalize_primitives =
  (((optimize_matches_option compress_normalize_besteffort .
      normalize_rules normalize_dst_ips) .
     normalize_rules normalize_src_ips) .
    normalize_rules normalize_dst_ports) .
    normalize_rules normalize_src_ports;

ctstate_is_UNIV :: Set Ctstate -> Bool;
ctstate_is_UNIV c =
  member CT_New c &&
    member CT_Established c &&
      member CT_Related c && member CT_Untracked c && member CT_Invalid c;

optimize_primitive_univ ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Match_expr (Common_primitive a);
optimize_primitive_univ (Match (IIface iface)) =
  (if equal_iface iface ifaceAny then MatchAny else Match (IIface iface));
optimize_primitive_univ (Match (OIface iface)) =
  (if equal_iface iface ifaceAny then MatchAny else Match (OIface iface));
optimize_primitive_univ (Match (Prot ProtoAny)) = MatchAny;
optimize_primitive_univ (Match (L4_Flags (TCP_Flags m c))) =
  (if equal_set m bot_set && equal_set c bot_set then MatchAny
    else Match (L4_Flags (TCP_Flags m c)));
optimize_primitive_univ (Match (CT_State ctstate)) =
  (if ctstate_is_UNIV ctstate then MatchAny else Match (CT_State ctstate));
optimize_primitive_univ (Match (Src (IpAddr va))) = Match (Src (IpAddr va));
optimize_primitive_univ (Match (Src (IpAddrRange va vb))) =
  Match (Src (IpAddrRange va vb));
optimize_primitive_univ (Match (Dst (IpAddr va))) = Match (Dst (IpAddr va));
optimize_primitive_univ (Match (Dst (IpAddrRange va vb))) =
  Match (Dst (IpAddrRange va vb));
optimize_primitive_univ (Match (Prot (Proto va))) = Match (Prot (Proto va));
optimize_primitive_univ (Match (Src_Ports v)) = Match (Src_Ports v);
optimize_primitive_univ (Match (Dst_Ports v)) = Match (Dst_Ports v);
optimize_primitive_univ (Match (Extra v)) = Match (Extra v);
optimize_primitive_univ (MatchNot m) = MatchNot (optimize_primitive_univ m);
optimize_primitive_univ (MatchAnd m1 m2) =
  MatchAnd (optimize_primitive_univ m1) (optimize_primitive_univ m2);
optimize_primitive_univ MatchAny = MatchAny;
optimize_primitive_univ (Match (Src (IpAddrNetmask uu vc))) =
  (if equal_nat vc zero_nat then MatchAny
    else Match (Src (IpAddrNetmask uu (suc (minus_nat vc one_nat)))));
optimize_primitive_univ (Match (Dst (IpAddrNetmask uv vc))) =
  (if equal_nat vc zero_nat then MatchAny
    else Match (Dst (IpAddrNetmask uv (suc (minus_nat vc one_nat)))));

opt_MatchAny_match_expr_once :: forall a. Match_expr a -> Match_expr a;
opt_MatchAny_match_expr_once MatchAny = MatchAny;
opt_MatchAny_match_expr_once (Match a) = Match a;
opt_MatchAny_match_expr_once (MatchNot (MatchNot m)) =
  opt_MatchAny_match_expr_once m;
opt_MatchAny_match_expr_once (MatchNot (Match v)) =
  MatchNot (opt_MatchAny_match_expr_once (Match v));
opt_MatchAny_match_expr_once (MatchNot (MatchAnd v va)) =
  MatchNot (opt_MatchAny_match_expr_once (MatchAnd v va));
opt_MatchAny_match_expr_once (MatchNot MatchAny) =
  MatchNot (opt_MatchAny_match_expr_once MatchAny);
opt_MatchAny_match_expr_once (MatchAnd MatchAny MatchAny) = MatchAny;
opt_MatchAny_match_expr_once (MatchAnd MatchAny (Match v)) =
  opt_MatchAny_match_expr_once (Match v);
opt_MatchAny_match_expr_once (MatchAnd MatchAny (MatchNot v)) =
  opt_MatchAny_match_expr_once (MatchNot v);
opt_MatchAny_match_expr_once (MatchAnd MatchAny (MatchAnd v va)) =
  opt_MatchAny_match_expr_once (MatchAnd v va);
opt_MatchAny_match_expr_once (MatchAnd (Match v) MatchAny) =
  opt_MatchAny_match_expr_once (Match v);
opt_MatchAny_match_expr_once (MatchAnd (MatchNot v) MatchAny) =
  opt_MatchAny_match_expr_once (MatchNot v);
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) MatchAny) =
  opt_MatchAny_match_expr_once (MatchAnd v va);
opt_MatchAny_match_expr_once (MatchAnd (Match v) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once (MatchAnd (MatchNot v) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once (MatchAnd (MatchNot MatchAny) (Match v)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot MatchAny) (MatchNot (Match va))) = MatchNot MatchAny;
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot MatchAny) (MatchNot (MatchNot va))) = MatchNot MatchAny;
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot MatchAny) (MatchNot (MatchAnd va vb))) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once (MatchAnd (MatchNot MatchAny) (MatchAnd v va)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr_once (MatchAnd (Match v) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr_once (Match v))
    (opt_MatchAny_match_expr_once (Match va));
opt_MatchAny_match_expr_once (MatchAnd (Match v) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (Match v))
    (opt_MatchAny_match_expr_once (MatchNot (Match vb)));
opt_MatchAny_match_expr_once (MatchAnd (Match v) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (Match v))
    (opt_MatchAny_match_expr_once (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr_once (MatchAnd (Match v) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr_once (Match v))
    (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr_once (MatchAnd (Match v) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr_once (Match v))
    (opt_MatchAny_match_expr_once (MatchAnd va vb));
opt_MatchAny_match_expr_once (MatchAnd (MatchNot (Match vb)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (Match vb)))
    (opt_MatchAny_match_expr_once (Match va));
opt_MatchAny_match_expr_once (MatchAnd (MatchNot (MatchNot vb)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchNot vb)))
    (opt_MatchAny_match_expr_once (Match va));
opt_MatchAny_match_expr_once (MatchAnd (MatchNot (MatchAnd vb vc)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vb vc)))
    (opt_MatchAny_match_expr_once (Match va));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (Match va)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (Match va)))
    (opt_MatchAny_match_expr_once (MatchNot (Match vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr_once (MatchNot (Match vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchAnd va vc)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchAnd va vc)))
    (opt_MatchAny_match_expr_once (MatchNot (Match vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (Match va)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (Match va)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchAnd va vc)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchAnd va vc)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (Match va)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (Match va)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchAnd va vd)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchAnd va vd)))
    (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr_once (MatchAnd (MatchNot (Match vc)) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (Match vc)))
    (opt_MatchAny_match_expr_once (MatchAnd va vb));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchNot vc)) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchNot vc)))
    (opt_MatchAny_match_expr_once (MatchAnd va vb));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchNot (MatchAnd vc vd)) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vc vd)))
    (opt_MatchAny_match_expr_once (MatchAnd va vb));
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) (Match vb)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchAnd v va))
    (opt_MatchAny_match_expr_once (Match vb));
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) (MatchNot (Match vc))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchAnd v va))
    (opt_MatchAny_match_expr_once (MatchNot (Match vc)));
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) (MatchNot (MatchNot vc)))
  = MatchAnd (opt_MatchAny_match_expr_once (MatchAnd v va))
      (opt_MatchAny_match_expr_once (MatchNot (MatchNot vc)));
opt_MatchAny_match_expr_once
  (MatchAnd (MatchAnd v va) (MatchNot (MatchAnd vc vd))) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchAnd v va))
    (opt_MatchAny_match_expr_once (MatchNot (MatchAnd vc vd)));
opt_MatchAny_match_expr_once (MatchAnd (MatchAnd v va) (MatchAnd vb vc)) =
  MatchAnd (opt_MatchAny_match_expr_once (MatchAnd v va))
    (opt_MatchAny_match_expr_once (MatchAnd vb vc));

repeat_stabilize :: forall a. (Eq a) => Nat -> (a -> a) -> a -> a;
repeat_stabilize n uu v =
  (if equal_nat n zero_nat then v
    else let {
           v_new = uu v;
         } in (if v == v_new then v
                else repeat_stabilize (minus_nat n one_nat) uu v_new));

opt_MatchAny_match_expr :: forall a. (Eq a) => Match_expr a -> Match_expr a;
opt_MatchAny_match_expr m =
  repeat_stabilize (nat_of_integer (2 :: Integer)) opt_MatchAny_match_expr_once
    m;

normalize_rules_dnf :: forall a. [Rule a] -> [Rule a];
normalize_rules_dnf [] = [];
normalize_rules_dnf (Rule m a : rs) =
  map (\ ma -> Rule ma a) (normalize_match m) ++ normalize_rules_dnf rs;

cut_off_after_match_any :: forall a. (Eq a) => [Rule a] -> [Rule a];
cut_off_after_match_any [] = [];
cut_off_after_match_any (Rule m a : rs) =
  (if equal_match_expr m MatchAny &&
        (equal_action a Accept ||
          (equal_action a Drop || equal_action a Reject))
    then [Rule m a] else Rule m a : cut_off_after_match_any rs);

matcheq_matchNone :: forall a. Match_expr a -> Bool;
matcheq_matchNone MatchAny = False;
matcheq_matchNone (Match uu) = False;
matcheq_matchNone (MatchNot MatchAny) = True;
matcheq_matchNone (MatchNot (Match uv)) = False;
matcheq_matchNone (MatchNot (MatchNot m)) = matcheq_matchNone m;
matcheq_matchNone (MatchNot (MatchAnd m1 m2)) =
  matcheq_matchNone (MatchNot m1) && matcheq_matchNone (MatchNot m2);
matcheq_matchNone (MatchAnd m1 m2) =
  matcheq_matchNone m1 || matcheq_matchNone m2;

optimize_matches ::
  forall a. (Match_expr a -> Match_expr a) -> [Rule a] -> [Rule a];
optimize_matches f rs =
  optimize_matches_option
    (\ m -> (if matcheq_matchNone (f m) then Nothing else Just (f m))) rs;

transform_optimize_dnf_strict ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
transform_optimize_dnf_strict =
  cut_off_after_match_any .
    (optimize_matches opt_MatchAny_match_expr . normalize_rules_dnf) .
      optimize_matches (opt_MatchAny_match_expr . optimize_primitive_univ);

get_action :: forall a. Rule a -> Action;
get_action (Rule x1 x2) = x2;

get_match :: forall a. Rule a -> Match_expr a;
get_match (Rule x1 x2) = x1;

optimize_matches_a ::
  forall a. (Action -> Match_expr a -> Match_expr a) -> [Rule a] -> [Rule a];
optimize_matches_a f rs =
  map (\ r -> Rule (f (get_action r) (get_match r)) (get_action r)) rs;

remdups_rev_code :: forall a. (Eq a) => [a] -> [a] -> [a];
remdups_rev_code uu [] = [];
remdups_rev_code ps (r : rs) =
  (if membera ps r then remdups_rev_code ps rs
    else r : remdups_rev_code (r : ps) rs);

upper_closure ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
upper_closure rs =
  remdups_rev_code []
    (transform_optimize_dnf_strict
      (transform_normalize_primitives
        (transform_optimize_dnf_strict
          (optimize_matches_a upper_closure_matchexpr rs))));

word_to_nat :: forall a. (Len a) => Word a -> Nat;
word_to_nat = unat;

match_sel :: forall a. Simple_rule a -> Simple_match_ext a ();
match_sel (SimpleRule x1 x2) = x1;

simple_conn_matches ::
  forall a. (Len a) => Simple_match_ext a () -> Parts_connection_ext () -> Bool;
simple_conn_matches m c =
  match_iface (iiface m) (pc_iiface c) &&
    match_iface (oiface m) (pc_oiface c) &&
      match_proto (proto m) (pc_proto c) &&
        simple_match_port (sports m) (pc_sport c) &&
          simple_match_port (dports m) (pc_dport c);

groupWIs2 ::
  forall a.
    (Len a) => Parts_connection_ext () -> [Simple_rule a] -> [[Wordinterval a]];
groupWIs2 c rs =
  let {
    p = getParts rs;
    w = map getOneIp p;
    filterW = filter (\ r -> simple_conn_matches (match_sel r) c) rs;
    f = (\ wi ->
          (map (\ d -> runFw (getOneIp wi) d c filterW) w,
            map (\ s -> runFw s (getOneIp wi) c filterW) w));
  } in map (map fst) (groupF snd (map (\ x -> (x, f x)) p));

wordinterval_element :: forall a. (Len0 a) => Word a -> Wordinterval a -> Bool;
wordinterval_element el (WordInterval s e) =
  less_eq_word s el && less_eq_word el e;
wordinterval_element el (RangeUnion r1 r2) =
  wordinterval_element el r1 || wordinterval_element el r2;

matching_srcs ::
  forall a.
    (Len a) => Word a -> [Simple_rule a] -> Wordinterval a -> Wordinterval a;
matching_srcs uu [] uv = empty_WordInterval;
matching_srcs d (SimpleRule m Accepta : rs) acc_dropped =
  (if simple_match_ip (dst m) d
    then wordinterval_union
           (wordinterval_setminus (ipcidr_tuple_to_wordinterval (src m))
             acc_dropped)
           (matching_srcs d rs acc_dropped)
    else matching_srcs d rs acc_dropped);
matching_srcs d (SimpleRule m Dropa : rs) acc_dropped =
  (if simple_match_ip (dst m) d
    then matching_srcs d rs
           (wordinterval_union (ipcidr_tuple_to_wordinterval (src m))
             acc_dropped)
    else matching_srcs d rs acc_dropped);

matching_dsts ::
  forall a.
    (Len a) => Word a -> [Simple_rule a] -> Wordinterval a -> Wordinterval a;
matching_dsts uu [] uv = empty_WordInterval;
matching_dsts s (SimpleRule m Accepta : rs) acc_dropped =
  (if simple_match_ip (src m) s
    then wordinterval_union
           (wordinterval_setminus (ipcidr_tuple_to_wordinterval (dst m))
             acc_dropped)
           (matching_dsts s rs acc_dropped)
    else matching_dsts s rs acc_dropped);
matching_dsts s (SimpleRule m Dropa : rs) acc_dropped =
  (if simple_match_ip (src m) s
    then matching_dsts s rs
           (wordinterval_union (ipcidr_tuple_to_wordinterval (dst m))
             acc_dropped)
    else matching_dsts s rs acc_dropped);

groupWIs3_default_policy ::
  forall a.
    (Len a) => Parts_connection_ext () -> [Simple_rule a] -> [[Wordinterval a]];
groupWIs3_default_policy c rs =
  let {
    p = getParts rs;
    w = map getOneIp p;
    filterW = filter (\ r -> simple_conn_matches (match_sel r) c) rs;
    f = (\ wi ->
          let {
            mtch_dsts = matching_dsts (getOneIp wi) filterW empty_WordInterval;
            mtch_srcs = matching_srcs (getOneIp wi) filterW empty_WordInterval;
          } in (map (\ d -> wordinterval_element d mtch_dsts) w,
                 map (\ s -> wordinterval_element s mtch_srcs) w));
  } in map (map fst) (groupF snd (map (\ x -> (x, f x)) p));

equal_simple_match_ext ::
  forall a b.
    (Len a, Eq b) => Simple_match_ext a b -> Simple_match_ext a b -> Bool;
equal_simple_match_ext
  (Simple_match_ext iifacea oifacea srca dsta protoa sportsa dportsa morea)
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  equal_iface iifacea iiface &&
    equal_iface oifacea oiface &&
      srca == src &&
        dsta == dst &&
          equal_protocol protoa proto &&
            sportsa == sports && dportsa == dports && morea == more;

simple_match_any :: forall a. (Len a) => Simple_match_ext a ();
simple_match_any =
  Simple_match_ext ifaceAny ifaceAny (zero_worda, zero_nat)
    (zero_worda, zero_nat) ProtoAny
    (zero_worda, word_of_int (Int_of_integer (65535 :: Integer)))
    (zero_worda, word_of_int (Int_of_integer (65535 :: Integer))) ();

has_default_policy :: forall a. (Len a) => [Simple_rule a] -> Bool;
has_default_policy [] = False;
has_default_policy [SimpleRule m uu] =
  equal_simple_match_ext m simple_match_any;
has_default_policy (uv : v : va) = has_default_policy (v : va);

groupWIs3 ::
  forall a.
    (Len a) => Parts_connection_ext () -> [Simple_rule a] -> [[Wordinterval a]];
groupWIs3 c rs =
  (if has_default_policy rs then groupWIs3_default_policy c rs
    else groupWIs2 c rs);

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

word_less_eq :: forall a. (Len a) => Word a -> Word a -> Bool;
word_less_eq a b = less_eq_word a b;

rw_Reject :: forall a. [Rule a] -> [Rule a];
rw_Reject [] = [];
rw_Reject (Rule m Reject : rs) = Rule m Drop : rw_Reject rs;
rw_Reject (Rule v Accept : rs) = Rule v Accept : rw_Reject rs;
rw_Reject (Rule v Drop : rs) = Rule v Drop : rw_Reject rs;
rw_Reject (Rule v Log : rs) = Rule v Log : rw_Reject rs;
rw_Reject (Rule v (Call vb) : rs) = Rule v (Call vb) : rw_Reject rs;
rw_Reject (Rule v Return : rs) = Rule v Return : rw_Reject rs;
rw_Reject (Rule v (Goto vb) : rs) = Rule v (Goto vb) : rw_Reject rs;
rw_Reject (Rule v Empty : rs) = Rule v Empty : rw_Reject rs;
rw_Reject (Rule v Unknown : rs) = Rule v Unknown : rw_Reject rs;

shiftr_word :: forall a. (Len0 a) => Word a -> Nat -> Word a;
shiftr_word w n = funpow n shiftr1 w;

int_to_ipv6preferred ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) -> Ipv6addr_syntax;
int_to_ipv6preferred i =
  IPv6AddrPreferred
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int
            (Int_of_integer
              (340277174624079928635746076935438991360 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (7 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int
            (Int_of_integer (5192217630372313364192902785269760 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (6 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int
            (Int_of_integer (79226953588444722964369244160 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (5 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int (Int_of_integer (1208907372870555465154560 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (4 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int (Int_of_integer (18446462598732840960 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (3 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i
          (word_of_int (Int_of_integer (281470681743360 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (2 :: Integer)))))
    (ucast
      (shiftr_word
        (bitAND_word i (word_of_int (Int_of_integer (4294901760 :: Integer))))
        (times_nat (nat_of_integer (16 :: Integer)) one_nat)))
    (ucast (bitAND_word i (word_of_int (Int_of_integer (65535 :: Integer)))));

ipv6preferred_to_int ::
  Ipv6addr_syntax -> Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))));
ipv6preferred_to_int (IPv6AddrPreferred a b c d e f g h) =
  bitOR_word
    (shiftl_word (ucast a)
      (times_nat (nat_of_integer (16 :: Integer))
        (nat_of_integer (7 :: Integer))))
    (bitOR_word
      (shiftl_word (ucast b)
        (times_nat (nat_of_integer (16 :: Integer))
          (nat_of_integer (6 :: Integer))))
      (bitOR_word
        (shiftl_word (ucast c)
          (times_nat (nat_of_integer (16 :: Integer))
            (nat_of_integer (5 :: Integer))))
        (bitOR_word
          (shiftl_word (ucast d)
            (times_nat (nat_of_integer (16 :: Integer))
              (nat_of_integer (4 :: Integer))))
          (bitOR_word
            (shiftl_word (ucast e)
              (times_nat (nat_of_integer (16 :: Integer))
                (nat_of_integer (3 :: Integer))))
            (bitOR_word
              (shiftl_word (ucast f)
                (times_nat (nat_of_integer (16 :: Integer))
                  (nat_of_integer (2 :: Integer))))
              (bitOR_word
                (shiftl_word (ucast g)
                  (times_nat (nat_of_integer (16 :: Integer)) one_nat))
                (shiftl_word (ucast h)
                  (times_nat (nat_of_integer (16 :: Integer)) zero_nat))))))));

string_of_nat :: Nat -> [Prelude.Char];
string_of_nat n =
  (if less_nat n (nat_of_integer (10 :: Integer))
    then [char_of_nat (plus_nat (nat_of_integer (48 :: Integer)) n)]
    else string_of_nat (divide_nat n (nat_of_integer (10 :: Integer))) ++
           [char_of_nat
              (plus_nat (nat_of_integer (48 :: Integer))
                (mod_nat n (nat_of_integer (10 :: Integer))))]);

dotteddecimal_toString :: (Nat, (Nat, (Nat, Nat))) -> [Prelude.Char];
dotteddecimal_toString (a, (b, (c, d))) =
  string_of_nat a ++
    "." ++ string_of_nat b ++ "." ++ string_of_nat c ++ "." ++ string_of_nat d;

dotdecimal_of_ipv4addr ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> (Nat, (Nat, (Nat, Nat)));
dotdecimal_of_ipv4addr a =
  (nat_of_ipv4addr
     (bitAND_word (shiftr_word a (nat_of_integer (24 :: Integer)))
       (word_of_int (Int_of_integer (255 :: Integer)))),
    (nat_of_ipv4addr
       (bitAND_word (shiftr_word a (nat_of_integer (16 :: Integer)))
         (word_of_int (Int_of_integer (255 :: Integer)))),
      (nat_of_ipv4addr
         (bitAND_word (shiftr_word a (nat_of_integer (8 :: Integer)))
           (word_of_int (Int_of_integer (255 :: Integer)))),
        nat_of_ipv4addr
          (bitAND_word a (word_of_int (Int_of_integer (255 :: Integer)))))));

ipv4addr_toString ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
ipv4addr_toString ip = dotteddecimal_toString (dotdecimal_of_ipv4addr ip);

ipv4addr_wordinterval_toString ::
  Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
ipv4addr_wordinterval_toString (WordInterval s e) =
  (if equal_word s e then ipv4addr_toString s
    else "{" ++ ipv4addr_toString s ++ " .. " ++ ipv4addr_toString e ++ "}");
ipv4addr_wordinterval_toString (RangeUnion a b) =
  ipv4addr_wordinterval_toString a ++ " u " ++ ipv4addr_wordinterval_toString b;

wordinterval_eq ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Bool;
wordinterval_eq r1 r2 = wordinterval_subset r1 r2 && wordinterval_subset r2 r1;

ipassmt_ignore_wildcard_list ::
  forall a. (Len a) => [(Iface, [(Word a, Nat)])] -> [(Iface, [(Word a, Nat)])];
ipassmt_ignore_wildcard_list ipassmt =
  filter
    (\ (_, ips) ->
      not (wordinterval_eq (l2wi (map ipcidr_to_interval ips))
            wordinterval_UNIV))
    ipassmt;

list_separated_toString ::
  forall a. [Prelude.Char] -> (a -> [Prelude.Char]) -> [a] -> [Prelude.Char];
list_separated_toString sep toStr ls =
  concat
    (splice (map toStr ls) (replicate (minus_nat (size_list ls) one_nat) sep));

list_toString :: forall a. (a -> [Prelude.Char]) -> [a] -> [Prelude.Char];
list_toString toStr ls = "[" ++ list_separated_toString ", " toStr ls ++ "]";

ipassmt_sanity_defined ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] ->
                 (Iface -> Maybe [(Word a, Nat)]) -> Bool;
ipassmt_sanity_defined rs ipassmt =
  all (\ iface -> not (is_none (ipassmt iface))) (collect_ifaces rs);

debug_ipassmt_generic ::
  forall a.
    (Len a) => (Wordinterval a -> [Prelude.Char]) ->
                 [(Iface, [(Word a, Nat)])] ->
                   [Rule (Common_primitive a)] -> [[Prelude.Char]];
debug_ipassmt_generic toStr ipassmt rs =
  let {
    ifaces = map fst ipassmt;
  } in ["distinct: " ++ (if distinct ifaces then "passed" else "FAIL!"),
         "ipassmt_sanity_nowildcards: " ++
           (if ball (image fst (Set ipassmt))
                 (\ iface -> not (iface_is_wildcard iface))
             then "passed"
             else "fail: " ++
                    list_toString iface_sel (filter iface_is_wildcard ifaces)),
         "ipassmt_sanity_defined (interfaces defined in the ruleset are also in ipassmt): " ++
           (if ipassmt_sanity_defined rs (map_of ipassmt) then "passed"
             else "fail: " ++
                    list_toString iface_sel
                      (filter (\ i -> not (membera ifaces i))
                        (collect_ifaces rs))),
         "ipassmt_sanity_disjoint (no zone-spanning interfaces): " ++
           (if let {
                 is = image fst (Set ipassmt);
               } in ball is
                      (\ i1 ->
                        ball is
                          (\ i2 ->
                            (if not (equal_iface i1 i2)
                              then wordinterval_empty
                                     (wordinterval_intersection
                                       (l2wi
 (map ipcidr_to_interval (the (map_of ipassmt i1))))
                                       (l2wi
 (map ipcidr_to_interval (the (map_of ipassmt i2)))))
                              else True)))
             then "passed"
             else "fail: " ++
                    list_toString
                      (\ (i1, i2) ->
                        "(" ++ iface_sel i1 ++ "," ++ iface_sel i2 ++ ")")
                      (filter
                        (\ (i1, i2) ->
                          not (equal_iface i1 i2) &&
                            not (wordinterval_empty
                                  (wordinterval_intersection
                                    (l2wi (map ipcidr_to_interval
    (the (map_of ipassmt i1))))
                                    (l2wi (map ipcidr_to_interval
    (the (map_of ipassmt i2)))))))
                        (product ifaces ifaces))),
         "ipassmt_sanity_disjoint excluding UNIV interfaces: " ++
           let {
             ipassmta = ipassmt_ignore_wildcard_list ipassmt;
             ifacesa = map fst ipassmta;
           } in (if let {
                      is = image fst (Set ipassmta);
                    } in ball is
                           (\ i1 ->
                             ball is
                               (\ i2 ->
                                 (if not (equal_iface i1 i2)
                                   then wordinterval_empty
  (wordinterval_intersection
    (l2wi (map ipcidr_to_interval (the (map_of ipassmta i1))))
    (l2wi (map ipcidr_to_interval (the (map_of ipassmta i2)))))
                                   else True)))
                  then "passed"
                  else "fail: " ++
                         list_toString
                           (\ (i1, i2) ->
                             "(" ++ iface_sel i1 ++ "," ++ iface_sel i2 ++ ")")
                           (filter
                             (\ (i1, i2) ->
                               not (equal_iface i1 i2) &&
                                 not (wordinterval_empty
                                       (wordinterval_intersection
 (l2wi (map ipcidr_to_interval (the (map_of ipassmta i1))))
 (l2wi (map ipcidr_to_interval (the (map_of ipassmta i2)))))))
                             (product ifacesa ifacesa))),
         "ipassmt_sanity_complete: " ++
           (if distinct (map fst ipassmt) &&
                 let {
                   range = map snd ipassmt;
                 } in wordinterval_eq
                        (wordinterval_Union
                          (map (l2wi . map ipcidr_to_interval) range))
                        wordinterval_UNIV
             then "passed"
             else "the following is not covered: " ++
                    toStr (wordinterval_setminus wordinterval_UNIV
                            (wordinterval_Union
                              (map (l2wi . map ipcidr_to_interval)
                                (map snd ipassmt))))),
         "ipassmt_sanity_complete excluding UNIV interfaces: " ++
           let {
             ipassmta = ipassmt_ignore_wildcard_list ipassmt;
           } in (if distinct (map fst ipassmta) &&
                      let {
                        range = map snd ipassmta;
                      } in wordinterval_eq
                             (wordinterval_Union
                               (map (l2wi . map ipcidr_to_interval) range))
                             wordinterval_UNIV
                  then "passed"
                  else "the following is not covered: " ++
                         toStr (wordinterval_setminus wordinterval_UNIV
                                 (wordinterval_Union
                                   (map (l2wi . map ipcidr_to_interval)
                                     (map snd ipassmta)))))];

debug_ipassmt_ipv4 ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    [Rule (Common_primitive (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))] ->
      [[Prelude.Char]];
debug_ipassmt_ipv4 = debug_ipassmt_generic ipv4addr_wordinterval_toString;

string_of_word_single :: forall a. (Len a) => Bool -> Word a -> [Prelude.Char];
string_of_word_single lc w =
  (if less_word w (word_of_int (Int_of_integer (10 :: Integer)))
    then [char_of_nat (plus_nat (nat_of_integer (48 :: Integer)) (unat w))]
    else (if less_word w (word_of_int (Int_of_integer (36 :: Integer)))
           then [char_of_nat
                   (plus_nat
                     (if lc then nat_of_integer (87 :: Integer)
                       else nat_of_integer (55 :: Integer))
                     (unat w))]
           else error "undefined"));

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

divide_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
divide_word a b = word_of_int (divide_int (uint a) (uint b));

mod_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
mod_word a b = word_of_int (mod_int (uint a) (uint b));

string_of_word ::
  forall a. (Len a) => Bool -> Word a -> Nat -> Word a -> [Prelude.Char];
string_of_word lc base ml w =
  (if less_word base (word_of_int (Int_of_integer (2 :: Integer))) ||
        less_nat ((len_of :: Itself a -> Nat) Type)
          (nat_of_integer (2 :: Integer))
    then error "undefined"
    else (if less_word w base && equal_nat ml zero_nat
           then string_of_word_single lc w
           else string_of_word lc base (minus_nat ml one_nat)
                  (divide_word w base) ++
                  string_of_word_single lc (mod_word w base)));

hex_string_of_word :: forall a. (Len a) => Nat -> Word a -> [Prelude.Char];
hex_string_of_word l =
  string_of_word True (word_of_int (Int_of_integer (16 :: Integer))) l;

hex_string_of_word0 :: forall a. (Len a) => Word a -> [Prelude.Char];
hex_string_of_word0 = hex_string_of_word zero_nat;

ipv6_preferred_to_compressed ::
  Ipv6addr_syntax -> [Maybe (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
ipv6_preferred_to_compressed (IPv6AddrPreferred a b c d e f g h) =
  let {
    lss = goup_by_zeros [a, b, c, d, e, f, g, h];
    max_zero_seq = foldr (\ xs -> max (size_list xs)) lss zero_nat;
    aa = (if less_nat one_nat max_zero_seq
           then list_replace1 (replicate max_zero_seq zero_worda) [] lss
           else lss);
  } in list_explode aa;

ipv6addr_toString ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) -> [Prelude.Char];
ipv6addr_toString ip =
  let {
    partslist = ipv6_preferred_to_compressed (int_to_ipv6preferred ip);
    fix_start = (\ ps -> (case ps of {
                           [] -> ps;
                           Nothing : _ -> Nothing : ps;
                           Just _ : _ -> ps;
                         }));
    fix_end = (\ ps -> (case reverse ps of {
                         [] -> ps;
                         Nothing : _ -> ps ++ [Nothing];
                         Just _ : _ -> ps;
                       }));
  } in list_separated_toString ":" (\ a -> (case a of {
     Nothing -> [];
     Just aa -> hex_string_of_word0 aa;
   }))
         ((fix_end . fix_start) partslist);

ipv6addr_wordinterval_toString ::
  Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) ->
    [Prelude.Char];
ipv6addr_wordinterval_toString (WordInterval s e) =
  (if equal_word s e then ipv6addr_toString s
    else "{" ++ ipv6addr_toString s ++ " .. " ++ ipv6addr_toString e ++ "}");
ipv6addr_wordinterval_toString (RangeUnion a b) =
  ipv6addr_wordinterval_toString a ++ " u " ++ ipv6addr_wordinterval_toString b;

debug_ipassmt_ipv6 ::
  [(Iface,
     [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))), Nat)])] ->
    [Rule (Common_primitive
            (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))))] ->
      [[Prelude.Char]];
debug_ipassmt_ipv6 = debug_ipassmt_generic ipv6addr_wordinterval_toString;

get_exists_matching_src_ips_executable ::
  forall a.
    (Len a) => Iface -> Match_expr (Common_primitive a) -> Wordinterval a;
get_exists_matching_src_ips_executable iface m =
  let {
    (i_matches, _) = primitive_extractor (is_Iiface, iiface_sel) m;
  } in (if all (\ a -> (case a of {
                         Pos i -> match_iface i (iface_sel iface);
                         Neg i -> not (match_iface i (iface_sel iface));
                       }))
             i_matches
         then let {
                (ip_matches, _) = primitive_extractor (is_Src, src_sel) m;
              } in (if null ip_matches then wordinterval_UNIV
                     else l2wi_negation_type_intersect
                            (negPos_map ipt_iprange_to_interval ip_matches))
         else empty_WordInterval);

matcheq_matchAny :: forall a. Match_expr a -> Bool;
matcheq_matchAny MatchAny = True;
matcheq_matchAny (MatchNot m) = not (matcheq_matchAny m);
matcheq_matchAny (MatchAnd m1 m2) = matcheq_matchAny m1 && matcheq_matchAny m2;
matcheq_matchAny (Match uu) = error "undefined";

has_primitive :: forall a. Match_expr a -> Bool;
has_primitive MatchAny = False;
has_primitive (Match a) = True;
has_primitive (MatchNot m) = has_primitive m;
has_primitive (MatchAnd m1 m2) = has_primitive m1 || has_primitive m2;

get_all_matching_src_ips_executable ::
  forall a.
    (Len a) => Iface -> Match_expr (Common_primitive a) -> Wordinterval a;
get_all_matching_src_ips_executable iface m =
  let {
    (i_matches, rest1) = primitive_extractor (is_Iiface, iiface_sel) m;
  } in (if all (\ a -> (case a of {
                         Pos i -> match_iface i (iface_sel iface);
                         Neg i -> not (match_iface i (iface_sel iface));
                       }))
             i_matches
         then let {
                (ip_matches, rest2) =
                  primitive_extractor (is_Src, src_sel) rest1;
              } in (if not (has_primitive rest2) && matcheq_matchAny rest2
                     then (if null ip_matches then wordinterval_UNIV
                            else l2wi_negation_type_intersect
                                   (negPos_map ipt_iprange_to_interval
                                     ip_matches))
                     else empty_WordInterval)
         else empty_WordInterval);

no_spoofing_algorithm_executable ::
  forall a.
    (Len a) => Iface ->
                 (Iface -> Maybe [(Word a, Nat)]) ->
                   [Rule (Common_primitive a)] ->
                     Wordinterval a -> Wordinterval a -> Bool;
no_spoofing_algorithm_executable iface ipassmt [] allowed denied1 =
  wordinterval_subset (wordinterval_setminus allowed denied1)
    (l2wi (map ipcidr_to_interval (the (ipassmt iface))));
no_spoofing_algorithm_executable iface ipassmt (Rule m Accept : rs) allowed
  denied1 =
  no_spoofing_algorithm_executable iface ipassmt rs
    (wordinterval_union allowed
      (get_exists_matching_src_ips_executable iface m))
    denied1;
no_spoofing_algorithm_executable iface ipassmt (Rule m Drop : rs) allowed
  denied1 =
  no_spoofing_algorithm_executable iface ipassmt rs allowed
    (wordinterval_union denied1
      (wordinterval_setminus (get_all_matching_src_ips_executable iface m)
        allowed));
no_spoofing_algorithm_executable uu uv (Rule vb Log : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb Reject : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb (Call vd) : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb Return : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb (Goto vd) : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb Empty : va) ux uy =
  error "undefined";
no_spoofing_algorithm_executable uu uv (Rule vb Unknown : va) ux uy =
  error "undefined";

no_spoofing_iface ::
  forall a.
    (Len a) => Iface ->
                 (Iface -> Maybe [(Word a, Nat)]) ->
                   [Rule (Common_primitive a)] -> Bool;
no_spoofing_iface iface ipassmt rs =
  no_spoofing_algorithm_executable iface ipassmt rs empty_WordInterval
    empty_WordInterval;

is_pos_Extra :: forall a. (Len a) => Negation_type (Common_primitive a) -> Bool;
is_pos_Extra a = (case a of {
                   Pos (Src _) -> False;
                   Pos (Dst _) -> False;
                   Pos (IIface _) -> False;
                   Pos (OIface _) -> False;
                   Pos (Prot _) -> False;
                   Pos (Src_Ports _) -> False;
                   Pos (Dst_Ports _) -> False;
                   Pos (L4_Flags _) -> False;
                   Pos (CT_State _) -> False;
                   Pos (Extra _) -> True;
                   Neg _ -> False;
                 });

nat_to_8word :: Nat -> Word (Bit0 (Bit0 (Bit0 Num1)));
nat_to_8word i = of_nat i;

mk_L4Ports_pre ::
  [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
     Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
    Ipt_l4_ports;
mk_L4Ports_pre ports_raw = L4Ports zero_worda ports_raw;

rm_LogEmpty :: forall a. [Rule a] -> [Rule a];
rm_LogEmpty [] = [];
rm_LogEmpty (Rule uu Empty : rs) = rm_LogEmpty rs;
rm_LogEmpty (Rule uv Log : rs) = rm_LogEmpty rs;
rm_LogEmpty (Rule v Accept : rs) = Rule v Accept : rm_LogEmpty rs;
rm_LogEmpty (Rule v Drop : rs) = Rule v Drop : rm_LogEmpty rs;
rm_LogEmpty (Rule v Reject : rs) = Rule v Reject : rm_LogEmpty rs;
rm_LogEmpty (Rule v (Call vb) : rs) = Rule v (Call vb) : rm_LogEmpty rs;
rm_LogEmpty (Rule v Return : rs) = Rule v Return : rm_LogEmpty rs;
rm_LogEmpty (Rule v (Goto vb) : rs) = Rule v (Goto vb) : rm_LogEmpty rs;
rm_LogEmpty (Rule v Unknown : rs) = Rule v Unknown : rm_LogEmpty rs;

ipv4addr_of_dotdecimal ::
  (Nat, (Nat, (Nat, Nat))) -> Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4addr_of_dotdecimal (a, (b, (c, d))) =
  ipv4addr_of_nat
    (plus_nat
      (plus_nat (plus_nat d (times_nat (nat_of_integer (256 :: Integer)) c))
        (times_nat (nat_of_integer (65536 :: Integer)) b))
      (times_nat (nat_of_integer (16777216 :: Integer)) a));

makea :: forall a. [Prelude.Char] -> Maybe (Word a) -> Routing_action_ext a ();
makea output_iface next_hop = Routing_action_ext output_iface next_hop ();

make ::
  forall a.
    (Len a) => Prefix_match a ->
                 Nat -> Routing_action_ext a () -> Routing_rule_ext a ();
make routing_match metric routing_action =
  Routing_rule_ext routing_match metric routing_action ();

default_metric :: forall a. (Zero a) => a;
default_metric = zero;

empty_rr_hlp :: forall a. (Len a) => Prefix_match a -> Routing_rule_ext a ();
empty_rr_hlp pm = make pm default_metric (makea [] Nothing);

all_pairs :: forall a. [a] -> [(a, a)];
all_pairs xs = concatMap (\ x -> map (\ a -> (x, a)) xs) xs;

sanity_wf_ruleset :: forall a. [([Prelude.Char], [Rule a])] -> Bool;
sanity_wf_ruleset gamma =
  let {
    dom = map fst gamma;
    ran = map snd gamma;
  } in distinct dom && all (all (\ r -> (case get_action r of {
  Accept -> True;
  Drop -> True;
  Log -> True;
  Reject -> True;
  Call a -> membera dom a;
  Return -> True;
  Goto a -> membera dom a;
  Empty -> True;
  Unknown -> False;
})))
                         ran;

match_list_to_match_expr :: forall a. [Match_expr a] -> Match_expr a;
match_list_to_match_expr [] = MatchNot MatchAny;
match_list_to_match_expr (m : ms) = matchOr m (match_list_to_match_expr ms);

ipassmt_iface_replace_dstip_mexpr ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Iface -> Match_expr (Common_primitive a);
ipassmt_iface_replace_dstip_mexpr ipassmt ifce =
  (case ipassmt ifce of {
    Nothing -> Match (OIface ifce);
    Just ips ->
      match_list_to_match_expr
        (map (Match . Dst) (map (uncurry IpAddrNetmask) ips));
  });

oiface_rewrite ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
oiface_rewrite uu MatchAny = MatchAny;
oiface_rewrite ipassmt (Match (OIface ifce)) =
  ipassmt_iface_replace_dstip_mexpr ipassmt ifce;
oiface_rewrite uv (Match (Src v)) = Match (Src v);
oiface_rewrite uv (Match (Dst v)) = Match (Dst v);
oiface_rewrite uv (Match (IIface v)) = Match (IIface v);
oiface_rewrite uv (Match (Prot v)) = Match (Prot v);
oiface_rewrite uv (Match (Src_Ports v)) = Match (Src_Ports v);
oiface_rewrite uv (Match (Dst_Ports v)) = Match (Dst_Ports v);
oiface_rewrite uv (Match (L4_Flags v)) = Match (L4_Flags v);
oiface_rewrite uv (Match (CT_State v)) = Match (CT_State v);
oiface_rewrite uv (Match (Extra v)) = Match (Extra v);
oiface_rewrite ipassmt (MatchNot m) = MatchNot (oiface_rewrite ipassmt m);
oiface_rewrite ipassmt (MatchAnd m1 m2) =
  MatchAnd (oiface_rewrite ipassmt m1) (oiface_rewrite ipassmt m2);

ipassmt_iface_constrain_srcip_mexpr ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Iface -> Match_expr (Common_primitive a);
ipassmt_iface_constrain_srcip_mexpr ipassmt ifce =
  (case ipassmt ifce of {
    Nothing -> Match (IIface ifce);
    Just ips ->
      MatchAnd (Match (IIface ifce))
        (match_list_to_match_expr
          (map (Match . Src) (map (uncurry IpAddrNetmask) ips)));
  });

iiface_constrain ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
iiface_constrain uu MatchAny = MatchAny;
iiface_constrain ipassmt (Match (IIface ifce)) =
  ipassmt_iface_constrain_srcip_mexpr ipassmt ifce;
iiface_constrain ipassmt (Match (Src v)) = Match (Src v);
iiface_constrain ipassmt (Match (Dst v)) = Match (Dst v);
iiface_constrain ipassmt (Match (OIface v)) = Match (OIface v);
iiface_constrain ipassmt (Match (Prot v)) = Match (Prot v);
iiface_constrain ipassmt (Match (Src_Ports v)) = Match (Src_Ports v);
iiface_constrain ipassmt (Match (Dst_Ports v)) = Match (Dst_Ports v);
iiface_constrain ipassmt (Match (L4_Flags v)) = Match (L4_Flags v);
iiface_constrain ipassmt (Match (CT_State v)) = Match (CT_State v);
iiface_constrain ipassmt (Match (Extra v)) = Match (Extra v);
iiface_constrain ipassmt (MatchNot m) = MatchNot (iiface_constrain ipassmt m);
iiface_constrain ipassmt (MatchAnd m1 m2) =
  MatchAnd (iiface_constrain ipassmt m1) (iiface_constrain ipassmt m2);

ipassmt_iface_replace_srcip_mexpr ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Iface -> Match_expr (Common_primitive a);
ipassmt_iface_replace_srcip_mexpr ipassmt ifce =
  (case ipassmt ifce of {
    Nothing -> Match (IIface ifce);
    Just ips ->
      match_list_to_match_expr
        (map (Match . Src) (map (uncurry IpAddrNetmask) ips));
  });

iiface_rewrite ::
  forall a.
    (Len a) => (Iface -> Maybe [(Word a, Nat)]) ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
iiface_rewrite uu MatchAny = MatchAny;
iiface_rewrite ipassmt (Match (IIface ifce)) =
  ipassmt_iface_replace_srcip_mexpr ipassmt ifce;
iiface_rewrite ipassmt (Match (Src v)) = Match (Src v);
iiface_rewrite ipassmt (Match (Dst v)) = Match (Dst v);
iiface_rewrite ipassmt (Match (OIface v)) = Match (OIface v);
iiface_rewrite ipassmt (Match (Prot v)) = Match (Prot v);
iiface_rewrite ipassmt (Match (Src_Ports v)) = Match (Src_Ports v);
iiface_rewrite ipassmt (Match (Dst_Ports v)) = Match (Dst_Ports v);
iiface_rewrite ipassmt (Match (L4_Flags v)) = Match (L4_Flags v);
iiface_rewrite ipassmt (Match (CT_State v)) = Match (CT_State v);
iiface_rewrite ipassmt (Match (Extra v)) = Match (Extra v);
iiface_rewrite ipassmt (MatchNot m) = MatchNot (iiface_rewrite ipassmt m);
iiface_rewrite ipassmt (MatchAnd m1 m2) =
  MatchAnd (iiface_rewrite ipassmt m1) (iiface_rewrite ipassmt m2);

reduce_range_destination ::
  forall a b. (Eq a, Len b) => [(a, Wordinterval b)] -> [(a, Wordinterval b)];
reduce_range_destination l =
  let {
    ps = remdups (map fst l);
    c = (\ s ->
          ((wordinterval_Union . map snd) . filter ((\ a -> s == a) . fst)) l);
  } in map (\ p -> (p, c p)) ps;

routing_action ::
  forall a b. (Len a) => Routing_rule_ext a b -> Routing_action_ext a ();
routing_action (Routing_rule_ext routing_match metric routing_action more) =
  routing_action;

output_iface :: forall a b. Routing_action_ext a b -> [Prelude.Char];
output_iface (Routing_action_ext output_iface next_hop more) = output_iface;

range_prefix_match ::
  forall a.
    (Len a) => Prefix_match a ->
                 Wordinterval a -> (Wordinterval a, Wordinterval a);
range_prefix_match pfx rg =
  let {
    pfxrg = prefix_to_wordinterval pfx;
  } in (wordinterval_intersection rg pfxrg, wordinterval_setminus rg pfxrg);

routing_port_ranges ::
  forall a.
    (Len a) => [Routing_rule_ext a ()] ->
                 Wordinterval a -> [([Prelude.Char], Wordinterval a)];
routing_port_ranges [] lo =
  (if wordinterval_empty lo then []
    else [(output_iface
             ((routing_action ::
                Routing_rule_ext a () -> Routing_action_ext a ())
               (error "undefined")),
            lo)]);
routing_port_ranges (a : asa) lo =
  let {
    rpm = range_prefix_match (routing_match a) lo;
    m = fst rpm;
    nm = snd rpm;
  } in (output_iface (routing_action a), m) : routing_port_ranges asa nm;

routing_ipassmt_wi ::
  forall a.
    (Len a) => [Routing_rule_ext a ()] -> [([Prelude.Char], Wordinterval a)];
routing_ipassmt_wi tbl =
  reduce_range_destination (routing_port_ranges tbl wordinterval_UNIV);

routing_ipassmt ::
  forall a. (Len a) => [Routing_rule_ext a ()] -> [(Iface, [(Word a, Nat)])];
routing_ipassmt rt =
  map (apfst Iface . apsnd cidr_split) (routing_ipassmt_wi rt);

iface_try_rewrite ::
  forall a.
    (Len a) => [(Iface, [(Word a, Nat)])] ->
                 Maybe [Routing_rule_ext a ()] ->
                   [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
iface_try_rewrite ipassmt rtblo rs =
  let {
    o_rewrite =
      (case rtblo of {
        Nothing -> id;
        Just rtbl ->
          transform_optimize_dnf_strict .
            optimize_matches
              (oiface_rewrite (map_of_ipassmt (routing_ipassmt rtbl)));
      });
  } in (if let {
             is = image fst (Set ipassmt);
           } in ball is
                  (\ i1 ->
                    ball is
                      (\ i2 ->
                        (if not (equal_iface i1 i2)
                          then wordinterval_empty
                                 (wordinterval_intersection
                                   (l2wi (map ipcidr_to_interval
   (the (map_of ipassmt i1))))
                                   (l2wi (map ipcidr_to_interval
   (the (map_of ipassmt i2)))))
                          else True))) &&
             ipassmt_sanity_defined rs (map_of ipassmt)
         then optimize_matches (iiface_rewrite (map_of_ipassmt ipassmt))
                (o_rewrite rs)
         else optimize_matches (iiface_constrain (map_of_ipassmt ipassmt))
                (o_rewrite rs));

get_pos_Extra ::
  forall a. (Len a) => Negation_type (Common_primitive a) -> [Prelude.Char];
get_pos_Extra a = let {
                    (Pos (Extra e)) = a;
                  } in e;

map_of_string ::
  forall a.
    [([Prelude.Char], [Rule (Common_primitive a)])] ->
      [Prelude.Char] -> Maybe [Rule (Common_primitive a)];
map_of_string rs = map_of rs;

nat_to_16word :: Nat -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
nat_to_16word i = of_nat i;

ipassmt_generic_ipv4 ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])];
ipassmt_generic_ipv4 =
  [(Iface "lo",
     [(ipv4addr_of_dotdecimal
         (nat_of_integer (127 :: Integer), (zero_nat, (zero_nat, zero_nat))),
        nat_of_integer (8 :: Integer))])];

ipassmt_generic_ipv6 ::
  [(Iface,
     [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))), Nat)])];
ipassmt_generic_ipv6 =
  [(Iface "lo", [(one_word, nat_of_integer (128 :: Integer))])];

ipv6_unparsed_compressed_to_preferred ::
  [Maybe (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] -> Maybe Ipv6addr_syntax;
ipv6_unparsed_compressed_to_preferred ls =
  (if not (equal_nat (size_list (filter is_none ls)) one_nat) ||
        less_nat (nat_of_integer (7 :: Integer))
          (size_list (filter (\ p -> not (is_none p)) ls))
    then Nothing
    else let {
           before_omission = map the (takeWhile (\ x -> not (is_none x)) ls);
           after_omission =
             map the (drop one_nat (dropWhile (\ x -> not (is_none x)) ls));
           num_omissions =
             minus_nat (nat_of_integer (8 :: Integer))
               (plus_nat (size_list before_omission)
                 (size_list after_omission));
           a = before_omission ++
                 replicate num_omissions zero_worda ++ after_omission;
         } in (case a of {
                [] -> Nothing;
                aa : b ->
                  (case b of {
                    [] -> Nothing;
                    ba : c ->
                      (case c of {
                        [] -> Nothing;
                        ca : d ->
                          (case d of {
                            [] -> Nothing;
                            da : e ->
                              (case e of {
                                [] -> Nothing;
                                ea : f ->
                                  (case f of {
                                    [] -> Nothing;
                                    fa : g ->
                                      (case g of {
[] -> Nothing;
ga : h -> (case h of {
            [] -> Nothing;
            [ha] -> Just (IPv6AddrPreferred aa ba ca da ea fa ga ha);
            _ : _ : _ -> Nothing;
          });
                                      });
                                  });
                              });
                          });
                      });
                  });
              }));

mk_ipv6addr ::
  [Maybe (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] -> Maybe Ipv6addr_syntax;
mk_ipv6addr partslist =
  let {
    fix_start = (\ ps -> (case ps of {
                           [] -> ps;
                           [Nothing] -> ps;
                           Nothing : Nothing : _ -> tl ps;
                           Nothing : Just _ : _ -> ps;
                           Just _ : _ -> ps;
                         }));
    fix_end = (\ ps -> (case reverse ps of {
                         [] -> ps;
                         [Nothing] -> ps;
                         Nothing : Nothing : _ -> butlast ps;
                         Nothing : Just _ : _ -> ps;
                         Just _ : _ -> ps;
                       }));
    ps = (fix_end . fix_start) partslist;
  } in (if equal_nat (size_list (filter is_none ps)) one_nat
         then ipv6_unparsed_compressed_to_preferred ps
         else (case ps of {
                [] -> Nothing;
                Nothing : _ -> Nothing;
                [Just _] -> Nothing;
                Just _ : Nothing : _ -> Nothing;
                [Just _, Just _] -> Nothing;
                Just _ : Just _ : Nothing : _ -> Nothing;
                [Just _, Just _, Just _] -> Nothing;
                Just _ : Just _ : Just _ : Nothing : _ -> Nothing;
                [Just _, Just _, Just _, Just _] -> Nothing;
                Just _ : Just _ : Just _ : Just _ : Nothing : _ -> Nothing;
                [Just _, Just _, Just _, Just _, Just _] -> Nothing;
                Just _ : Just _ : Just _ : Just _ : Just _ : Nothing : _ ->
                  Nothing;
                [Just _, Just _, Just _, Just _, Just _, Just _] -> Nothing;
                Just _ :
                  Just _ : Just _ : Just _ : Just _ : Just _ : Nothing : _
                  -> Nothing;
                [Just _, Just _, Just _, Just _, Just _, Just _, Just _] ->
                  Nothing;
                Just _ :
                  Just _ :
                    Just _ : Just _ : Just _ : Just _ : Just _ : Nothing : _
                  -> Nothing;
                [Just a, Just b, Just c, Just d, Just e, Just f, Just g, Just h]
                  -> Just (IPv6AddrPreferred a b c d e f g h);
                Just _ :
                  Just _ :
                    Just _ : Just _ : Just _ : Just _ : Just _ : Just _ : _ : _
                  -> Nothing;
              }));

tcp_flag_toString :: Tcp_flag -> [Prelude.Char];
tcp_flag_toString TCP_SYN = "TCP_SYN";
tcp_flag_toString TCP_ACK = "TCP_ACK";
tcp_flag_toString TCP_FIN = "TCP_FIN";
tcp_flag_toString TCP_RST = "TCP_RST";
tcp_flag_toString TCP_URG = "TCP_URG";
tcp_flag_toString TCP_PSH = "TCP_PSH";

ipt_tcp_syn :: Ipt_tcp_flags;
ipt_tcp_syn =
  TCP_Flags
    (insert TCP_SYN (insert TCP_RST (insert TCP_ACK (insert TCP_FIN bot_set))))
    (insert TCP_SYN bot_set);

terminal_chain :: forall a. [Rule a] -> Bool;
terminal_chain [] = False;
terminal_chain [Rule MatchAny Accept] = True;
terminal_chain [Rule MatchAny Drop] = True;
terminal_chain [Rule MatchAny Reject] = True;
terminal_chain (Rule uu (Goto uv) : rs) = False;
terminal_chain (Rule uw (Call ux) : rs) = False;
terminal_chain (Rule uy Return : rs) = False;
terminal_chain (Rule uz Unknown : rs) = False;
terminal_chain (Rule (Match vc) Accept : rs) = terminal_chain rs;
terminal_chain (Rule (Match vc) Drop : rs) = terminal_chain rs;
terminal_chain (Rule (Match vc) Log : rs) = terminal_chain rs;
terminal_chain (Rule (Match vc) Reject : rs) = terminal_chain rs;
terminal_chain (Rule (Match vc) Empty : rs) = terminal_chain rs;
terminal_chain (Rule (MatchNot vc) Accept : rs) = terminal_chain rs;
terminal_chain (Rule (MatchNot vc) Drop : rs) = terminal_chain rs;
terminal_chain (Rule (MatchNot vc) Log : rs) = terminal_chain rs;
terminal_chain (Rule (MatchNot vc) Reject : rs) = terminal_chain rs;
terminal_chain (Rule (MatchNot vc) Empty : rs) = terminal_chain rs;
terminal_chain (Rule (MatchAnd vc vd) Accept : rs) = terminal_chain rs;
terminal_chain (Rule (MatchAnd vc vd) Drop : rs) = terminal_chain rs;
terminal_chain (Rule (MatchAnd vc vd) Log : rs) = terminal_chain rs;
terminal_chain (Rule (MatchAnd vc vd) Reject : rs) = terminal_chain rs;
terminal_chain (Rule (MatchAnd vc vd) Empty : rs) = terminal_chain rs;
terminal_chain (Rule v Drop : va : vb) = terminal_chain (va : vb);
terminal_chain (Rule v Log : rs) = terminal_chain rs;
terminal_chain (Rule v Reject : va : vb) = terminal_chain (va : vb);
terminal_chain (Rule v Empty : rs) = terminal_chain rs;
terminal_chain (Rule vc Accept : v : vb) = terminal_chain (v : vb);

simple_ruleset :: forall a. [Rule a] -> Bool;
simple_ruleset rs =
  all (\ r ->
        equal_action (get_action r) Accept || equal_action (get_action r) Drop)
    rs;

fill_l4_protocol_raw ::
  forall a.
    (Len a) => Word (Bit0 (Bit0 (Bit0 Num1))) ->
                 [Negation_type (Common_primitive a)] ->
                   [Negation_type (Common_primitive a)];
fill_l4_protocol_raw protocol =
  negPos_map
    (\ a ->
      (case a of {
        Src aa -> Src aa;
        Dst aa -> Dst aa;
        IIface aa -> IIface aa;
        OIface aa -> OIface aa;
        Src_Ports (L4Ports x pts) ->
          (if not (equal_word x zero_worda) then error "undefined"
            else Src_Ports (L4Ports protocol pts));
        Dst_Ports (L4Ports x pts) ->
          (if not (equal_word x zero_worda) then error "undefined"
            else Dst_Ports (L4Ports protocol pts));
        L4_Flags aa -> L4_Flags aa;
        CT_State aa -> CT_State aa;
        Extra aa -> Extra aa;
      }));

fill_l4_protocol ::
  forall a.
    (Len a) => [Negation_type (Common_primitive a)] ->
                 [Negation_type (Common_primitive a)];
fill_l4_protocol [] = [];
fill_l4_protocol (Pos (Prot (Proto protocol)) : ms) =
  Pos (Prot (Proto protocol)) : fill_l4_protocol_raw protocol ms;
fill_l4_protocol (Pos (Src_Ports uu) : uv) = error "undefined";
fill_l4_protocol (Pos (Dst_Ports uw) : ux) = error "undefined";
fill_l4_protocol (Pos (Src va) : ms) = Pos (Src va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (Dst va) : ms) = Pos (Dst va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (IIface va) : ms) = Pos (IIface va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (OIface va) : ms) = Pos (OIface va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (Prot ProtoAny) : ms) =
  Pos (Prot ProtoAny) : fill_l4_protocol ms;
fill_l4_protocol (Pos (L4_Flags va) : ms) =
  Pos (L4_Flags va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (CT_State va) : ms) =
  Pos (CT_State va) : fill_l4_protocol ms;
fill_l4_protocol (Pos (Extra va) : ms) = Pos (Extra va) : fill_l4_protocol ms;
fill_l4_protocol (Neg v : ms) = Neg v : fill_l4_protocol ms;

integer_to_16word :: Integer -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
integer_to_16word i = nat_to_16word (nat_of_integer i);

ctstate_toString :: Ctstate -> [Prelude.Char];
ctstate_toString CT_New = "NEW";
ctstate_toString CT_Established = "ESTABLISHED";
ctstate_toString CT_Related = "RELATED";
ctstate_toString CT_Untracked = "UNTRACKED";
ctstate_toString CT_Invalid = "INVALID";

has_disc :: forall a. (a -> Bool) -> Match_expr a -> Bool;
has_disc uu MatchAny = False;
has_disc disc (Match a) = disc a;
has_disc disc (MatchNot m) = has_disc disc m;
has_disc disc (MatchAnd m1 m2) = has_disc disc m1 || has_disc disc m2;

rewrite_Goto_chain_safe ::
  forall a. ([Prelude.Char] -> Maybe [Rule a]) -> [Rule a] -> Maybe [Rule a];
rewrite_Goto_chain_safe uu [] = Just [];
rewrite_Goto_chain_safe gamma (Rule m (Goto chain) : rs) =
  (case gamma chain of {
    Nothing -> Nothing;
    Just rsa ->
      (if not (terminal_chain rsa) then Nothing
        else map_option (\ a -> Rule m (Call chain) : a)
               (rewrite_Goto_chain_safe gamma rs));
  });
rewrite_Goto_chain_safe gamma (Rule v Accept : rs) =
  map_option (\ a -> Rule v Accept : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Drop : rs) =
  map_option (\ a -> Rule v Drop : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Log : rs) =
  map_option (\ a -> Rule v Log : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Reject : rs) =
  map_option (\ a -> Rule v Reject : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v (Call vb) : rs) =
  map_option (\ a -> Rule v (Call vb) : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Return : rs) =
  map_option (\ a -> Rule v Return : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Empty : rs) =
  map_option (\ a -> Rule v Empty : a) (rewrite_Goto_chain_safe gamma rs);
rewrite_Goto_chain_safe gamma (Rule v Unknown : rs) =
  map_option (\ a -> Rule v Unknown : a) (rewrite_Goto_chain_safe gamma rs);

rewrite_Goto_safe_internal ::
  forall a.
    [([Prelude.Char], [Rule a])] ->
      [([Prelude.Char], [Rule a])] -> Maybe [([Prelude.Char], [Rule a])];
rewrite_Goto_safe_internal uu [] = Just [];
rewrite_Goto_safe_internal gamma ((chain_name, rs) : cs) =
  (case rewrite_Goto_chain_safe (map_of gamma) rs of {
    Nothing -> Nothing;
    Just rsa ->
      map_option (\ a -> (chain_name, rsa) : a)
        (rewrite_Goto_safe_internal gamma cs);
  });

rewrite_Goto_safe ::
  forall a. [([Prelude.Char], [Rule a])] -> Maybe [([Prelude.Char], [Rule a])];
rewrite_Goto_safe cs = rewrite_Goto_safe_internal cs cs;

process_ret :: forall a. [Rule a] -> [Rule a];
process_ret [] = [];
process_ret (Rule m Return : rs) = add_match (MatchNot m) (process_ret rs);
process_ret (Rule v Accept : rs) = Rule v Accept : process_ret rs;
process_ret (Rule v Drop : rs) = Rule v Drop : process_ret rs;
process_ret (Rule v Log : rs) = Rule v Log : process_ret rs;
process_ret (Rule v Reject : rs) = Rule v Reject : process_ret rs;
process_ret (Rule v (Call vb) : rs) = Rule v (Call vb) : process_ret rs;
process_ret (Rule v (Goto vb) : rs) = Rule v (Goto vb) : process_ret rs;
process_ret (Rule v Empty : rs) = Rule v Empty : process_ret rs;
process_ret (Rule v Unknown : rs) = Rule v Unknown : process_ret rs;

dec_string_of_word0 :: forall a. (Len a) => Word a -> [Prelude.Char];
dec_string_of_word0 =
  string_of_word True (word_of_int (Int_of_integer (10 :: Integer))) zero_nat;

port_toString :: Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) -> [Prelude.Char];
port_toString p = dec_string_of_word0 p;

wordinterval_sort :: forall a. (Len a) => Wordinterval a -> Wordinterval a;
wordinterval_sort w = l2wi (mergesort_remdups (wi2l w));

build_ip_partition ::
  forall a.
    (Len a) => Parts_connection_ext () -> [Simple_rule a] -> [Wordinterval a];
build_ip_partition c rs =
  map (\ xs ->
        wordinterval_sort
          (wordinterval_compress
            (foldr wordinterval_union xs empty_WordInterval)))
    (groupWIs3 c rs);

process_call ::
  forall a. ([Prelude.Char] -> Maybe [Rule a]) -> [Rule a] -> [Rule a];
process_call gamma [] = [];
process_call gamma (Rule m (Call chain) : rs) =
  add_match m (process_ret (the (gamma chain))) ++ process_call gamma rs;
process_call gamma (Rule v Accept : rs) = Rule v Accept : process_call gamma rs;
process_call gamma (Rule v Drop : rs) = Rule v Drop : process_call gamma rs;
process_call gamma (Rule v Log : rs) = Rule v Log : process_call gamma rs;
process_call gamma (Rule v Reject : rs) = Rule v Reject : process_call gamma rs;
process_call gamma (Rule v Return : rs) = Rule v Return : process_call gamma rs;
process_call gamma (Rule v (Goto vb) : rs) =
  Rule v (Goto vb) : process_call gamma rs;
process_call gamma (Rule v Empty : rs) = Rule v Empty : process_call gamma rs;
process_call gamma (Rule v Unknown : rs) =
  Rule v Unknown : process_call gamma rs;

enum_set_get_one :: forall a. (Eq a) => [a] -> Set a -> Maybe a;
enum_set_get_one [] s = Nothing;
enum_set_get_one (sa : ss) s =
  (if member sa s then Just sa else enum_set_get_one ss s);

enum_set_to_list :: forall a. (Enum a, Eq a) => Set a -> [a];
enum_set_to_list s =
  (if is_empty s then [] else (case enum_set_get_one enum s of {
                                Nothing -> [];
                                Just a -> a : enum_set_to_list (remove a s);
                              }));

ipt_tcp_flags_toString :: Set Tcp_flag -> [Prelude.Char];
ipt_tcp_flags_toString flags =
  list_toString tcp_flag_toString (enum_set_to_list flags);

iface_toString :: [Prelude.Char] -> Iface -> [Prelude.Char];
iface_toString descr iface =
  (if equal_iface iface ifaceAny then [] else let {
        (Iface a) = iface;
      } in descr ++ a);

ports_toString ::
  [Prelude.Char] ->
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
      [Prelude.Char];
ports_toString descr (s, e) =
  (if equal_word s zero_worda && equal_word e max_word then []
    else descr ++
           (if equal_word s e then port_toString s
             else port_toString s ++ ":" ++ port_toString e));

valid_prefix_fw :: forall a. (Len a) => (Word a, Nat) -> Bool;
valid_prefix_fw m = valid_prefix (uncurry PrefixMatch m);

simple_fw_valid :: forall a. (Len a) => [Simple_rule a] -> Bool;
simple_fw_valid =
  all ((\ m ->
         let {
           c = (\ (s, e) ->
                 not (equal_word s zero_worda) || not (equal_word e max_word));
         } in (if c (sports m) || c (dports m)
                then equal_protocol (proto m) (Proto tcp) ||
                       (equal_protocol (proto m) (Proto udp) ||
                         equal_protocol (proto m) (Proto sctp))
                else True) &&
           valid_prefix_fw (src m) && valid_prefix_fw (dst m)) .
        match_sel);

simpl_ports_conjunct ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
    Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
      (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
        Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
simpl_ports_conjunct (p1s, p1e) (p2s, p2e) = (max p1s p2s, min p1e p2e);

simple_match_and ::
  forall a.
    (Len a) => Simple_match_ext a () ->
                 Simple_match_ext a () -> Maybe (Simple_match_ext a ());
simple_match_and (Simple_match_ext iif1 oif1 sip1 dip1 p1 sps1 dps1 ())
  (Simple_match_ext iif2 oif2 sip2 dip2 p2 sps2 dps2 ()) =
  (case (if wordinterval_empty
              (wordinterval_intersection (ipcidr_tuple_to_wordinterval sip1)
                (ipcidr_tuple_to_wordinterval sip2))
          then Nothing
          else (if wordinterval_subset (ipcidr_tuple_to_wordinterval sip1)
                     (ipcidr_tuple_to_wordinterval sip2)
                 then Just sip1 else Just sip2))
    of {
    Nothing -> Nothing;
    Just sip ->
      (case (if wordinterval_empty
                  (wordinterval_intersection (ipcidr_tuple_to_wordinterval dip1)
                    (ipcidr_tuple_to_wordinterval dip2))
              then Nothing
              else (if wordinterval_subset (ipcidr_tuple_to_wordinterval dip1)
                         (ipcidr_tuple_to_wordinterval dip2)
                     then Just dip1 else Just dip2))
        of {
        Nothing -> Nothing;
        Just dip ->
          (case iface_conjunct iif1 iif2 of {
            Nothing -> Nothing;
            Just iif ->
              (case iface_conjunct oif1 oif2 of {
                Nothing -> Nothing;
                Just oif ->
                  (case simple_proto_conjunct p1 p2 of {
                    Nothing -> Nothing;
                    Just p ->
                      Just (Simple_match_ext iif oif sip dip p
                             (simpl_ports_conjunct sps1 sps2)
                             (simpl_ports_conjunct dps1 dps2) ());
                  });
              });
          });
      });
  });

compress_parsed_extra ::
  forall a.
    (Len a) => [Negation_type (Common_primitive a)] ->
                 [Negation_type (Common_primitive a)];
compress_parsed_extra [] = [];
compress_parsed_extra (a1 : a2 : asa) =
  (if is_pos_Extra a1 && is_pos_Extra a2
    then compress_parsed_extra
           (Pos (Extra (get_pos_Extra a1 ++ " " ++ get_pos_Extra a2)) : asa)
    else a1 : compress_parsed_extra (a2 : asa));
compress_parsed_extra [a] = a : compress_parsed_extra [];

ctstate_set_toString :: Set Ctstate -> [Prelude.Char];
ctstate_set_toString s =
  list_separated_toString "," ctstate_toString (enum_set_to_list s);

normalized_dst_ports ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_dst_ports MatchAny = True;
normalized_dst_ports (Match (Dst_Ports (L4Ports uu []))) = True;
normalized_dst_ports (Match (Dst_Ports (L4Ports uv [uw]))) = True;
normalized_dst_ports (Match (Dst_Ports (L4Ports v (vb : va : vd)))) = False;
normalized_dst_ports (Match (Src v)) = True;
normalized_dst_ports (Match (Dst v)) = True;
normalized_dst_ports (Match (IIface v)) = True;
normalized_dst_ports (Match (OIface v)) = True;
normalized_dst_ports (Match (Prot v)) = True;
normalized_dst_ports (Match (Src_Ports v)) = True;
normalized_dst_ports (Match (L4_Flags v)) = True;
normalized_dst_ports (Match (CT_State v)) = True;
normalized_dst_ports (Match (Extra v)) = True;
normalized_dst_ports (MatchNot (Match (Dst_Ports uz))) = False;
normalized_dst_ports (MatchNot (Match (Src v))) = True;
normalized_dst_ports (MatchNot (Match (Dst v))) = True;
normalized_dst_ports (MatchNot (Match (IIface v))) = True;
normalized_dst_ports (MatchNot (Match (OIface v))) = True;
normalized_dst_ports (MatchNot (Match (Prot v))) = True;
normalized_dst_ports (MatchNot (Match (Src_Ports v))) = True;
normalized_dst_ports (MatchNot (Match (L4_Flags v))) = True;
normalized_dst_ports (MatchNot (Match (CT_State v))) = True;
normalized_dst_ports (MatchNot (Match (Extra v))) = True;
normalized_dst_ports (MatchAnd m1 m2) =
  normalized_dst_ports m1 && normalized_dst_ports m2;
normalized_dst_ports (MatchNot (MatchAnd vb vc)) = False;
normalized_dst_ports (MatchNot (MatchNot vd)) = False;
normalized_dst_ports (MatchNot MatchAny) = True;

normalized_src_ports ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_src_ports MatchAny = True;
normalized_src_ports (Match (Src_Ports (L4Ports uu []))) = True;
normalized_src_ports (Match (Src_Ports (L4Ports uv [uw]))) = True;
normalized_src_ports (Match (Src_Ports (L4Ports v (vb : va : vd)))) = False;
normalized_src_ports (Match (Src v)) = True;
normalized_src_ports (Match (Dst v)) = True;
normalized_src_ports (Match (IIface v)) = True;
normalized_src_ports (Match (OIface v)) = True;
normalized_src_ports (Match (Prot v)) = True;
normalized_src_ports (Match (Dst_Ports v)) = True;
normalized_src_ports (Match (L4_Flags v)) = True;
normalized_src_ports (Match (CT_State v)) = True;
normalized_src_ports (Match (Extra v)) = True;
normalized_src_ports (MatchNot (Match (Src_Ports uz))) = False;
normalized_src_ports (MatchNot (Match (Src v))) = True;
normalized_src_ports (MatchNot (Match (Dst v))) = True;
normalized_src_ports (MatchNot (Match (IIface v))) = True;
normalized_src_ports (MatchNot (Match (OIface v))) = True;
normalized_src_ports (MatchNot (Match (Prot v))) = True;
normalized_src_ports (MatchNot (Match (Dst_Ports v))) = True;
normalized_src_ports (MatchNot (Match (L4_Flags v))) = True;
normalized_src_ports (MatchNot (Match (CT_State v))) = True;
normalized_src_ports (MatchNot (Match (Extra v))) = True;
normalized_src_ports (MatchAnd m1 m2) =
  normalized_src_ports m1 && normalized_src_ports m2;
normalized_src_ports (MatchNot (MatchAnd vb vc)) = False;
normalized_src_ports (MatchNot (MatchNot vd)) = False;
normalized_src_ports (MatchNot MatchAny) = True;

ipt_tcp_flags_equal :: Ipt_tcp_flags -> Ipt_tcp_flags -> Bool;
ipt_tcp_flags_equal (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) =
  (if less_eq_set c1 fmask1 && less_eq_set c2 fmask2
    then equal_set c1 c2 && equal_set fmask1 fmask2
    else not (less_eq_set c1 fmask1) && not (less_eq_set c2 fmask2));

primitive_protocol_toString :: Word (Bit0 (Bit0 (Bit0 Num1))) -> [Prelude.Char];
primitive_protocol_toString protid =
  (if equal_word protid tcp then "tcp"
    else (if equal_word protid udp then "udp"
           else (if equal_word protid icmp then "icmp"
                  else (if equal_word protid sctp then "sctp"
                         else (if equal_word protid igmp then "igmp"
                                else (if equal_word protid gre then "gre"
                                       else (if equal_word protid esp then "esp"
      else (if equal_word protid ah then "ah"
             else (if equal_word protid iPv6ICMP then "ipv6-icmp"
                    else "protocolid:" ++ dec_string_of_word0 protid)))))))));

protocol_toString :: Protocol -> [Prelude.Char];
protocol_toString ProtoAny = "all";
protocol_toString (Proto protid) = primitive_protocol_toString protid;

common_primitive_toString ::
  forall a.
    (Len a) => (Word a -> [Prelude.Char]) ->
                 Common_primitive a -> [Prelude.Char];
common_primitive_toString ipToStr (Src (IpAddr ip)) = "-s " ++ ipToStr ip;
common_primitive_toString ipToStr (Dst (IpAddr ip)) = "-d " ++ ipToStr ip;
common_primitive_toString ipToStr (Src (IpAddrNetmask ip n)) =
  "-s " ++ ipToStr ip ++ "/" ++ string_of_nat n;
common_primitive_toString ipToStr (Dst (IpAddrNetmask ip n)) =
  "-d " ++ ipToStr ip ++ "/" ++ string_of_nat n;
common_primitive_toString ipToStr (Src (IpAddrRange ip1 ip2)) =
  "-m iprange --src-range " ++ ipToStr ip1 ++ "-" ++ ipToStr ip2;
common_primitive_toString ipToStr (Dst (IpAddrRange ip1 ip2)) =
  "-m iprange --dst-range " ++ ipToStr ip1 ++ "-" ++ ipToStr ip2;
common_primitive_toString uu (IIface ifce) = iface_toString "-i " ifce;
common_primitive_toString uv (OIface ifce) = iface_toString "-o " ifce;
common_primitive_toString uw (Prot prot) = "-p " ++ protocol_toString prot;
common_primitive_toString ux (Src_Ports (L4Ports prot pts)) =
  "-m " ++
    primitive_protocol_toString prot ++
      " --spts " ++ list_toString (ports_toString []) pts;
common_primitive_toString uy (Dst_Ports (L4Ports prot pts)) =
  "-m " ++
    primitive_protocol_toString prot ++
      " --dpts " ++ list_toString (ports_toString []) pts;
common_primitive_toString uz (CT_State s) =
  "-m state --state " ++ ctstate_set_toString s;
common_primitive_toString va (L4_Flags (TCP_Flags c m)) =
  "--tcp-flags " ++ ipt_tcp_flags_toString c ++ " " ++ ipt_tcp_flags_toString m;
common_primitive_toString vb (Extra e) = "~~" ++ e ++ "~~";

ipaddr_generic_toString :: forall a. (Len a) => Word a -> [Prelude.Char];
ipaddr_generic_toString ip =
  "[IP address (" ++
    string_of_nat ((len_of :: Itself a -> Nat) Type) ++
      " bit): " ++ dec_string_of_word0 ip ++ "]";

abstract_primitive ::
  forall a.
    (Len a) => (Negation_type (Common_primitive a) -> Bool) ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
abstract_primitive uu MatchAny = MatchAny;
abstract_primitive disc (Match a) =
  (if disc (Pos a)
    then Match (Extra (common_primitive_toString ipaddr_generic_toString a))
    else Match a);
abstract_primitive disc (MatchNot (Match a)) =
  (if disc (Neg a)
    then Match (Extra
                 ("! " ++ common_primitive_toString ipaddr_generic_toString a))
    else MatchNot (Match a));
abstract_primitive disc (MatchNot (MatchNot v)) =
  MatchNot (abstract_primitive disc (MatchNot v));
abstract_primitive disc (MatchNot (MatchAnd v va)) =
  MatchNot (abstract_primitive disc (MatchAnd v va));
abstract_primitive disc (MatchNot MatchAny) =
  MatchNot (abstract_primitive disc MatchAny);
abstract_primitive disc (MatchAnd m1 m2) =
  MatchAnd (abstract_primitive disc m1) (abstract_primitive disc m2);

next_hop :: forall a b. Routing_action_ext a b -> Maybe (Word a);
next_hop (Routing_action_ext output_iface next_hop more) = next_hop;

has_disc_negated :: forall a. (a -> Bool) -> Bool -> Match_expr a -> Bool;
has_disc_negated uu uv MatchAny = False;
has_disc_negated disc neg (Match a) = (if disc a then neg else False);
has_disc_negated disc neg (MatchNot m) = has_disc_negated disc (not neg) m;
has_disc_negated disc neg (MatchAnd m1 m2) =
  has_disc_negated disc neg m1 || has_disc_negated disc neg m2;

normalized_ifaces ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_ifaces m =
  not (has_disc_negated (\ a -> is_Iiface a || is_Oiface a) False m);

ipv4_cidr_toString ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat) -> [Prelude.Char];
ipv4_cidr_toString ip_n = let {
                            (base, n) = ip_n;
                          } in ipv4addr_toString base ++ "/" ++ string_of_nat n;

ipv6_cidr_toString ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))), Nat) ->
    [Prelude.Char];
ipv6_cidr_toString ip_n = let {
                            (base, n) = ip_n;
                          } in ipv6addr_toString base ++ "/" ++ string_of_nat n;

prefix_match_32_toString ::
  Prefix_match (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
prefix_match_32_toString pfx =
  let {
    (PrefixMatch p l) = pfx;
  } in ipv4addr_toString p ++
         (if not (equal_nat l (nat_of_integer (32 :: Integer)))
           then "/" ++ string_of_nat l else []);

routing_rule_32_toString ::
  Routing_rule_ext (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) () -> [Prelude.Char];
routing_rule_32_toString rr =
  prefix_match_32_toString (routing_match rr) ++
    (case next_hop (routing_action rr) of {
      Nothing -> [];
      Just nh -> " via " ++ ipv4addr_toString nh;
    }) ++
      " dev " ++
        output_iface (routing_action rr) ++
          " metric " ++ string_of_nat (metric rr);

mk_parts_connection_TCP ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) ->
    Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) -> Parts_connection_ext ();
mk_parts_connection_TCP sport dport =
  Parts_connection_ext "1" "1" tcp sport dport ();

sports_update ::
  forall a b.
    (Len a) => ((Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                  Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
                 (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                   Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))) ->
                 Simple_match_ext a b -> Simple_match_ext a b;
sports_update sportsa
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface oiface src dst proto (sportsa sports) dports more;

oiface_update ::
  forall a b.
    (Len a) => (Iface -> Iface) -> Simple_match_ext a b -> Simple_match_ext a b;
oiface_update oifacea
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface (oifacea oiface) src dst proto sports dports more;

iiface_update ::
  forall a b.
    (Len a) => (Iface -> Iface) -> Simple_match_ext a b -> Simple_match_ext a b;
iiface_update iifacea
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext (iifacea iiface) oiface src dst proto sports dports more;

dports_update ::
  forall a b.
    (Len a) => ((Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                  Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
                 (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
                   Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))) ->
                 Simple_match_ext a b -> Simple_match_ext a b;
dports_update dportsa
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface oiface src dst proto sports (dportsa dports) more;

proto_update ::
  forall a b.
    (Len a) => (Protocol -> Protocol) ->
                 Simple_match_ext a b -> Simple_match_ext a b;
proto_update protoa
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface oiface src dst (protoa proto) sports dports more;

src_update ::
  forall a b.
    (Len a) => ((Word a, Nat) -> (Word a, Nat)) ->
                 Simple_match_ext a b -> Simple_match_ext a b;
src_update srca
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface oiface (srca src) dst proto sports dports more;

dst_update ::
  forall a b.
    (Len a) => ((Word a, Nat) -> (Word a, Nat)) ->
                 Simple_match_ext a b -> Simple_match_ext a b;
dst_update dsta
  (Simple_match_ext iiface oiface src dst proto sports dports more) =
  Simple_match_ext iiface oiface src (dsta dst) proto sports dports more;

common_primitive_match_to_simple_match ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) -> Maybe (Simple_match_ext a ());
common_primitive_match_to_simple_match MatchAny = Just simple_match_any;
common_primitive_match_to_simple_match (MatchNot MatchAny) = Nothing;
common_primitive_match_to_simple_match (Match (IIface iif)) =
  Just (iiface_update (\ _ -> iif) simple_match_any);
common_primitive_match_to_simple_match (Match (OIface oif)) =
  Just (oiface_update (\ _ -> oif) simple_match_any);
common_primitive_match_to_simple_match (Match (Src (IpAddrNetmask pre len))) =
  Just (src_update (\ _ -> (pre, len)) simple_match_any);
common_primitive_match_to_simple_match (Match (Dst (IpAddrNetmask pre len))) =
  Just (dst_update (\ _ -> (pre, len)) simple_match_any);
common_primitive_match_to_simple_match (Match (Prot p)) =
  Just (proto_update (\ _ -> p) simple_match_any);
common_primitive_match_to_simple_match (Match (Src_Ports (L4Ports p []))) =
  Nothing;
common_primitive_match_to_simple_match (Match (Src_Ports (L4Ports p [(s, e)])))
  = Just (sports_update (\ _ -> (s, e))
           (proto_update (\ _ -> Proto p) simple_match_any));
common_primitive_match_to_simple_match (Match (Dst_Ports (L4Ports p []))) =
  Nothing;
common_primitive_match_to_simple_match (Match (Dst_Ports (L4Ports p [(s, e)])))
  = Just (dports_update (\ _ -> (s, e))
           (proto_update (\ _ -> Proto p) simple_match_any));
common_primitive_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) =
  Nothing;
common_primitive_match_to_simple_match (MatchAnd m1 m2) =
  (case (common_primitive_match_to_simple_match m1,
          common_primitive_match_to_simple_match m2)
    of {
    (Nothing, _) -> Nothing;
    (Just _, Nothing) -> Nothing;
    (Just a, Just b) -> simple_match_and a b;
  });
common_primitive_match_to_simple_match (Match (Src (IpAddr uu))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Src (IpAddrRange uv uw))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Dst (IpAddr ux))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Dst (IpAddrRange uy uz))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Prot (Proto v)))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (IIface vb))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (OIface vc))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Src vd))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Dst ve))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (MatchAnd vf vg)) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (MatchNot vh)) =
  error "undefined";
common_primitive_match_to_simple_match
  (Match (Src_Ports (L4Ports v (vb : va : vd)))) = error "undefined";
common_primitive_match_to_simple_match
  (Match (Dst_Ports (L4Ports v (vb : va : vd)))) = error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Src_Ports vk))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Dst_Ports vl))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (CT_State vm)) =
  error "undefined";
common_primitive_match_to_simple_match (Match (L4_Flags vn)) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (L4_Flags vo))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Extra vp)) = error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Extra vq))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (CT_State vr))) =
  error "undefined";

is_L4_Flags :: forall a. (Len a) => Common_primitive a -> Bool;
is_L4_Flags (Src x1) = False;
is_L4_Flags (Dst x2) = False;
is_L4_Flags (IIface x3) = False;
is_L4_Flags (OIface x4) = False;
is_L4_Flags (Prot x5) = False;
is_L4_Flags (Src_Ports x6) = False;
is_L4_Flags (Dst_Ports x7) = False;
is_L4_Flags (L4_Flags x8) = True;
is_L4_Flags (CT_State x9) = False;
is_L4_Flags (Extra x10) = False;

is_CT_State :: forall a. (Len a) => Common_primitive a -> Bool;
is_CT_State (Src x1) = False;
is_CT_State (Dst x2) = False;
is_CT_State (IIface x3) = False;
is_CT_State (OIface x4) = False;
is_CT_State (Prot x5) = False;
is_CT_State (Src_Ports x6) = False;
is_CT_State (Dst_Ports x7) = False;
is_CT_State (L4_Flags x8) = False;
is_CT_State (CT_State x9) = True;
is_CT_State (Extra x10) = False;

is_Extra :: forall a. (Len a) => Common_primitive a -> Bool;
is_Extra (Src x1) = False;
is_Extra (Dst x2) = False;
is_Extra (IIface x3) = False;
is_Extra (OIface x4) = False;
is_Extra (Prot x5) = False;
is_Extra (Src_Ports x6) = False;
is_Extra (Dst_Ports x7) = False;
is_Extra (L4_Flags x8) = False;
is_Extra (CT_State x9) = False;
is_Extra (Extra x10) = True;

normalized_protocols ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_protocols m = not (has_disc_negated is_Prot False m);

normalized_src_ips ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_src_ips MatchAny = True;
normalized_src_ips (Match (Src (IpAddrRange uu uv))) = False;
normalized_src_ips (Match (Src (IpAddr uw))) = False;
normalized_src_ips (Match (Src (IpAddrNetmask ux uy))) = True;
normalized_src_ips (Match (Dst v)) = True;
normalized_src_ips (Match (IIface v)) = True;
normalized_src_ips (Match (OIface v)) = True;
normalized_src_ips (Match (Prot v)) = True;
normalized_src_ips (Match (Src_Ports v)) = True;
normalized_src_ips (Match (Dst_Ports v)) = True;
normalized_src_ips (Match (L4_Flags v)) = True;
normalized_src_ips (Match (CT_State v)) = True;
normalized_src_ips (Match (Extra v)) = True;
normalized_src_ips (MatchNot (Match (Src va))) = False;
normalized_src_ips (MatchNot (Match (Dst v))) = True;
normalized_src_ips (MatchNot (Match (IIface v))) = True;
normalized_src_ips (MatchNot (Match (OIface v))) = True;
normalized_src_ips (MatchNot (Match (Prot v))) = True;
normalized_src_ips (MatchNot (Match (Src_Ports v))) = True;
normalized_src_ips (MatchNot (Match (Dst_Ports v))) = True;
normalized_src_ips (MatchNot (Match (L4_Flags v))) = True;
normalized_src_ips (MatchNot (Match (CT_State v))) = True;
normalized_src_ips (MatchNot (Match (Extra v))) = True;
normalized_src_ips (MatchAnd m1 m2) =
  normalized_src_ips m1 && normalized_src_ips m2;
normalized_src_ips (MatchNot (MatchAnd vc vd)) = False;
normalized_src_ips (MatchNot (MatchNot ve)) = False;
normalized_src_ips (MatchNot MatchAny) = True;

normalized_dst_ips ::
  forall a. (Len a) => Match_expr (Common_primitive a) -> Bool;
normalized_dst_ips MatchAny = True;
normalized_dst_ips (Match (Dst (IpAddrRange uu uv))) = False;
normalized_dst_ips (Match (Dst (IpAddr uw))) = False;
normalized_dst_ips (Match (Dst (IpAddrNetmask ux uy))) = True;
normalized_dst_ips (Match (Src v)) = True;
normalized_dst_ips (Match (IIface v)) = True;
normalized_dst_ips (Match (OIface v)) = True;
normalized_dst_ips (Match (Prot v)) = True;
normalized_dst_ips (Match (Src_Ports v)) = True;
normalized_dst_ips (Match (Dst_Ports v)) = True;
normalized_dst_ips (Match (L4_Flags v)) = True;
normalized_dst_ips (Match (CT_State v)) = True;
normalized_dst_ips (Match (Extra v)) = True;
normalized_dst_ips (MatchNot (Match (Dst va))) = False;
normalized_dst_ips (MatchNot (Match (Src v))) = True;
normalized_dst_ips (MatchNot (Match (IIface v))) = True;
normalized_dst_ips (MatchNot (Match (OIface v))) = True;
normalized_dst_ips (MatchNot (Match (Prot v))) = True;
normalized_dst_ips (MatchNot (Match (Src_Ports v))) = True;
normalized_dst_ips (MatchNot (Match (Dst_Ports v))) = True;
normalized_dst_ips (MatchNot (Match (L4_Flags v))) = True;
normalized_dst_ips (MatchNot (Match (CT_State v))) = True;
normalized_dst_ips (MatchNot (Match (Extra v))) = True;
normalized_dst_ips (MatchAnd m1 m2) =
  normalized_dst_ips m1 && normalized_dst_ips m2;
normalized_dst_ips (MatchNot (MatchAnd vc vd)) = False;
normalized_dst_ips (MatchNot (MatchNot ve)) = False;
normalized_dst_ips (MatchNot MatchAny) = True;

check_simple_fw_preconditions ::
  forall a. (Len a) => [Rule (Common_primitive a)] -> Bool;
check_simple_fw_preconditions rs =
  all (\ (Rule m a) ->
        normalized_src_ports m &&
          normalized_dst_ports m &&
            normalized_src_ips m &&
              normalized_dst_ips m &&
                normalized_ifaces m &&
                  normalized_protocols m &&
                    not (has_disc is_L4_Flags m) &&
                      not (has_disc is_CT_State m) &&
                        not (has_disc is_Extra m) &&
                          (equal_action a Accept || equal_action a Drop))
    rs;

action_to_simple_action :: Action -> Simple_action;
action_to_simple_action Accept = Accepta;
action_to_simple_action Drop = Dropa;
action_to_simple_action Log = error "undefined";
action_to_simple_action Reject = error "undefined";
action_to_simple_action (Call v) = error "undefined";
action_to_simple_action Return = error "undefined";
action_to_simple_action (Goto v) = error "undefined";
action_to_simple_action Empty = error "undefined";
action_to_simple_action Unknown = error "undefined";

to_simple_firewall ::
  forall a. (Len a) => [Rule (Common_primitive a)] -> [Simple_rule a];
to_simple_firewall rs =
  (if check_simple_fw_preconditions rs
    then map_filter
           (\ (Rule m a) ->
             (case common_primitive_match_to_simple_match m of {
               Nothing -> Nothing;
               Just sm -> Just (SimpleRule sm (action_to_simple_action a));
             }))
           rs
    else error "undefined");

ipt_tcp_flags_NoMatch :: Ipt_tcp_flags;
ipt_tcp_flags_NoMatch = TCP_Flags bot_set (insert TCP_SYN bot_set);

prefix_match_128_toString ::
  Prefix_match (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) ->
    [Prelude.Char];
prefix_match_128_toString pfx =
  let {
    (PrefixMatch p l) = pfx;
  } in ipv6addr_toString p ++
         (if not (equal_nat l (nat_of_integer (128 :: Integer)))
           then "/" ++ string_of_nat l else []);

routing_rule_128_toString ::
  Routing_rule_ext (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) () ->
    [Prelude.Char];
routing_rule_128_toString rr =
  prefix_match_128_toString (routing_match rr) ++
    (case next_hop (routing_action rr) of {
      Nothing -> [];
      Just nh -> " via " ++ ipv6addr_toString nh;
    }) ++
      " dev " ++
        output_iface (routing_action rr) ++
          " metric " ++ string_of_nat (metric rr);

unfold_optimize_ruleset_CHAIN ::
  forall a.
    (Eq a) => (Match_expr a -> Match_expr a) ->
                [Prelude.Char] ->
                  Action ->
                    ([Prelude.Char] -> Maybe [Rule a]) -> Maybe [Rule a];
unfold_optimize_ruleset_CHAIN optimize chain_name default_action rs =
  let {
    rsa = repeat_stabilize (nat_of_integer (1000 :: Integer))
            (optimize_matches opt_MatchAny_match_expr)
            (optimize_matches optimize
              (rw_Reject
                (rm_LogEmpty
                  (repeat_stabilize (nat_of_integer (10000 :: Integer))
                    (process_call rs)
                    [Rule MatchAny (Call chain_name),
                      Rule MatchAny default_action]))));
  } in (if simple_ruleset rsa then Just rsa else Nothing);

unfold_ruleset_CHAIN_safe ::
  forall a.
    (Len a) => [Prelude.Char] ->
                 Action ->
                   ([Prelude.Char] -> Maybe [Rule (Common_primitive a)]) ->
                     Maybe [Rule (Common_primitive a)];
unfold_ruleset_CHAIN_safe =
  unfold_optimize_ruleset_CHAIN optimize_primitive_univ;

metric_update ::
  forall a b.
    (Len a) => (Nat -> Nat) -> Routing_rule_ext a b -> Routing_rule_ext a b;
metric_update metrica
  (Routing_rule_ext routing_match metric routing_action more) =
  Routing_rule_ext routing_match (metrica metric) routing_action more;

access_matrix_pretty_ipv4_code ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty_ipv4_code c rs =
  (if not (all (\ m ->
                 equal_iface (iiface (match_sel m)) ifaceAny &&
                   equal_iface (oiface (match_sel m)) ifaceAny)
            rs)
    then error "undefined"
    else let {
           w = build_ip_partition c rs;
           r = map getOneIp w;
           _ = all_pairs r;
         } in (zip (map ipv4addr_toString r)
                 (map ipv4addr_wordinterval_toString w),
                map_filter
                  (\ x ->
                    (if let {
                          (s, d) = x;
                        } in equal_state (runFw s d c rs) (Decision FinalAllow)
                      then Just (let {
                                   (xa, y) = x;
                                 } in (ipv4addr_toString xa,
ipv4addr_toString y))
                      else Nothing))
                  (all_pairs r)));

access_matrix_pretty_ipv4 ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty_ipv4 = access_matrix_pretty_ipv4_code;

access_matrix_pretty_ipv6_code ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty_ipv6_code c rs =
  (if not (all (\ m ->
                 equal_iface (iiface (match_sel m)) ifaceAny &&
                   equal_iface (oiface (match_sel m)) ifaceAny)
            rs)
    then error "undefined"
    else let {
           w = build_ip_partition c rs;
           r = map getOneIp w;
           _ = all_pairs r;
         } in (zip (map ipv6addr_toString r)
                 (map ipv6addr_wordinterval_toString w),
                map_filter
                  (\ x ->
                    (if let {
                          (s, d) = x;
                        } in equal_state (runFw s d c rs) (Decision FinalAllow)
                      then Just (let {
                                   (xa, y) = x;
                                 } in (ipv6addr_toString xa,
ipv6addr_toString y))
                      else Nothing))
                  (all_pairs r)));

access_matrix_pretty_ipv6 ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty_ipv6 = access_matrix_pretty_ipv6_code;

simple_action_toString :: Simple_action -> [Prelude.Char];
simple_action_toString Accepta = "ACCEPT";
simple_action_toString Dropa = "DROP";

action_toString :: Action -> [Prelude.Char];
action_toString Accept = "-j ACCEPT";
action_toString Drop = "-j DROP";
action_toString Reject = "-j REJECT";
action_toString (Call target) = "-j " ++ target ++ " (call)";
action_toString (Goto target) = "-g " ++ target;
action_toString Empty = [];
action_toString Log = "-j LOG";
action_toString Return = "-j RETURN";
action_toString Unknown = "!!!!!!!!!!! UNKNOWN !!!!!!!!!!!";

match_tcp_flags_conjunct :: Ipt_tcp_flags -> Ipt_tcp_flags -> Ipt_tcp_flags;
match_tcp_flags_conjunct (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) =
  (if less_eq_set c1 fmask1 &&
        less_eq_set c2 fmask2 &&
          equal_set (inf_set (inf_set fmask1 fmask2) c1)
            (inf_set (inf_set fmask1 fmask2) c2)
    then TCP_Flags (sup_set fmask1 fmask2) (sup_set c1 c2)
    else ipt_tcp_flags_NoMatch);

match_tcp_flags_conjunct_option ::
  Ipt_tcp_flags -> Ipt_tcp_flags -> Maybe Ipt_tcp_flags;
match_tcp_flags_conjunct_option f1 f2 =
  let {
    (TCP_Flags fmask c) = match_tcp_flags_conjunct f1 f2;
  } in (if less_eq_set c fmask then Just (TCP_Flags fmask c) else Nothing);

ipt_tcp_flags_assume_flag ::
  forall a.
    (Len a) => Ipt_tcp_flags ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
ipt_tcp_flags_assume_flag flg (Match (L4_Flags x)) =
  (if ipt_tcp_flags_equal x flg then MatchAny
    else (case match_tcp_flags_conjunct_option x flg of {
           Nothing -> MatchNot MatchAny;
           Just f3 -> Match (L4_Flags f3);
         }));
ipt_tcp_flags_assume_flag flg (Match (Src v)) = Match (Src v);
ipt_tcp_flags_assume_flag flg (Match (Dst v)) = Match (Dst v);
ipt_tcp_flags_assume_flag flg (Match (IIface v)) = Match (IIface v);
ipt_tcp_flags_assume_flag flg (Match (OIface v)) = Match (OIface v);
ipt_tcp_flags_assume_flag flg (Match (Prot v)) = Match (Prot v);
ipt_tcp_flags_assume_flag flg (Match (Src_Ports v)) = Match (Src_Ports v);
ipt_tcp_flags_assume_flag flg (Match (Dst_Ports v)) = Match (Dst_Ports v);
ipt_tcp_flags_assume_flag flg (Match (CT_State v)) = Match (CT_State v);
ipt_tcp_flags_assume_flag flg (Match (Extra v)) = Match (Extra v);
ipt_tcp_flags_assume_flag flg (MatchNot m) =
  MatchNot (ipt_tcp_flags_assume_flag flg m);
ipt_tcp_flags_assume_flag uu MatchAny = MatchAny;
ipt_tcp_flags_assume_flag flg (MatchAnd m1 m2) =
  MatchAnd (ipt_tcp_flags_assume_flag flg m1)
    (ipt_tcp_flags_assume_flag flg m2);

ipt_tcp_flags_assume_syn ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
ipt_tcp_flags_assume_syn =
  optimize_matches (ipt_tcp_flags_assume_flag ipt_tcp_syn);

ctstate_assume_state ::
  forall a.
    (Len a) => Ctstate ->
                 Match_expr (Common_primitive a) ->
                   Match_expr (Common_primitive a);
ctstate_assume_state s (Match (CT_State x)) =
  (if member s x then MatchAny else MatchNot MatchAny);
ctstate_assume_state s (Match (Src v)) = Match (Src v);
ctstate_assume_state s (Match (Dst v)) = Match (Dst v);
ctstate_assume_state s (Match (IIface v)) = Match (IIface v);
ctstate_assume_state s (Match (OIface v)) = Match (OIface v);
ctstate_assume_state s (Match (Prot v)) = Match (Prot v);
ctstate_assume_state s (Match (Src_Ports v)) = Match (Src_Ports v);
ctstate_assume_state s (Match (Dst_Ports v)) = Match (Dst_Ports v);
ctstate_assume_state s (Match (L4_Flags v)) = Match (L4_Flags v);
ctstate_assume_state s (Match (Extra v)) = Match (Extra v);
ctstate_assume_state s (MatchNot m) = MatchNot (ctstate_assume_state s m);
ctstate_assume_state uu MatchAny = MatchAny;
ctstate_assume_state s (MatchAnd m1 m2) =
  MatchAnd (ctstate_assume_state s m1) (ctstate_assume_state s m2);

ctstate_assume_new ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
ctstate_assume_new = optimize_matches (ctstate_assume_state CT_New);

packet_assume_new ::
  forall a.
    (Len a) => [Rule (Common_primitive a)] -> [Rule (Common_primitive a)];
packet_assume_new = ctstate_assume_new . ipt_tcp_flags_assume_syn;

routing_action_update ::
  forall a b.
    (Len a) => (Routing_action_ext a () -> Routing_action_ext a ()) ->
                 Routing_rule_ext a b -> Routing_rule_ext a b;
routing_action_update routing_actiona
  (Routing_rule_ext routing_match metric routing_action more) =
  Routing_rule_ext routing_match metric (routing_actiona routing_action) more;

output_iface_update ::
  forall a b.
    ([Prelude.Char] -> [Prelude.Char]) ->
      Routing_action_ext a b -> Routing_action_ext a b;
output_iface_update output_ifacea
  (Routing_action_ext output_iface next_hop more) =
  Routing_action_ext (output_ifacea output_iface) next_hop more;

routing_action_oiface_update ::
  forall a.
    (Len a) => [Prelude.Char] -> Routing_rule_ext a () -> Routing_rule_ext a ();
routing_action_oiface_update h pk =
  routing_action_update (output_iface_update (\ _ -> h)) pk;

simple_rule_ipv4_toString ::
  Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
simple_rule_ipv4_toString
  (SimpleRule (Simple_match_ext iif oif sip dip p sps dps ()) a) =
  simple_action_toString a ++
    "     " ++
      protocol_toString p ++
        "  --  " ++
          ipv4_cidr_toString sip ++
            "            " ++
              ipv4_cidr_toString dip ++
                " " ++
                  iface_toString "in: " iif ++
                    " " ++
                      iface_toString "out: " oif ++
                        " " ++
                          ports_toString "sports: " sps ++
                            " " ++ ports_toString "dports: " dps;

simple_rule_ipv6_toString ::
  Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) ->
    [Prelude.Char];
simple_rule_ipv6_toString
  (SimpleRule (Simple_match_ext iif oif sip dip p sps dps ()) a) =
  simple_action_toString a ++
    "     " ++
      protocol_toString p ++
        "  --  " ++
          ipv6_cidr_toString sip ++
            "            " ++
              ipv6_cidr_toString dip ++
                " " ++
                  iface_toString "in: " iif ++
                    " " ++
                      iface_toString "out: " oif ++
                        " " ++
                          ports_toString "sports: " sps ++
                            " " ++ ports_toString "dports: " dps;

next_hop_update ::
  forall a b.
    (Maybe (Word a) -> Maybe (Word a)) ->
      Routing_action_ext a b -> Routing_action_ext a b;
next_hop_update next_hopa (Routing_action_ext output_iface next_hop more) =
  Routing_action_ext output_iface (next_hopa next_hop) more;

routing_action_next_hop_update ::
  forall a. (Len a) => Word a -> Routing_rule_ext a () -> Routing_rule_ext a ();
routing_action_next_hop_update h pk =
  routing_action_update
    (\ _ -> next_hop_update (\ _ -> Just h) (routing_action pk)) pk;

abstract_for_simple_firewall ::
  forall a.
    (Len a) => Match_expr (Common_primitive a) ->
                 Match_expr (Common_primitive a);
abstract_for_simple_firewall =
  abstract_primitive
    (\ a ->
      (case a of {
        Pos aa -> is_CT_State aa || is_L4_Flags aa;
        Neg aa ->
          is_Iiface aa ||
            (is_Oiface aa ||
              (is_Prot aa || (is_CT_State aa || is_L4_Flags aa)));
      }));

ipt_ipv4range_toString ::
  Ipt_iprange (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
ipt_ipv4range_toString (IpAddr ip) = ipv4addr_toString ip;
ipt_ipv4range_toString (IpAddrNetmask ip n) =
  ipv4addr_toString ip ++ "/" ++ string_of_nat n;
ipt_ipv4range_toString (IpAddrRange ip1 ip2) =
  ipv4addr_toString ip1 ++ "-" ++ ipv4addr_toString ip2;

ipt_ipv6range_toString ::
  Ipt_iprange (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) ->
    [Prelude.Char];
ipt_ipv6range_toString (IpAddr ip) = ipv6addr_toString ip;
ipt_ipv6range_toString (IpAddrNetmask ip n) =
  ipv6addr_toString ip ++ "/" ++ string_of_nat n;
ipt_ipv6range_toString (IpAddrRange ip1 ip2) =
  ipv6addr_toString ip1 ++ "-" ++ ipv6addr_toString ip2;

common_primitive_ipv4_toString ::
  Common_primitive (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
common_primitive_ipv4_toString = common_primitive_toString ipv4addr_toString;

common_primitive_ipv6_toString ::
  Common_primitive (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))))) ->
    [Prelude.Char];
common_primitive_ipv6_toString = common_primitive_toString ipv6addr_toString;

to_simple_firewall_without_interfaces ::
  forall a.
    (Len a) => [(Iface, [(Word a, Nat)])] ->
                 Maybe [Routing_rule_ext a ()] ->
                   [Rule (Common_primitive a)] -> [Simple_rule a];
to_simple_firewall_without_interfaces ipassmt rtblo rs =
  to_simple_firewall
    (upper_closure
      (optimize_matches
        (abstract_primitive (\ a -> (case a of {
                                      Pos aa -> is_Iiface aa || is_Oiface aa;
                                      Neg aa -> is_Iiface aa || is_Oiface aa;
                                    })))
        (optimize_matches abstract_for_simple_firewall
          (upper_closure
            (iface_try_rewrite ipassmt rtblo
              (upper_closure (packet_assume_new rs)))))));

common_primitive_match_expr_toString ::
  forall a.
    (Common_primitive a -> [Prelude.Char]) ->
      Match_expr (Common_primitive a) -> [Prelude.Char];
common_primitive_match_expr_toString toStr MatchAny = [];
common_primitive_match_expr_toString toStr (Match m) = toStr m;
common_primitive_match_expr_toString toStr (MatchAnd m1 m2) =
  common_primitive_match_expr_toString toStr m1 ++
    " " ++ common_primitive_match_expr_toString toStr m2;
common_primitive_match_expr_toString toStr (MatchNot (Match m)) =
  "! " ++ toStr m;
common_primitive_match_expr_toString toStr (MatchNot (MatchNot v)) =
  "NOT (" ++ common_primitive_match_expr_toString toStr (MatchNot v) ++ ")";
common_primitive_match_expr_toString toStr (MatchNot (MatchAnd v va)) =
  "NOT (" ++ common_primitive_match_expr_toString toStr (MatchAnd v va) ++ ")";
common_primitive_match_expr_toString toStr (MatchNot MatchAny) =
  "NOT (" ++ common_primitive_match_expr_toString toStr MatchAny ++ ")";

common_primitive_match_expr_ipv4_toString ::
  Match_expr (Common_primitive (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))) ->
    [Prelude.Char];
common_primitive_match_expr_ipv4_toString =
  common_primitive_match_expr_toString common_primitive_ipv4_toString;

common_primitive_match_expr_ipv6_toString ::
  Match_expr
    (Common_primitive (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))))) ->
    [Prelude.Char];
common_primitive_match_expr_ipv6_toString =
  common_primitive_match_expr_toString common_primitive_ipv6_toString;

}
