{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Network.IPTables.Generated(Int, Num, Nat(..), Set, Word, Len, Iface(..), Bit0,
                              Num1, Protocol(..), Tcp_flag(..), Match_expr(..),
                              Action(..), Rule(..), Ctstate(..),
                              Ipt_ipv4range(..), Ipt_tcp_flags(..), Nibble,
                              Common_primitive(..), Wordinterval,
                              Negation_type(..), Simple_match_ext,
                              Simple_action(..), Simple_rule,
                              Parts_connection_ext, tcp, udp, icmp, alist_and,
                              mk_Set, dotteddecimal_toString, ipv4addr_toString,
                              ipassmt_sanity_defined, debug_ipassmt,
                              map_of_ipassmt, to_ipassmt, ipassmt_generic,
                              optimize_matches, upper_closure, word_to_nat,
                              word_less_eq, no_spoofing_iface, nat_to_8word,
                              sanity_wf_ruleset, map_of_string, nat_to_16word,
                              compress_parsed_extra, integer_to_16word,
                              rewrite_Goto_safe, access_matrix_pretty,
                              common_primitive_toString,
                              mk_parts_connection_TCP, to_simple_firewall,
                              ipv4_cidr_toString, simple_rule_toString,
                              unfold_ruleset_CHAIN_safe, action_toString,
                              packet_assume_new, abstract_for_simple_firewall,
                              to_simple_firewall_without_interfaces,
                              common_primitive_match_expr_toString)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

newtype Int = Int_of_integer Integer;

data Num = One | Bit0 Num | Bit1 Num;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

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

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

instance One Nat where {
  one = one_nat;
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

instance Times Nat where {
  times = times_nat;
};

instance Power Nat where {
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Nat where {
};

instance Order Nat where {
};

class (Order a) => Linorder a where {
};

instance Linorder Nat where {
};

data Set a = Set [a] | Coset [a];

top_set :: forall a. Set a;
top_set = Coset [];

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

data Itself a = Type;

class Len0 a where {
  len_of :: Itself a -> Nat;
};

newtype Word a = Word Int;

class (Len0 a) => Len a where {
};

enum_all_word :: forall a. (Len a) => (Word a -> Bool) -> Bool;
enum_all_word p = ball top_set p;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

enum_ex_word :: forall a. (Len a) => (Word a -> Bool) -> Bool;
enum_ex_word p = bex top_set p;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

numeral :: forall a. (Numeral a) => Num -> a;
numeral (Bit1 n) = let {
                     m = numeral n;
                   } in plus (plus m m) one;
numeral (Bit0 n) = let {
                     m = numeral n;
                   } in plus m m;
numeral One = one;

class Zero a where {
  zero :: a;
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

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

mod_integer :: Integer -> Integer -> Integer;
mod_integer k l = snd (divmod_integer k l);

mod_nat :: Nat -> Nat -> Nat;
mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n = (divide_nat m n, mod_nat m n);

class (Times a) => Semigroup_mult a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

of_nat :: forall a. (Semiring_1 a) => Nat -> a;
of_nat n =
  (if equal_nat n zero_nat then zero
    else let {
           (m, q) = divmod_nat n (nat_of_integer (2 :: Integer));
           ma = times (numeral (Bit0 One)) (of_nat m);
         } in (if equal_nat q zero_nat then ma else plus ma one));

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

mod_int :: Int -> Int -> Int;
mod_int k l =
  Int_of_integer (mod_integer (integer_of_int k) (integer_of_int l));

word_of_int :: forall a. (Len0 a) => Int -> Word a;
word_of_int k =
  Word (mod_int k
         (power (Int_of_integer (2 :: Integer))
           ((len_of :: Itself a -> Nat) Type)));

uint :: forall a. (Len0 a) => Word a -> Int;
uint (Word x) = x;

times_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
times_word a b = word_of_int (times_int (uint a) (uint b));

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

zero_word :: forall a. (Len0 a) => Word a;
zero_word = word_of_int zero_int;

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

plus_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
plus_word a b = word_of_int (plus_int (uint a) (uint b));

one_word :: forall a. (Len0 a) => Word a;
one_word = word_of_int (Int_of_integer (1 :: Integer));

instance (Len0 a) => Times (Word a) where {
  times = times_word;
};

instance (Len0 a) => Semigroup_mult (Word a) where {
};

instance (Len0 a) => One (Word a) where {
  one = one_word;
};

instance (Len0 a) => Power (Word a) where {
};

instance (Len0 a) => Monoid_mult (Word a) where {
};

instance (Len0 a) => Plus (Word a) where {
  plus = plus_word;
};

instance (Len0 a) => Semigroup_add (Word a) where {
};

instance (Len0 a) => Ab_semigroup_add (Word a) where {
};

instance (Len0 a) => Semiring (Word a) where {
};

instance (Len0 a) => Numeral (Word a) where {
};

instance (Len a) => Semiring_numeral (Word a) where {
};

instance (Len0 a) => Zero (Word a) where {
  zero = zero_word;
};

instance (Len a) => Zero_neq_one (Word a) where {
};

instance (Len0 a) => Monoid_add (Word a) where {
};

instance (Len0 a) => Comm_monoid_add (Word a) where {
};

instance (Len0 a) => Mult_zero (Word a) where {
};

instance (Len0 a) => Semiring_0 (Word a) where {
};

instance (Len a) => Semiring_1 (Word a) where {
};

enum_word :: forall a. (Len a) => [Word a];
enum_word =
  map of_nat
    (upt zero_nat
      (power (nat_of_integer (2 :: Integer))
        ((len_of :: Itself a -> Nat) Type)));

class Finite a where {
};

class (Finite a) => Enum a where {
  enum :: [a];
  enum_all :: (a -> Bool) -> Bool;
  enum_ex :: (a -> Bool) -> Bool;
};

instance (Len0 a) => Finite (Word a) where {
};

instance (Len a) => Enum (Word a) where {
  enum = enum_word;
  enum_all = enum_all_word;
  enum_ex = enum_ex_word;
};

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

equal_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
equal_word k l = equal_int (uint k) (uint l);

instance (Len0 a) => Eq (Word a) where {
  a == b = equal_word a b;
};

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

less_eq_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
less_eq_word a b = less_eq_int (uint a) (uint b);

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

less_word :: forall a. (Len0 a) => Word a -> Word a -> Bool;
less_word a b = less_int (uint a) (uint b);

instance (Len0 a) => Ord (Word a) where {
  less_eq = less_eq_word;
  less = less_word;
};

instance (Len0 a) => Preorder (Word a) where {
};

instance (Len0 a) => Order (Word a) where {
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

data Ipt_ipv4range = Ip4Addr (Nat, (Nat, (Nat, Nat)))
  | Ip4AddrNetmask (Nat, (Nat, (Nat, Nat))) Nat
  | Ip4AddrRange (Nat, (Nat, (Nat, Nat))) (Nat, (Nat, (Nat, Nat)));

equal_ipt_ipv4range :: Ipt_ipv4range -> Ipt_ipv4range -> Bool;
equal_ipt_ipv4range (Ip4AddrNetmask x21 x22) (Ip4AddrRange x31 x32) = False;
equal_ipt_ipv4range (Ip4AddrRange x31 x32) (Ip4AddrNetmask x21 x22) = False;
equal_ipt_ipv4range (Ip4Addr x1) (Ip4AddrRange x31 x32) = False;
equal_ipt_ipv4range (Ip4AddrRange x31 x32) (Ip4Addr x1) = False;
equal_ipt_ipv4range (Ip4Addr x1) (Ip4AddrNetmask x21 x22) = False;
equal_ipt_ipv4range (Ip4AddrNetmask x21 x22) (Ip4Addr x1) = False;
equal_ipt_ipv4range (Ip4AddrRange x31 x32) (Ip4AddrRange y31 y32) =
  x31 == y31 && x32 == y32;
equal_ipt_ipv4range (Ip4AddrNetmask x21 x22) (Ip4AddrNetmask y21 y22) =
  x21 == y21 && equal_nat x22 y22;
equal_ipt_ipv4range (Ip4Addr x1) (Ip4Addr y1) = x1 == y1;

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

data Common_primitive = Src Ipt_ipv4range | Dst Ipt_ipv4range | IIface Iface
  | OIface Iface | Prot Protocol
  | Src_Ports
      [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
         Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))]
  | Dst_Ports
      [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
         Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))]
  | L4_Flags Ipt_tcp_flags | CT_State (Set Ctstate) | Extra [Prelude.Char];

equal_common_primitive :: Common_primitive -> Common_primitive -> Bool;
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
equal_common_primitive (Dst_Ports x7) (Dst_Ports y7) = x7 == y7;
equal_common_primitive (Src_Ports x6) (Src_Ports y6) = x6 == y6;
equal_common_primitive (Prot x5) (Prot y5) = equal_protocol x5 y5;
equal_common_primitive (OIface x4) (OIface y4) = equal_iface x4 y4;
equal_common_primitive (IIface x3) (IIface y3) = equal_iface x3 y3;
equal_common_primitive (Dst x2) (Dst y2) = equal_ipt_ipv4range x2 y2;
equal_common_primitive (Src x1) (Src y1) = equal_ipt_ipv4range x1 y1;

instance Eq Common_primitive where {
  a == b = equal_common_primitive a b;
};

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

data Simple_packet_ext a b =
  Simple_packet_ext [Prelude.Char] [Prelude.Char] (Word a) (Word a)
    (Word (Bit0 (Bit0 (Bit0 Num1)))) (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) (Set Tcp_flag) Ctstate b;

data Parts_connection_ext a =
  Parts_connection_ext [Prelude.Char] [Prelude.Char]
    (Word (Bit0 (Bit0 (Bit0 Num1)))) (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) Ctstate a;

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

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

bit :: Int -> Bool -> Int;
bit k b =
  plus_int (plus_int (if b then Int_of_integer (1 :: Integer) else zero_int) k)
    k;

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

splice :: forall a. [a] -> [a] -> [a];
splice (x : xs) (y : ys) = x : y : splice xs ys;
splice [] ys = ys;
splice xs [] = xs;

collect :: forall a. (Enum a) => (a -> Bool) -> Set a;
collect p = Set (filter p enum);

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

product :: forall a b. [a] -> [b] -> [(a, b)];
product [] uu = [];
product (x : xs) ys = map (\ a -> (x, a)) ys ++ product xs ys;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

tcp :: Word (Bit0 (Bit0 (Bit0 Num1)));
tcp = word_of_int (Int_of_integer (6 :: Integer));

udp :: Word (Bit0 (Bit0 (Bit0 Num1)));
udp = word_of_int (Int_of_integer (17 :: Integer));

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

bin_rest :: Int -> Int;
bin_rest w = divide_int w (Int_of_integer (2 :: Integer));

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

icmp :: Word (Bit0 (Bit0 (Bit0 Num1)));
icmp = one_word;

sctp :: Word (Bit0 (Bit0 (Bit0 Num1)));
sctp = word_of_int (Int_of_integer (132 :: Integer));

max_word :: forall a. (Len a) => Word a;
max_word =
  word_of_int
    (minus_int
      (power (Int_of_integer (2 :: Integer)) ((len_of :: Itself a -> Nat) Type))
      (Int_of_integer (1 :: Integer)));

ifaceAny :: Iface;
ifaceAny = Iface "+";

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

pfxes :: forall a. (Len0 a) => Itself a -> [Nat];
pfxes uu =
  map nat (upto zero_int (int_of_nat ((len_of :: Itself a -> Nat) Type)));

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

merge :: forall a. (Eq a, Linorder a) => [a] -> [a] -> [a];
merge [] l2 = l2;
merge (v : va) [] = v : va;
merge (x1 : l1) (x2 : l2) =
  (if less x1 x2 then x1 : merge l1 (x2 : l2)
    else (if x1 == x2 then x1 : merge l1 l2 else x2 : merge (x1 : l1) l2));

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

alist_and :: forall a. [Negation_type a] -> Match_expr a;
alist_and [] = MatchAny;
alist_and [Pos e] = Match e;
alist_and [Neg e] = MatchNot (Match e);
alist_and (Pos e : v : va) = MatchAnd (Match e) (alist_and (v : va));
alist_and (Neg e : v : va) = MatchAnd (MatchNot (Match e)) (alist_and (v : va));

br2l :: forall a. (Len0 a) => Wordinterval a -> [(Word a, Word a)];
br2l (RangeUnion r1 r2) = br2l r1 ++ br2l r2;
br2l (WordInterval s e) = (if less_word e s then [] else [(s, e)]);

empty_WordInterval :: forall a. (Len a) => Wordinterval a;
empty_WordInterval = WordInterval one_word zero_word;

l2br :: forall a. (Len a) => [(Word a, Word a)] -> Wordinterval a;
l2br [] = empty_WordInterval;
l2br [(s, e)] = WordInterval s e;
l2br ((s, e) : v : va) = RangeUnion (WordInterval s e) (l2br (v : va));

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

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

word_prev :: forall a. (Len a) => Word a -> Word a;
word_prev a =
  (if equal_word a zero_word then zero_word else minus_word a one_word);

word_next :: forall a. (Len a) => Word a -> Word a;
word_next a =
  (if equal_word a max_word then max_word else plus_word a one_word);

wordinterval_setminusa ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_setminusa (WordInterval s e) (WordInterval ms me) =
  (if less_word e s || less_word me ms then WordInterval s e
    else (if less_eq_word e me
           then WordInterval (if equal_word ms zero_word then one_word else s)
                  (min e (word_prev ms))
           else (if less_eq_word ms s
                  then WordInterval (max s (word_next me))
                         (if equal_word me max_word then zero_word else e)
                  else RangeUnion
                         (WordInterval
                           (if equal_word ms zero_word then one_word else s)
                           (word_prev ms))
                         (WordInterval (word_next me)
                           (if equal_word me max_word then zero_word
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
  l2br (remdups
         (listwordinterval_adjacent
           (listwordinterval_compress
             (br2l (wordinterval_optimize_empty2 r)))));

wordinterval_setminus ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_setminus r1 r2 =
  wordinterval_compress (wordinterval_setminusa r1 r2);

wordinterval_UNIV :: forall a. (Len a) => Wordinterval a;
wordinterval_UNIV = WordInterval zero_word max_word;

wordinterval_invert :: forall a. (Len a) => Wordinterval a -> Wordinterval a;
wordinterval_invert r = wordinterval_setminus wordinterval_UNIV r;

ports_invert ::
  [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
     Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
ports_invert ps = br2l (wordinterval_invert (l2br ps));

char_of_nat :: Nat -> Prelude.Char;
char_of_nat =
  (let chr k | (0 <= k && k < 256) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger) .
    integer_of_nat;

mk_Set :: forall a. [a] -> Set a;
mk_Set = Set;

is_pos_Extra :: Negation_type Common_primitive -> Bool;
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

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

bitNOT_int :: Int -> Int;
bitNOT_int = (\ x -> minus_int (uminus_int x) (Int_of_integer (1 :: Integer)));

bin_last :: Int -> Bool;
bin_last w =
  equal_int (mod_int w (Int_of_integer (2 :: Integer)))
    (Int_of_integer (1 :: Integer));

bitAND_int :: Int -> Int -> Int;
bitAND_int x y =
  (if equal_int x zero_int then zero_int
    else (if equal_int x (uminus_int (Int_of_integer (1 :: Integer))) then y
           else bit (bitAND_int (bin_rest x) (bin_rest y))
                  (bin_last x && bin_last y)));

bitOR_int :: Int -> Int -> Int;
bitOR_int = (\ x y -> bitNOT_int (bitAND_int (bitNOT_int x) (bitNOT_int y)));

bitOR_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
bitOR_word a b = word_of_int (bitOR_int (uint a) (uint b));

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

bitAND_word :: forall a. (Len0 a) => Word a -> Word a -> Word a;
bitAND_word a b = word_of_int (bitAND_int (uint a) (uint b));

valid_prefix :: forall a. (Len a) => Prefix_match a -> Bool;
valid_prefix pf =
  equal_word (bitAND_word (pfxm_mask pf) (pfxm_prefix pf)) zero_word;

wordinterval_CIDR_split1_2 ::
  forall a.
    (Len a) => Wordinterval a -> (Maybe (Prefix_match a), Wordinterval a);
wordinterval_CIDR_split1_2 r =
  let {
    a = wordinterval_lowest_element r;
  } in (case a of {
         Nothing -> (Nothing, r);
         Just aa ->
           let {
             cs = map (PrefixMatch aa) ((pfxes :: Itself a -> [Nat]) Type);
             ms = filter
                    (\ s ->
                      valid_prefix s &&
                        wordinterval_subset (prefix_to_wordinterval s) r)
                    cs;
           } in (Just (hd ms),
                  wordinterval_setminus r (prefix_to_wordinterval (hd ms)));
       });

wordinterval_CIDR_split1 ::
  forall a.
    (Len a) => Wordinterval a -> (Maybe (Prefix_match a), Wordinterval a);
wordinterval_CIDR_split1 s = wordinterval_CIDR_split1_2 s;

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

pc_tag_ctstate :: forall a. Parts_connection_ext a -> Ctstate;
pc_tag_ctstate
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_tag_ctstate;

pc_oiface :: forall a. Parts_connection_ext a -> [Prelude.Char];
pc_oiface
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_oiface;

pc_iiface :: forall a. Parts_connection_ext a -> [Prelude.Char];
pc_iiface
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_iiface;

pc_sport ::
  forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
pc_sport
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_sport;

pc_proto :: forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 Num1)));
pc_proto
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_proto;

pc_dport ::
  forall a. Parts_connection_ext a -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
pc_dport
  (Parts_connection_ext pc_iiface pc_oiface pc_proto pc_sport pc_dport
    pc_tag_ctstate more)
  = pc_dport;

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

p_oiface :: forall a b. (Len a) => Simple_packet_ext a b -> [Prelude.Char];
p_oiface
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_tag_ctstate more)
  = p_oiface;

p_iiface :: forall a b. (Len a) => Simple_packet_ext a b -> [Prelude.Char];
p_iiface
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_tag_ctstate more)
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
    p_tcp_flags p_tag_ctstate more)
  = p_sport;

p_proto ::
  forall a b.
    (Len a) => Simple_packet_ext a b -> Word (Bit0 (Bit0 (Bit0 Num1)));
p_proto
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_tag_ctstate more)
  = p_proto;

p_dport ::
  forall a b.
    (Len a) => Simple_packet_ext a b -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
p_dport
  (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
    p_tcp_flags p_tag_ctstate more)
  = p_dport;

src :: forall a b. (Len a) => Simple_match_ext a b -> (Word a, Nat);
src (Simple_match_ext iiface oiface src dst proto sports dports more) = src;

dst :: forall a b. (Len a) => Simple_match_ext a b -> (Word a, Nat);
dst (Simple_match_ext iiface oiface src dst proto sports dports more) = dst;

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
        p_tcp_flags p_tag_ctstate more)
  = p_src;

p_dst :: forall a b. (Len a) => Simple_packet_ext a b -> Word a;
p_dst (Simple_packet_ext p_iiface p_oiface p_src p_dst p_proto p_sport p_dport
        p_tcp_flags p_tag_ctstate more)
  = p_dst;

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
      (pc_dport c) (insert TCP_SYN bot_set) (pc_tag_ctstate c) ());

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

merge_list :: forall a. (Eq a, Linorder a) => [[a]] -> [[a]] -> [a];
merge_list [] [] = [];
merge_list [] [l] = l;
merge_list (la : acc2) [] = merge_list [] (la : acc2);
merge_list (la : acc2) [l] = merge_list [] (l : la : acc2);
merge_list acc2 (l1 : l2 : ls) = merge_list (merge l1 l2 : acc2) ls;

getNeg :: forall a. [Negation_type a] -> [a];
getNeg [] = [];
getNeg (Neg x : xs) = x : getNeg xs;
getNeg (Pos v : xs) = getNeg xs;

getPos :: forall a. [Negation_type a] -> [a];
getPos [] = [];
getPos (Pos x : xs) = x : getPos xs;
getPos (Neg v : xs) = getPos xs;

get_pos_Extra :: Negation_type Common_primitive -> [Prelude.Char];
get_pos_Extra a = let {
                    (Pos (Extra e)) = a;
                  } in e;

ipt_tcp_syn :: Ipt_tcp_flags;
ipt_tcp_syn =
  TCP_Flags
    (insert TCP_SYN (insert TCP_RST (insert TCP_ACK (insert TCP_FIN bot_set))))
    (insert TCP_SYN bot_set);

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

shiftr_word :: forall a. (Len0 a) => Word a -> Nat -> Word a;
shiftr_word w n = funpow n shiftr1 w;

nat_of_ipv4addr :: Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> Nat;
nat_of_ipv4addr a = unat a;

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

wordinterval_eq ::
  forall a. (Len a) => Wordinterval a -> Wordinterval a -> Bool;
wordinterval_eq r1 r2 = wordinterval_subset r1 r2 && wordinterval_subset r2 r1;

ipcidr_to_interval_start :: forall a. (Len a) => (Word a, Nat) -> Word a;
ipcidr_to_interval_start (pre, len) =
  let {
    netmask =
      shiftl_word (mask len) (minus_nat ((len_of :: Itself a -> Nat) Type) len);
    network_prefix = bitAND_word pre netmask;
  } in network_prefix;

bitNOT_word :: forall a. (Len0 a) => Word a -> Word a;
bitNOT_word a = word_of_int (bitNOT_int (uint a));

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

ipassmt_ignore_wildcard_list ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])];
ipassmt_ignore_wildcard_list ipassmt =
  filter
    (\ (_, ips) ->
      not (wordinterval_eq (l2br (map ipcidr_to_interval ips))
            wordinterval_UNIV))
    ipassmt;

wordinterval_union ::
  forall a. (Len0 a) => Wordinterval a -> Wordinterval a -> Wordinterval a;
wordinterval_union r1 r2 = RangeUnion r1 r2;

wordinterval_Union :: forall a. (Len a) => [Wordinterval a] -> Wordinterval a;
wordinterval_Union ws =
  wordinterval_compress (foldr wordinterval_union ws empty_WordInterval);

mergesort_remdups :: forall a. (Eq a, Linorder a) => [a] -> [a];
mergesort_remdups xs = merge_list [] (map (\ x -> [x]) xs);

oiface_sel :: Common_primitive -> Iface;
oiface_sel (OIface x4) = x4;

iiface_sel :: Common_primitive -> Iface;
iiface_sel (IIface x3) = x3;

is_Oiface :: Common_primitive -> Bool;
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

is_Iiface :: Common_primitive -> Bool;
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

collect_ifacesa :: [Rule Common_primitive] -> [Iface];
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

collect_ifaces :: [Rule Common_primitive] -> [Iface];
collect_ifaces rs = mergesort_remdups (collect_ifacesa rs);

ipassmt_sanity_defined ::
  [Rule Common_primitive] ->
    (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
      Bool;
ipassmt_sanity_defined rs ipassmt =
  all (\ iface -> not (is_none (ipassmt iface))) (collect_ifaces rs);

list_separated_toString ::
  forall a. [Prelude.Char] -> (a -> [Prelude.Char]) -> [a] -> [Prelude.Char];
list_separated_toString sep toStr ls =
  concat
    (splice (map toStr ls) (replicate (minus_nat (size_list ls) one_nat) sep));

list_toString :: forall a. (a -> [Prelude.Char]) -> [a] -> [Prelude.Char];
list_toString toStr ls = "[" ++ list_separated_toString ", " toStr ls ++ "]";

iface_is_wildcard :: Iface -> Bool;
iface_is_wildcard ifce = iface_name_is_wildcard (iface_sel ifce);

debug_ipassmt ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    [Rule Common_primitive] -> [[Prelude.Char]];
debug_ipassmt ipassmt rs =
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
                                       (l2br
 (map ipcidr_to_interval (the (map_of ipassmt i1))))
                                       (l2br
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
                                    (l2br (map ipcidr_to_interval
    (the (map_of ipassmt i1))))
                                    (l2br (map ipcidr_to_interval
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
    (l2br (map ipcidr_to_interval (the (map_of ipassmta i1))))
    (l2br (map ipcidr_to_interval (the (map_of ipassmta i2)))))
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
 (l2br (map ipcidr_to_interval (the (map_of ipassmta i1))))
 (l2br (map ipcidr_to_interval (the (map_of ipassmta i2)))))))
                             (product ifacesa ifacesa))),
         "ipassmt_sanity_complete: " ++
           (if distinct (map fst ipassmt) &&
                 let {
                   range = map snd ipassmt;
                 } in wordinterval_eq
                        (wordinterval_Union
                          (map (l2br . map ipcidr_to_interval) range))
                        wordinterval_UNIV
             then "passed"
             else "the following is not covered: " ++
                    ipv4addr_wordinterval_toString
                      (wordinterval_setminus wordinterval_UNIV
                        (wordinterval_Union
                          (map (l2br . map ipcidr_to_interval)
                            (map snd ipassmt))))),
         "ipassmt_sanity_complete excluding UNIV interfaces: " ++
           let {
             ipassmta = ipassmt_ignore_wildcard_list ipassmt;
           } in (if distinct (map fst ipassmta) &&
                      let {
                        range = map snd ipassmta;
                      } in wordinterval_eq
                             (wordinterval_Union
                               (map (l2br . map ipcidr_to_interval) range))
                             wordinterval_UNIV
                  then "passed"
                  else "the following is not covered: " ++
                         ipv4addr_wordinterval_toString
                           (wordinterval_setminus wordinterval_UNIV
                             (wordinterval_Union
                               (map (l2br . map ipcidr_to_interval)
                                 (map snd ipassmta)))))];

partIps ::
  forall a. (Len a) => Wordinterval a -> [Wordinterval a] -> [Wordinterval a];
partIps uu [] = [];
partIps s (t : ts) =
  (if wordinterval_empty s then t : ts
    else (if wordinterval_empty (wordinterval_intersection s t)
           then t : partIps (wordinterval_setminus s t) ts
           else (if wordinterval_empty (wordinterval_setminus t s)
                  then t : partIps (wordinterval_setminus s t) ts
                  else wordinterval_intersection t s :
                         wordinterval_setminus t s :
                           partIps (wordinterval_setminus s t) ts)));

map_of_ipassmt ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)];
map_of_ipassmt ipassmt =
  (if distinct (map fst ipassmt) &&
        ball (image fst (Set ipassmt))
          (\ iface -> not (iface_is_wildcard iface))
    then map_of ipassmt else error "undefined");

ipv4addr_of_nat :: Nat -> Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4addr_of_nat n = of_nat n;

ipv4addr_of_dotdecimal ::
  (Nat, (Nat, (Nat, Nat))) -> Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4addr_of_dotdecimal (a, (b, (c, d))) =
  ipv4addr_of_nat
    (plus_nat
      (plus_nat (plus_nat d (times_nat (nat_of_integer (256 :: Integer)) c))
        (times_nat (nat_of_integer (65536 :: Integer)) b))
      (times_nat (nat_of_integer (16777216 :: Integer)) a));

ipt_ipv4range_to_interval ::
  Ipt_ipv4range ->
    (Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))));
ipt_ipv4range_to_interval (Ip4Addr addr) =
  (ipv4addr_of_dotdecimal addr, ipv4addr_of_dotdecimal addr);
ipt_ipv4range_to_interval (Ip4AddrNetmask pre len) =
  let {
    netmask =
      shiftl_word (mask len) (minus_nat (nat_of_integer (32 :: Integer)) len);
    network_prefix = bitAND_word (ipv4addr_of_dotdecimal pre) netmask;
  } in (network_prefix, bitOR_word network_prefix (bitNOT_word netmask));
ipt_ipv4range_to_interval (Ip4AddrRange ip1 ip2) =
  (ipv4addr_of_dotdecimal ip1, ipv4addr_of_dotdecimal ip2);

ipv4range_range ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))),
    Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))) ->
    Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4range_range (ip_start, ip_end) = WordInterval ip_start ip_end;

ipt_ipv4range_to_cidr ::
  Ipt_ipv4range -> [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)];
ipt_ipv4range_to_cidr ips =
  cidr_split (ipv4range_range (ipt_ipv4range_to_interval ips));

all_but_those_ips ::
  [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)];
all_but_those_ips cidrips =
  cidr_split (wordinterval_invert (l2br (map ipcidr_to_interval cidrips)));

ipassmt_iprange_translate ::
  Negation_type [Ipt_ipv4range] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)];
ipassmt_iprange_translate (Pos ips) = concatMap ipt_ipv4range_to_cidr ips;
ipassmt_iprange_translate (Neg ips) =
  all_but_those_ips (concatMap ipt_ipv4range_to_cidr ips);

to_ipassmt ::
  [(Iface, Negation_type [Ipt_ipv4range])] ->
    [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])];
to_ipassmt assmt =
  map (\ (ifce, ips) -> (ifce, ipassmt_iprange_translate ips)) assmt;

matchOr :: forall a. Match_expr a -> Match_expr a -> Match_expr a;
matchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2));

iprange_interval :: forall a. (Len a) => (Word a, Word a) -> Wordinterval a;
iprange_interval (ip_start, ip_end) = WordInterval ip_start ip_end;

getOneIp :: forall a. (Len a) => Wordinterval a -> Word a;
getOneIp (WordInterval b uu) = b;
getOneIp (RangeUnion r1 r2) =
  (if wordinterval_empty r1 then getOneIp r2 else getOneIp r1);

partitioningIps ::
  forall a. (Len a) => [Wordinterval a] -> [Wordinterval a] -> [Wordinterval a];
partitioningIps [] ts = ts;
partitioningIps (s : ss) ts = partIps s (partitioningIps ss ts);

ipcidr_tuple_to_wordinterval ::
  forall a. (Len a) => (Word a, Nat) -> Wordinterval a;
ipcidr_tuple_to_wordinterval iprng =
  iprange_interval (ipcidr_to_interval iprng);

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

ipv4range_UNIV :: Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipv4range_UNIV = wordinterval_UNIV;

ipassmt_generic ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])];
ipassmt_generic =
  [(Iface "lo",
     [(ipv4addr_of_dotdecimal
         (nat_of_integer (127 :: Integer), (zero_nat, (zero_nat, zero_nat))),
        nat_of_integer (8 :: Integer))])];

upper_closure_matchexpr ::
  Action -> Match_expr Common_primitive -> Match_expr Common_primitive;
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

alist_anda :: forall a. [Negation_type a] -> Match_expr a;
alist_anda [] = MatchAny;
alist_anda (Pos e : es) = MatchAnd (Match e) (alist_anda es);
alist_anda (Neg e : es) = MatchAnd (MatchNot (Match e)) (alist_anda es);

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
             (alist_anda (negPos_map c (map Pos as_pos ++ map Neg as_neg))) rst)
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
  Match_expr Common_primitive -> Maybe (Match_expr Common_primitive);
compress_normalize_output_interfaces m =
  compress_normalize_primitive (is_Oiface, oiface_sel) OIface
    compress_interfaces m;

compress_normalize_input_interfaces ::
  Match_expr Common_primitive -> Maybe (Match_expr Common_primitive);
compress_normalize_input_interfaces m =
  compress_normalize_primitive (is_Iiface, iiface_sel) IIface
    compress_interfaces m;

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

prot_sel :: Common_primitive -> Protocol;
prot_sel (Prot x5) = x5;

is_Prot :: Common_primitive -> Bool;
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

atLeast :: forall a. (Enum a, Ord a) => a -> Set a;
atLeast l = collect (less_eq l);

atMost :: forall a. (Enum a, Ord a) => a -> Set a;
atMost u = collect (\ x -> less_eq x u);

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

atLeastAtMost :: forall a. (Enum a, Eq a, Ord a) => a -> a -> Set a;
atLeastAtMost l u = inf_set (atLeast l) (atMost u);

compress_protocols ::
  [Negation_type Protocol] -> Maybe ([Protocol], [Protocol]);
compress_protocols ps =
  (case compress_pos_protocols (getPos ps) of {
    Nothing -> Nothing;
    Just proto ->
      (if membera (getNeg ps) ProtoAny ||
            ball (atLeastAtMost zero_word max_word)
              (\ p -> membera (getNeg ps) (Proto p))
        then Nothing
        else (if equal_protocol proto ProtoAny then Just ([], getNeg ps)
               else (if any (\ p ->
                              not (is_none (simple_proto_conjunct proto p)))
                          (getNeg ps)
                      then Nothing else Just ([proto], getNeg ps))));
  });

compress_normalize_protocols ::
  Match_expr Common_primitive -> Maybe (Match_expr Common_primitive);
compress_normalize_protocols m =
  compress_normalize_primitive (is_Prot, prot_sel) Prot compress_protocols m;

compress_normalize_besteffort ::
  Match_expr Common_primitive -> Maybe (Match_expr Common_primitive);
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

src_sel :: Common_primitive -> Ipt_ipv4range;
src_sel (Src x1) = x1;

is_Src :: Common_primitive -> Bool;
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

l2br_negation_type_intersect ::
  forall a. (Len a) => [Negation_type (Word a, Word a)] -> Wordinterval a;
l2br_negation_type_intersect [] = wordinterval_UNIV;
l2br_negation_type_intersect (Pos (s, e) : ls) =
  wordinterval_intersection (WordInterval s e)
    (l2br_negation_type_intersect ls);
l2br_negation_type_intersect (Neg (s, e) : ls) =
  wordinterval_intersection (wordinterval_invert (WordInterval s e))
    (l2br_negation_type_intersect ls);

ipt_ipv4range_negation_type_to_br_intersect ::
  [Negation_type Ipt_ipv4range] ->
    Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
ipt_ipv4range_negation_type_to_br_intersect l =
  l2br_negation_type_intersect (negPos_map ipt_ipv4range_to_interval l);

wi_2_cidr_ipt_ipv4range_list ::
  Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Ipt_ipv4range];
wi_2_cidr_ipt_ipv4range_list r =
  map (\ (base, a) -> Ip4AddrNetmask (dotdecimal_of_ipv4addr base) a)
    (cidr_split r);

ipt_ipv4range_compress :: [Negation_type Ipt_ipv4range] -> [Ipt_ipv4range];
ipt_ipv4range_compress =
  wi_2_cidr_ipt_ipv4range_list . ipt_ipv4range_negation_type_to_br_intersect;

normalize_src_ips ::
  Match_expr Common_primitive -> [Match_expr Common_primitive];
normalize_src_ips =
  normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress;

dst_sel :: Common_primitive -> Ipt_ipv4range;
dst_sel (Dst x2) = x2;

is_Dst :: Common_primitive -> Bool;
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
  Match_expr Common_primitive -> [Match_expr Common_primitive];
normalize_dst_ips =
  normalize_primitive_extract (is_Dst, dst_sel) Dst ipt_ipv4range_compress;

optimize_matches_option ::
  forall a. (Match_expr a -> Maybe (Match_expr a)) -> [Rule a] -> [Rule a];
optimize_matches_option uu [] = [];
optimize_matches_option f (Rule m a : rs) =
  (case f m of {
    Nothing -> optimize_matches_option f rs;
    Just ma -> Rule ma a : optimize_matches_option f rs;
  });

src_ports_sel ::
  Common_primitive ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
src_ports_sel (Src_Ports x6) = x6;

is_Src_Ports :: Common_primitive -> Bool;
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

ipt_ports_negation_type_normalize ::
  Negation_type
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
ipt_ports_negation_type_normalize (Pos ps) = ps;
ipt_ports_negation_type_normalize (Neg ps) = ports_invert ps;

ipt_ports_andlist_compress ::
  forall a. (Len a) => [[(Word a, Word a)]] -> [(Word a, Word a)];
ipt_ports_andlist_compress pss =
  br2l (fold (\ ps -> wordinterval_intersection (l2br ps)) pss
         wordinterval_UNIV);

ipt_ports_compress ::
  [Negation_type
     [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
        Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))]] ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
ipt_ports_compress pss =
  ipt_ports_andlist_compress (map ipt_ports_negation_type_normalize pss);

normalize_ports_step ::
  (Common_primitive -> Bool,
    Common_primitive ->
      [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
         Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))]) ->
    ([(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
        Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
      Common_primitive) ->
      Match_expr Common_primitive -> [Match_expr Common_primitive];
normalize_ports_step disc_sel c =
  normalize_primitive_extract disc_sel c
    (\ me -> map (\ pt -> [pt]) (ipt_ports_compress me));

normalize_src_ports ::
  Match_expr Common_primitive -> [Match_expr Common_primitive];
normalize_src_ports =
  normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports;

dst_ports_sel ::
  Common_primitive ->
    [(Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
       Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
dst_ports_sel (Dst_Ports x7) = x7;

is_Dst_Ports :: Common_primitive -> Bool;
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

normalize_dst_ports ::
  Match_expr Common_primitive -> [Match_expr Common_primitive];
normalize_dst_ports =
  normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports;

normalize_rules ::
  forall a. (Match_expr a -> [Match_expr a]) -> [Rule a] -> [Rule a];
normalize_rules uu [] = [];
normalize_rules f (Rule m a : rs) =
  map (\ ma -> Rule ma a) (f m) ++ normalize_rules f rs;

transform_normalize_primitives ::
  [Rule Common_primitive] -> [Rule Common_primitive];
transform_normalize_primitives =
  (((normalize_rules normalize_dst_ips . normalize_rules normalize_src_ips) .
     normalize_rules normalize_dst_ports) .
    normalize_rules normalize_src_ports) .
    optimize_matches_option compress_normalize_besteffort;

ctstate_is_UNIV :: Set Ctstate -> Bool;
ctstate_is_UNIV c =
  member CT_New c &&
    member CT_Established c &&
      member CT_Related c && member CT_Untracked c && member CT_Invalid c;

optimize_primitive_univ ::
  Match_expr Common_primitive -> Match_expr Common_primitive;
optimize_primitive_univ (Match (IIface iface)) =
  (if equal_iface iface ifaceAny then MatchAny else Match (IIface iface));
optimize_primitive_univ (Match (OIface iface)) =
  (if equal_iface iface ifaceAny then MatchAny else Match (OIface iface));
optimize_primitive_univ (Match (Src_Ports [(s, e)])) =
  (if equal_word s zero_word &&
        equal_word e (word_of_int (Int_of_integer (65535 :: Integer)))
    then MatchAny else Match (Src_Ports [(s, e)]));
optimize_primitive_univ (Match (Dst_Ports [(s, e)])) =
  (if equal_word s zero_word &&
        equal_word e (word_of_int (Int_of_integer (65535 :: Integer)))
    then MatchAny else Match (Dst_Ports [(s, e)]));
optimize_primitive_univ (Match (Prot ProtoAny)) = MatchAny;
optimize_primitive_univ (Match (L4_Flags (TCP_Flags m c))) =
  (if equal_set m bot_set && equal_set c bot_set then MatchAny
    else Match (L4_Flags (TCP_Flags m c)));
optimize_primitive_univ (Match (CT_State ctstate)) =
  (if ctstate_is_UNIV ctstate then MatchAny else Match (CT_State ctstate));
optimize_primitive_univ (Match (Src (Ip4Addr va))) = Match (Src (Ip4Addr va));
optimize_primitive_univ (Match (Src (Ip4AddrRange va vb))) =
  Match (Src (Ip4AddrRange va vb));
optimize_primitive_univ (Match (Dst (Ip4Addr va))) = Match (Dst (Ip4Addr va));
optimize_primitive_univ (Match (Dst (Ip4AddrRange va vb))) =
  Match (Dst (Ip4AddrRange va vb));
optimize_primitive_univ (Match (Prot (Proto va))) = Match (Prot (Proto va));
optimize_primitive_univ (Match (Src_Ports [])) = Match (Src_Ports []);
optimize_primitive_univ (Match (Src_Ports (va : vc : vd))) =
  Match (Src_Ports (va : vc : vd));
optimize_primitive_univ (Match (Dst_Ports [])) = Match (Dst_Ports []);
optimize_primitive_univ (Match (Dst_Ports (va : vc : vd))) =
  Match (Dst_Ports (va : vc : vd));
optimize_primitive_univ (Match (Extra v)) = Match (Extra v);
optimize_primitive_univ (MatchNot m) = MatchNot (optimize_primitive_univ m);
optimize_primitive_univ (MatchAnd m1 m2) =
  MatchAnd (optimize_primitive_univ m1) (optimize_primitive_univ m2);
optimize_primitive_univ MatchAny = MatchAny;
optimize_primitive_univ (Match (Src (Ip4AddrNetmask (ve, (vg, (vi, via))) vc)))
  = (if equal_nat vc zero_nat
      then (if equal_nat via zero_nat
             then (if equal_nat vi zero_nat
                    then (if equal_nat vg zero_nat
                           then (if equal_nat ve zero_nat then MatchAny
                                  else Match
 (Src (Ip4AddrNetmask
        (suc (minus_nat ve one_nat), (zero_nat, (zero_nat, zero_nat)))
        zero_nat)))
                           else Match (Src
(Ip4AddrNetmask (ve, (suc (minus_nat vg one_nat), (zero_nat, zero_nat)))
  zero_nat)))
                    else Match (Src (Ip4AddrNetmask
                                      (ve,
(vg, (suc (minus_nat vi one_nat), zero_nat)))
                                      zero_nat)))
             else Match (Src (Ip4AddrNetmask
                               (ve, (vg, (vi, suc (minus_nat via one_nat))))
                               zero_nat)))
      else Match (Src (Ip4AddrNetmask (ve, (vg, (vi, via)))
                        (suc (minus_nat vc one_nat)))));
optimize_primitive_univ (Match (Dst (Ip4AddrNetmask (ve, (vg, (vi, via))) vc)))
  = (if equal_nat vc zero_nat
      then (if equal_nat via zero_nat
             then (if equal_nat vi zero_nat
                    then (if equal_nat vg zero_nat
                           then (if equal_nat ve zero_nat then MatchAny
                                  else Match
 (Dst (Ip4AddrNetmask
        (suc (minus_nat ve one_nat), (zero_nat, (zero_nat, zero_nat)))
        zero_nat)))
                           else Match (Dst
(Ip4AddrNetmask (ve, (suc (minus_nat vg one_nat), (zero_nat, zero_nat)))
  zero_nat)))
                    else Match (Dst (Ip4AddrNetmask
                                      (ve,
(vg, (suc (minus_nat vi one_nat), zero_nat)))
                                      zero_nat)))
             else Match (Dst (Ip4AddrNetmask
                               (ve, (vg, (vi, suc (minus_nat via one_nat))))
                               zero_nat)))
      else Match (Dst (Ip4AddrNetmask (ve, (vg, (vi, via)))
                        (suc (minus_nat vc one_nat)))));

opt_MatchAny_match_expr :: forall a. Match_expr a -> Match_expr a;
opt_MatchAny_match_expr MatchAny = MatchAny;
opt_MatchAny_match_expr (Match a) = Match a;
opt_MatchAny_match_expr (MatchNot (MatchNot m)) = opt_MatchAny_match_expr m;
opt_MatchAny_match_expr (MatchNot (Match v)) =
  MatchNot (opt_MatchAny_match_expr (Match v));
opt_MatchAny_match_expr (MatchNot (MatchAnd v va)) =
  MatchNot (opt_MatchAny_match_expr (MatchAnd v va));
opt_MatchAny_match_expr (MatchNot MatchAny) =
  MatchNot (opt_MatchAny_match_expr MatchAny);
opt_MatchAny_match_expr (MatchAnd MatchAny MatchAny) = MatchAny;
opt_MatchAny_match_expr (MatchAnd MatchAny (Match v)) =
  opt_MatchAny_match_expr (Match v);
opt_MatchAny_match_expr (MatchAnd MatchAny (MatchNot v)) =
  opt_MatchAny_match_expr (MatchNot v);
opt_MatchAny_match_expr (MatchAnd MatchAny (MatchAnd v va)) =
  opt_MatchAny_match_expr (MatchAnd v va);
opt_MatchAny_match_expr (MatchAnd (Match v) MatchAny) =
  opt_MatchAny_match_expr (Match v);
opt_MatchAny_match_expr (MatchAnd (MatchNot v) MatchAny) =
  opt_MatchAny_match_expr (MatchNot v);
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) MatchAny) =
  opt_MatchAny_match_expr (MatchAnd v va);
opt_MatchAny_match_expr (MatchAnd (Match v) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchNot v) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (MatchNot MatchAny)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) (Match v)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) (MatchNot (Match va))) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) (MatchNot (MatchNot va)))
  = MatchNot MatchAny;
opt_MatchAny_match_expr
  (MatchAnd (MatchNot MatchAny) (MatchNot (MatchAnd va vb))) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny) (MatchAnd v va)) =
  MatchNot MatchAny;
opt_MatchAny_match_expr (MatchAnd (Match v) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr (Match v))
    (opt_MatchAny_match_expr (Match va));
opt_MatchAny_match_expr (MatchAnd (Match v) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr (Match v))
    (opt_MatchAny_match_expr (MatchNot (Match vb)));
opt_MatchAny_match_expr (MatchAnd (Match v) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr (Match v))
    (opt_MatchAny_match_expr (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr (MatchAnd (Match v) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr (Match v))
    (opt_MatchAny_match_expr (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr (MatchAnd (Match v) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr (Match v))
    (opt_MatchAny_match_expr (MatchAnd va vb));
opt_MatchAny_match_expr (MatchAnd (MatchNot (Match vb)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (Match vb)))
    (opt_MatchAny_match_expr (Match va));
opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchNot vb)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchNot vb)))
    (opt_MatchAny_match_expr (Match va));
opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchAnd vb vc)) (Match va)) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchAnd vb vc)))
    (opt_MatchAny_match_expr (Match va));
opt_MatchAny_match_expr (MatchAnd (MatchNot (Match va)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (Match va)))
    (opt_MatchAny_match_expr (MatchNot (Match vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr (MatchNot (Match vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchAnd va vc)) (MatchNot (Match vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchAnd va vc)))
    (opt_MatchAny_match_expr (MatchNot (Match vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (Match va)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (Match va)))
    (opt_MatchAny_match_expr (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchAnd va vc)) (MatchNot (MatchNot vb))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchAnd va vc)))
    (opt_MatchAny_match_expr (MatchNot (MatchNot vb)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (Match va)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (Match va)))
    (opt_MatchAny_match_expr (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchNot va)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchNot va)))
    (opt_MatchAny_match_expr (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr
  (MatchAnd (MatchNot (MatchAnd va vd)) (MatchNot (MatchAnd vb vc))) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchAnd va vd)))
    (opt_MatchAny_match_expr (MatchNot (MatchAnd vb vc)));
opt_MatchAny_match_expr (MatchAnd (MatchNot (Match vc)) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (Match vc)))
    (opt_MatchAny_match_expr (MatchAnd va vb));
opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchNot vc)) (MatchAnd va vb)) =
  MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchNot vc)))
    (opt_MatchAny_match_expr (MatchAnd va vb));
opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchAnd vc vd)) (MatchAnd va vb))
  = MatchAnd (opt_MatchAny_match_expr (MatchNot (MatchAnd vc vd)))
      (opt_MatchAny_match_expr (MatchAnd va vb));
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (Match vb)) =
  MatchAnd (opt_MatchAny_match_expr (MatchAnd v va))
    (opt_MatchAny_match_expr (Match vb));
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (MatchNot (Match vc))) =
  MatchAnd (opt_MatchAny_match_expr (MatchAnd v va))
    (opt_MatchAny_match_expr (MatchNot (Match vc)));
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (MatchNot (MatchNot vc))) =
  MatchAnd (opt_MatchAny_match_expr (MatchAnd v va))
    (opt_MatchAny_match_expr (MatchNot (MatchNot vc)));
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (MatchNot (MatchAnd vc vd))) =
  MatchAnd (opt_MatchAny_match_expr (MatchAnd v va))
    (opt_MatchAny_match_expr (MatchNot (MatchAnd vc vd)));
opt_MatchAny_match_expr (MatchAnd (MatchAnd v va) (MatchAnd vb vc)) =
  MatchAnd (opt_MatchAny_match_expr (MatchAnd v va))
    (opt_MatchAny_match_expr (MatchAnd vb vc));

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

normalize_rules_dnf :: forall a. [Rule a] -> [Rule a];
normalize_rules_dnf [] = [];
normalize_rules_dnf (Rule m a : rs) =
  map (\ ma -> Rule ma a) (normalize_match m) ++ normalize_rules_dnf rs;

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
  [Rule Common_primitive] -> [Rule Common_primitive];
transform_optimize_dnf_strict =
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

upper_closure :: [Rule Common_primitive] -> [Rule Common_primitive];
upper_closure rs =
  remdups_rev_code []
    (transform_optimize_dnf_strict
      (transform_normalize_primitives
        (transform_optimize_dnf_strict
          (optimize_matches_a upper_closure_matchexpr rs))));

word_to_nat :: forall a. (Len a) => Word a -> Nat;
word_to_nat = unat;

all_pairs :: forall a. [a] -> [(a, a)];
all_pairs xs = concatMap (\ x -> map (\ a -> (x, a)) xs) xs;

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
  Simple_match_ext ifaceAny ifaceAny (zero_word, zero_nat) (zero_word, zero_nat)
    ProtoAny (zero_word, word_of_int (Int_of_integer (65535 :: Integer)))
    (zero_word, word_of_int (Int_of_integer (65535 :: Integer))) ();

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

get_exists_matching_src_ips_executable ::
  Iface ->
    Match_expr Common_primitive ->
      Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
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
              } in (if null ip_matches then ipv4range_UNIV
                     else l2br_negation_type_intersect
                            (negPos_map ipt_ipv4range_to_interval ip_matches))
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
  Iface ->
    Match_expr Common_primitive ->
      Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))));
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
                     then (if null ip_matches then ipv4range_UNIV
                            else l2br_negation_type_intersect
                                   (negPos_map ipt_ipv4range_to_interval
                                     ip_matches))
                     else empty_WordInterval)
         else empty_WordInterval);

no_spoofing_algorithm_executable ::
  Iface ->
    (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
      [Rule Common_primitive] ->
        Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
          Wordinterval (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> Bool;
no_spoofing_algorithm_executable iface ipassmt [] allowed denied1 =
  wordinterval_subset (wordinterval_setminus allowed denied1)
    (l2br (map ipcidr_to_interval (the (ipassmt iface))));
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
  Iface ->
    (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
      [Rule Common_primitive] -> Bool;
no_spoofing_iface iface ipassmt rs =
  no_spoofing_algorithm_executable iface ipassmt rs empty_WordInterval
    empty_WordInterval;

tcp_flag_toString :: Tcp_flag -> [Prelude.Char];
tcp_flag_toString TCP_SYN = "TCP_SYN";
tcp_flag_toString TCP_ACK = "TCP_ACK";
tcp_flag_toString TCP_FIN = "TCP_FIN";
tcp_flag_toString TCP_RST = "TCP_RST";
tcp_flag_toString TCP_URG = "TCP_URG";
tcp_flag_toString TCP_PSH = "TCP_PSH";

nat_to_8word :: Nat -> Word (Bit0 (Bit0 (Bit0 Num1)));
nat_to_8word i = of_nat i;

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

map_of_string ::
  [([Prelude.Char], [Rule Common_primitive])] ->
    [Prelude.Char] -> Maybe [Rule Common_primitive];
map_of_string rs = map_of rs;

nat_to_16word :: Nat -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
nat_to_16word i = of_nat i;

compress_parsed_extra ::
  [Negation_type Common_primitive] -> [Negation_type Common_primitive];
compress_parsed_extra [] = [];
compress_parsed_extra (a1 : a2 : asa) =
  (if is_pos_Extra a1 && is_pos_Extra a2
    then compress_parsed_extra
           (Pos (Extra (get_pos_Extra a1 ++ " " ++ get_pos_Extra a2)) : asa)
    else a1 : compress_parsed_extra (a2 : asa));
compress_parsed_extra [a] = a : compress_parsed_extra [];

ipt_tcp_flags_equal :: Ipt_tcp_flags -> Ipt_tcp_flags -> Bool;
ipt_tcp_flags_equal (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) =
  (if less_eq_set c1 fmask1 && less_eq_set c2 fmask2
    then equal_set c1 c2 && equal_set fmask1 fmask2
    else not (less_eq_set c1 fmask1) && not (less_eq_set c2 fmask2));

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

ipt_tcp_flags_NoMatch :: Ipt_tcp_flags;
ipt_tcp_flags_NoMatch = TCP_Flags bot_set (insert TCP_SYN bot_set);

ipt_tcp_flags_toString :: Set Tcp_flag -> [Prelude.Char];
ipt_tcp_flags_toString flags =
  list_toString tcp_flag_toString (enum_set_to_list flags);

integer_to_16word :: Integer -> Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))));
integer_to_16word i = nat_to_16word (nat_of_integer i);

ctstate_toString :: Ctstate -> [Prelude.Char];
ctstate_toString CT_New = "NEW";
ctstate_toString CT_Established = "ESTABLISHED";
ctstate_toString CT_Related = "RELATED";
ctstate_toString CT_Untracked = "UNTRACKED";
ctstate_toString CT_Invalid = "INVALID";

match_list_to_match_expr :: forall a. [Match_expr a] -> Match_expr a;
match_list_to_match_expr [] = MatchNot MatchAny;
match_list_to_match_expr (m : ms) = matchOr m (match_list_to_match_expr ms);

ipassmt_iface_replace_srcip_mexpr ::
  (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
    Iface -> Match_expr Common_primitive;
ipassmt_iface_replace_srcip_mexpr ipassmt ifce =
  (case ipassmt ifce of {
    Nothing -> Match (IIface ifce);
    Just ips ->
      match_list_to_match_expr
        (map (Match . Src)
          (map (\ (ip, a) -> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) a)
            ips));
  });

iiface_rewrite ::
  (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
    Match_expr Common_primitive -> Match_expr Common_primitive;
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

has_disc :: forall a. (a -> Bool) -> Match_expr a -> Bool;
has_disc uu MatchAny = False;
has_disc disc (Match a) = disc a;
has_disc disc (MatchNot m) = has_disc disc m;
has_disc disc (MatchAnd m1 m2) = has_disc disc m1 || has_disc disc m2;

repeat_stabilize :: forall a. (Eq a) => Nat -> (a -> a) -> a -> a;
repeat_stabilize n uu v =
  (if equal_nat n zero_nat then v
    else let {
           v_new = uu v;
         } in (if v == v_new then v
                else repeat_stabilize (minus_nat n one_nat) uu v_new));

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

wordinterval_sort :: forall a. (Len a) => Wordinterval a -> Wordinterval a;
wordinterval_sort w = l2br (mergesort_remdups (br2l w));

build_ip_partition ::
  forall a.
    (Len a) => Parts_connection_ext () -> [Simple_rule a] -> [Wordinterval a];
build_ip_partition c rs =
  map (\ xs ->
        wordinterval_sort
          (wordinterval_compress
            (foldr wordinterval_union xs empty_WordInterval)))
    (groupWIs3 c rs);

match_tcp_flags_conjunct :: Ipt_tcp_flags -> Ipt_tcp_flags -> Ipt_tcp_flags;
match_tcp_flags_conjunct (TCP_Flags fmask1 c1) (TCP_Flags fmask2 c2) =
  (if less_eq_set c1 fmask1 &&
        less_eq_set c2 fmask2 &&
          equal_set (inf_set (inf_set fmask1 fmask2) c1)
            (inf_set (inf_set fmask1 fmask2) c2)
    then TCP_Flags (sup_set fmask1 fmask2) (sup_set c1 c2)
    else ipt_tcp_flags_NoMatch);

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

ipassmt_iface_constrain_srcip_mexpr ::
  (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
    Iface -> Match_expr Common_primitive;
ipassmt_iface_constrain_srcip_mexpr ipassmt ifce =
  (case ipassmt ifce of {
    Nothing -> Match (IIface ifce);
    Just ips ->
      MatchAnd (Match (IIface ifce))
        (match_list_to_match_expr
          (map (Match . Src)
            (map (\ (ip, a) -> Ip4AddrNetmask (dotdecimal_of_ipv4addr ip) a)
              ips)));
  });

iiface_constrain ::
  (Iface -> Maybe [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)]) ->
    Match_expr Common_primitive -> Match_expr Common_primitive;
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

access_matrix_pretty_code ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty_code c rs =
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

access_matrix_pretty ::
  Parts_connection_ext () ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))] ->
      ([([Prelude.Char], [Prelude.Char])], [([Prelude.Char], [Prelude.Char])]);
access_matrix_pretty = access_matrix_pretty_code;

iface_try_rewrite ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    [Rule Common_primitive] -> [Rule Common_primitive];
iface_try_rewrite ipassmt rs =
  (if let {
        is = image fst (Set ipassmt);
      } in ball is
             (\ i1 ->
               ball is
                 (\ i2 ->
                   (if not (equal_iface i1 i2)
                     then wordinterval_empty
                            (wordinterval_intersection
                              (l2br (map ipcidr_to_interval
                                      (the (map_of ipassmt i1))))
                              (l2br (map ipcidr_to_interval
                                      (the (map_of ipassmt i2)))))
                     else True))) &&
        ipassmt_sanity_defined rs (map_of ipassmt)
    then optimize_matches (iiface_rewrite (map_of_ipassmt ipassmt)) rs
    else optimize_matches (iiface_constrain (map_of_ipassmt ipassmt)) rs);

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

ctstate_set_toString :: Set Ctstate -> [Prelude.Char];
ctstate_set_toString s =
  list_separated_toString "," ctstate_toString (enum_set_to_list s);

normalized_dst_ports :: Match_expr Common_primitive -> Bool;
normalized_dst_ports MatchAny = True;
normalized_dst_ports (Match (Dst_Ports [])) = True;
normalized_dst_ports (Match (Dst_Ports [uu])) = True;
normalized_dst_ports (Match (Dst_Ports (v : vb : vc))) = False;
normalized_dst_ports (Match (Src v)) = True;
normalized_dst_ports (Match (Dst v)) = True;
normalized_dst_ports (Match (IIface v)) = True;
normalized_dst_ports (Match (OIface v)) = True;
normalized_dst_ports (Match (Prot v)) = True;
normalized_dst_ports (Match (Src_Ports v)) = True;
normalized_dst_ports (Match (L4_Flags v)) = True;
normalized_dst_ports (Match (CT_State v)) = True;
normalized_dst_ports (Match (Extra v)) = True;
normalized_dst_ports (MatchNot (Match (Dst_Ports ux))) = False;
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
normalized_dst_ports (MatchNot (MatchAnd uz va)) = False;
normalized_dst_ports (MatchNot (MatchNot vb)) = False;
normalized_dst_ports (MatchNot MatchAny) = True;

normalized_src_ports :: Match_expr Common_primitive -> Bool;
normalized_src_ports MatchAny = True;
normalized_src_ports (Match (Src_Ports [])) = True;
normalized_src_ports (Match (Src_Ports [uu])) = True;
normalized_src_ports (Match (Src_Ports (v : vb : vc))) = False;
normalized_src_ports (Match (Src v)) = True;
normalized_src_ports (Match (Dst v)) = True;
normalized_src_ports (Match (IIface v)) = True;
normalized_src_ports (Match (OIface v)) = True;
normalized_src_ports (Match (Prot v)) = True;
normalized_src_ports (Match (Dst_Ports v)) = True;
normalized_src_ports (Match (L4_Flags v)) = True;
normalized_src_ports (Match (CT_State v)) = True;
normalized_src_ports (Match (Extra v)) = True;
normalized_src_ports (MatchNot (Match (Src_Ports ux))) = False;
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
normalized_src_ports (MatchNot (MatchAnd uz va)) = False;
normalized_src_ports (MatchNot (MatchNot vb)) = False;
normalized_src_ports (MatchNot MatchAny) = True;

protocol_toString :: Protocol -> [Prelude.Char];
protocol_toString ProtoAny = "all";
protocol_toString (Proto protid) =
  (if equal_word protid tcp then "tcp"
    else (if equal_word protid udp then "udp"
           else (if equal_word protid icmp then "icmp"
                  else (if equal_word protid sctp then "sctp"
                         else "protocolid:" ++ string_of_nat (unat protid)))));

port_toString :: Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) -> [Prelude.Char];
port_toString p = string_of_nat (unat p);

ports_toString ::
  [Prelude.Char] ->
    (Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))),
      Word (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ->
      [Prelude.Char];
ports_toString descr (s, e) =
  (if equal_word s zero_word && equal_word e max_word then []
    else descr ++
           (if equal_word s e then port_toString s
             else port_toString s ++ ":" ++ port_toString e));

iface_toString :: [Prelude.Char] -> Iface -> [Prelude.Char];
iface_toString descr iface =
  (if equal_iface iface ifaceAny then [] else let {
        (Iface a) = iface;
      } in descr ++ a);

common_primitive_toString :: Common_primitive -> [Prelude.Char];
common_primitive_toString (Src (Ip4Addr ip)) =
  "-s " ++ dotteddecimal_toString ip;
common_primitive_toString (Dst (Ip4Addr ip)) =
  "-d " ++ dotteddecimal_toString ip;
common_primitive_toString (Src (Ip4AddrNetmask ip n)) =
  "-s " ++ dotteddecimal_toString ip ++ "/" ++ string_of_nat n;
common_primitive_toString (Dst (Ip4AddrNetmask ip n)) =
  "-d " ++ dotteddecimal_toString ip ++ "/" ++ string_of_nat n;
common_primitive_toString (Src (Ip4AddrRange ip1 ip2)) =
  "-m iprange --src-range " ++
    dotteddecimal_toString ip1 ++ "-" ++ dotteddecimal_toString ip2;
common_primitive_toString (Dst (Ip4AddrRange ip1 ip2)) =
  "-m iprange --dst-range " ++
    dotteddecimal_toString ip1 ++ "-" ++ dotteddecimal_toString ip2;
common_primitive_toString (IIface ifce) = iface_toString "-i " ifce;
common_primitive_toString (OIface ifce) = iface_toString "-o " ifce;
common_primitive_toString (Prot prot) = "-p " ++ protocol_toString prot;
common_primitive_toString (Src_Ports pts) =
  "--spts " ++ list_toString (ports_toString []) pts;
common_primitive_toString (Dst_Ports pts) =
  "--dpts " ++ list_toString (ports_toString []) pts;
common_primitive_toString (CT_State s) =
  "-m state --state " ++ ctstate_set_toString s;
common_primitive_toString (L4_Flags (TCP_Flags c m)) =
  "--tcp-flags " ++ ipt_tcp_flags_toString c ++ " " ++ ipt_tcp_flags_toString m;
common_primitive_toString (Extra e) = "~~" ++ e ++ "~~";

abstract_primitive ::
  (Negation_type Common_primitive -> Bool) ->
    Match_expr Common_primitive -> Match_expr Common_primitive;
abstract_primitive uu MatchAny = MatchAny;
abstract_primitive disc (Match a) =
  (if disc (Pos a) then Match (Extra (common_primitive_toString a))
    else Match a);
abstract_primitive disc (MatchNot (Match a)) =
  (if disc (Neg a) then Match (Extra ("! " ++ common_primitive_toString a))
    else MatchNot (Match a));
abstract_primitive disc (MatchNot (MatchNot v)) =
  MatchNot (abstract_primitive disc (MatchNot v));
abstract_primitive disc (MatchNot (MatchAnd v va)) =
  MatchNot (abstract_primitive disc (MatchAnd v va));
abstract_primitive disc (MatchNot MatchAny) =
  MatchNot (abstract_primitive disc MatchAny);
abstract_primitive disc (MatchAnd m1 m2) =
  MatchAnd (abstract_primitive disc m1) (abstract_primitive disc m2);

has_disc_negated :: forall a. (a -> Bool) -> Bool -> Match_expr a -> Bool;
has_disc_negated uu uv MatchAny = False;
has_disc_negated disc neg (Match a) = (if disc a then neg else False);
has_disc_negated disc neg (MatchNot m) = has_disc_negated disc (not neg) m;
has_disc_negated disc neg (MatchAnd m1 m2) =
  has_disc_negated disc neg m1 || has_disc_negated disc neg m2;

normalized_ifaces :: Match_expr Common_primitive -> Bool;
normalized_ifaces m =
  not (has_disc_negated (\ a -> is_Iiface a || is_Oiface a) False m);

mk_parts_connection_TCP ::
  Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) ->
    Word (Bit0 (Bit0 (Bit0 (Bit0 Num1)))) -> Parts_connection_ext ();
mk_parts_connection_TCP sport dport =
  Parts_connection_ext "1" "1" tcp sport dport CT_New ();

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
  Match_expr Common_primitive ->
    Maybe (Simple_match_ext (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) ());
common_primitive_match_to_simple_match MatchAny = Just simple_match_any;
common_primitive_match_to_simple_match (MatchNot MatchAny) = Nothing;
common_primitive_match_to_simple_match (Match (IIface iif)) =
  Just (iiface_update (\ _ -> iif) simple_match_any);
common_primitive_match_to_simple_match (Match (OIface oif)) =
  Just (oiface_update (\ _ -> oif) simple_match_any);
common_primitive_match_to_simple_match (Match (Src (Ip4AddrNetmask pre len))) =
  Just (src_update (\ _ -> (ipv4addr_of_dotdecimal pre, len)) simple_match_any);
common_primitive_match_to_simple_match (Match (Dst (Ip4AddrNetmask pre len))) =
  Just (dst_update (\ _ -> (ipv4addr_of_dotdecimal pre, len)) simple_match_any);
common_primitive_match_to_simple_match (Match (Prot p)) =
  Just (proto_update (\ _ -> p) simple_match_any);
common_primitive_match_to_simple_match (Match (Src_Ports [])) = Nothing;
common_primitive_match_to_simple_match (Match (Src_Ports [(s, e)])) =
  Just (sports_update (\ _ -> (s, e)) simple_match_any);
common_primitive_match_to_simple_match (Match (Dst_Ports [])) = Nothing;
common_primitive_match_to_simple_match (Match (Dst_Ports [(s, e)])) =
  Just (dports_update (\ _ -> (s, e)) simple_match_any);
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
common_primitive_match_to_simple_match (Match (Src (Ip4Addr uu))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Src (Ip4AddrRange uv uw))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Dst (Ip4Addr ux))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Dst (Ip4AddrRange uy uz))) =
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
common_primitive_match_to_simple_match (Match (Src_Ports (vi : v : va))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Dst_Ports (vk : v : va))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Src_Ports vm))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Dst_Ports vn))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (CT_State vo)) =
  error "undefined";
common_primitive_match_to_simple_match (Match (L4_Flags vp)) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (L4_Flags vq))) =
  error "undefined";
common_primitive_match_to_simple_match (Match (Extra vr)) = error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (Extra vs))) =
  error "undefined";
common_primitive_match_to_simple_match (MatchNot (Match (CT_State vt))) =
  error "undefined";

is_L4_Flags :: Common_primitive -> Bool;
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

is_CT_State :: Common_primitive -> Bool;
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

is_Extra :: Common_primitive -> Bool;
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

normalized_protocols :: Match_expr Common_primitive -> Bool;
normalized_protocols m = not (has_disc_negated is_Prot False m);

normalized_src_ips :: Match_expr Common_primitive -> Bool;
normalized_src_ips MatchAny = True;
normalized_src_ips (Match (Src (Ip4AddrRange uu uv))) = False;
normalized_src_ips (Match (Src (Ip4Addr uw))) = False;
normalized_src_ips (Match (Src (Ip4AddrNetmask ux uy))) = True;
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

normalized_dst_ips :: Match_expr Common_primitive -> Bool;
normalized_dst_ips MatchAny = True;
normalized_dst_ips (Match (Dst (Ip4AddrRange uu uv))) = False;
normalized_dst_ips (Match (Dst (Ip4Addr uw))) = False;
normalized_dst_ips (Match (Dst (Ip4AddrNetmask ux uy))) = True;
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

check_simple_fw_preconditions :: [Rule Common_primitive] -> Bool;
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
  [Rule Common_primitive] ->
    [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
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

ipv4_cidr_toString ::
  (Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat) -> [Prelude.Char];
ipv4_cidr_toString ip_n = let {
                            (base, n) = ip_n;
                          } in ipv4addr_toString base ++ "/" ++ string_of_nat n;

simple_action_toString :: Simple_action -> [Prelude.Char];
simple_action_toString Accepta = "ACCEPT";
simple_action_toString Dropa = "DROP";

simple_rule_toString ::
  Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))) -> [Prelude.Char];
simple_rule_toString
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
  [Prelude.Char] ->
    Action ->
      ([Prelude.Char] -> Maybe [Rule Common_primitive]) ->
        Maybe [Rule Common_primitive];
unfold_ruleset_CHAIN_safe =
  unfold_optimize_ruleset_CHAIN optimize_primitive_univ;

match_tcp_flags_conjunct_option ::
  Ipt_tcp_flags -> Ipt_tcp_flags -> Maybe Ipt_tcp_flags;
match_tcp_flags_conjunct_option f1 f2 =
  let {
    (TCP_Flags fmask c) = match_tcp_flags_conjunct f1 f2;
  } in (if less_eq_set c fmask then Just (TCP_Flags fmask c) else Nothing);

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

ipt_tcp_flags_assume_flag ::
  Ipt_tcp_flags -> Match_expr Common_primitive -> Match_expr Common_primitive;
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

ipt_tcp_flags_assume_syn :: [Rule Common_primitive] -> [Rule Common_primitive];
ipt_tcp_flags_assume_syn =
  optimize_matches (ipt_tcp_flags_assume_flag ipt_tcp_syn);

ctstate_assume_state ::
  Ctstate -> Match_expr Common_primitive -> Match_expr Common_primitive;
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

ctstate_assume_new :: [Rule Common_primitive] -> [Rule Common_primitive];
ctstate_assume_new = optimize_matches (ctstate_assume_state CT_New);

packet_assume_new :: [Rule Common_primitive] -> [Rule Common_primitive];
packet_assume_new = ctstate_assume_new . ipt_tcp_flags_assume_syn;

abstract_for_simple_firewall ::
  Match_expr Common_primitive -> Match_expr Common_primitive;
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

to_simple_firewall_without_interfaces ::
  [(Iface, [(Word (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1))))), Nat)])] ->
    [Rule Common_primitive] ->
      [Simple_rule (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 Num1)))))];
to_simple_firewall_without_interfaces ipassmt rs =
  to_simple_firewall
    (upper_closure
      (optimize_matches
        (abstract_primitive (\ a -> (case a of {
                                      Pos aa -> is_Iiface aa || is_Oiface aa;
                                      Neg aa -> is_Iiface aa || is_Oiface aa;
                                    })))
        (optimize_matches abstract_for_simple_firewall
          (upper_closure
            (iface_try_rewrite ipassmt
              (upper_closure (packet_assume_new rs)))))));

common_primitive_match_expr_toString ::
  Match_expr Common_primitive -> [Prelude.Char];
common_primitive_match_expr_toString MatchAny = [];
common_primitive_match_expr_toString (Match m) = common_primitive_toString m;
common_primitive_match_expr_toString (MatchAnd m1 m2) =
  common_primitive_match_expr_toString m1 ++
    " " ++ common_primitive_match_expr_toString m2;
common_primitive_match_expr_toString (MatchNot (Match m)) =
  "! " ++ common_primitive_toString m;
common_primitive_match_expr_toString (MatchNot (MatchNot v)) =
  "NOT (" ++ common_primitive_match_expr_toString (MatchNot v) ++ ")";
common_primitive_match_expr_toString (MatchNot (MatchAnd v va)) =
  "NOT (" ++ common_primitive_match_expr_toString (MatchAnd v va) ++ ")";
common_primitive_match_expr_toString (MatchNot MatchAny) =
  "NOT (" ++ common_primitive_match_expr_toString MatchAny ++ ")";

}
