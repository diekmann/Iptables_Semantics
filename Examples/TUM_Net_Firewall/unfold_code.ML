structure Test : sig
  type num
  type nat
  val integer_of_nat : nat -> IntInf.int
  type 'a word
  val nat_of_integer : IntInf.int -> nat
  type 'a bit0
  type num1
  datatype action = Accept | Drop | Log | Reject | Call of char list | Return |
    Empty | Unknown
  datatype 'a negation_type = Pos of 'a | Neg of 'a
  datatype ipt_ipv4range = Ip4Addr of (nat * (nat * (nat * nat))) |
    Ip4AddrNetmask of (nat * (nat * (nat * nat))) * nat
  datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP
  datatype iptrule_match = Src of ipt_ipv4range | Dst of ipt_ipv4range |
    Prot of ipt_protocol | Extra of char list
  type nibble
  datatype 'a match_expr = Match of 'a | MatchNot of 'a match_expr |
    MatchAnd of 'a match_expr * 'a match_expr | MatchAny
  datatype 'a rule = Rule of 'a match_expr * action
  type 'a packet_set
  datatype match_Ln_uncompressed =
    UncompressedFormattedMatch of
      ipt_ipv4range negation_type list * ipt_ipv4range negation_type list *
        ipt_protocol negation_type list * (char list) negation_type list
  val deny_set : iptrule_match rule list -> iptrule_match packet_set list
  val compress_Ln_ips :
    (match_Ln_uncompressed * action) list ->
      (match_Ln_uncompressed * action) list
  val lower_closure : iptrule_match rule list -> iptrule_match rule list
  val map_of_string :
    (char list * iptrule_match rule list) list ->
      char list -> (iptrule_match rule list) option
  val upper_closure : iptrule_match rule list -> iptrule_match rule list
  val format_Ln_rules_uncompressed :
    iptrule_match rule list -> (match_Ln_uncompressed * action) list
  val does_I_has_compressed_prots :
    (match_Ln_uncompressed * action) list ->
      (match_Ln_uncompressed * action) list
  val does_I_has_compressed_rules :
    (match_Ln_uncompressed * action) list ->
      (match_Ln_uncompressed * action) list
  val unfold_ruleset_FORWARD :
    (char list -> (iptrule_match rule list) option) -> iptrule_match rule list
  val bitmask_to_strange_inverse_cisco_mask : nat -> nat * (nat * (nat * nat))
end = struct

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun integer_of_int (Int_of_integer k) = k;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

fun sgn_integer k =
  (if ((k : IntInf.int) = 0) then 0
    else (if IntInf.< (k, 0) then (~1 : IntInf.int) else (1 : IntInf.int)));

fun abs_integer k = (if IntInf.< (k, 0) then IntInf.~ k else k);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = 0) then (0, 0)
    else (if ((l : IntInf.int) = 0) then (0, k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = 0) then (IntInf.~ r, 0)
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_integer l, s)))
                         end)));

fun snd (x1, x2) = x2;

fun mod_integer k l = snd (divmod_integer k l);

fun mod_int k l =
  Int_of_integer (mod_integer (integer_of_int k) (integer_of_int l));

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nat m n =
  Nat (max ord_integer 0 (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat 0;

val one_nat : nat = Nat (1 : IntInf.int);

fun power one times a n =
  (if equal_nata n zero_nat then one
    else times a (power one times a (minus_nat n one_nat)));

fun powera A_ = power (one (one_power A_)) (times (times_power A_));

datatype 'a word = Word of int;

fun word_of_int A_ k =
  Word (mod_int k
         (powera power_int (Int_of_integer (2 : IntInf.int)) (len_of A_ Type)));

fun one_worda A_ = word_of_int A_ (Int_of_integer (1 : IntInf.int));

fun one_word A_ = {one = one_worda A_} : 'a word one;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun uint A_ (Word x) = x;

fun plus_worda A_ a b = word_of_int A_ (plus_int (uint A_ a) (uint A_ b));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

fun plus_word A_ = {plus = plus_worda A_} : 'a word plus;

val zero_int : int = Int_of_integer 0;

fun zero_worda A_ = word_of_int A_ zero_int;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

fun zero_word A_ = {zero = zero_worda A_} : 'a word zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

fun semigroup_add_word A_ = {plus_semigroup_add = plus_word A_} :
  'a word semigroup_add;

fun numeral_word A_ =
  {one_numeral = one_word A_, semigroup_add_numeral = semigroup_add_word A_} :
  'a word numeral;

fun times_worda A_ a b = word_of_int A_ (times_inta (uint A_ a) (uint A_ b));

fun times_word A_ = {times = times_worda A_} : 'a word times;

fun power_word A_ = {one_power = one_word A_, times_power = times_word A_} :
  'a word power;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun less_eq_word A_ a b = less_eq_int (uint A_ a) (uint A_ b);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun less_word A_ a b = less_int (uint A_ a) (uint A_ b);

fun ord_word A_ = {less_eq = less_eq_word A_, less = less_word A_} :
  'a word ord;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

fun ab_semigroup_add_word A_ =
  {semigroup_add_ab_semigroup_add = semigroup_add_word A_} :
  'a word ab_semigroup_add;

fun semigroup_mult_word A_ = {times_semigroup_mult = times_word A_} :
  'a word semigroup_mult;

fun semiring_word A_ =
  {ab_semigroup_add_semiring = ab_semigroup_add_word A_,
    semigroup_mult_semiring = semigroup_mult_word A_}
  : 'a word semiring;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

fun mult_zero_word A_ =
  {times_mult_zero = times_word A_, zero_mult_zero = zero_word A_} :
  'a word mult_zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

fun monoid_add_word A_ =
  {semigroup_add_monoid_add = semigroup_add_word A_,
    zero_monoid_add = zero_word A_}
  : 'a word monoid_add;

fun comm_monoid_add_word A_ =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_word A_,
    monoid_add_comm_monoid_add = monoid_add_word A_}
  : 'a word comm_monoid_add;

fun semiring_0_word A_ =
  {comm_monoid_add_semiring_0 = comm_monoid_add_word A_,
    mult_zero_semiring_0 = mult_zero_word A_,
    semiring_semiring_0 = semiring_word A_}
  : 'a word semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

fun monoid_mult_word A_ =
  {semigroup_mult_monoid_mult = semigroup_mult_word A_,
    power_monoid_mult = power_word A_}
  : 'a word monoid_mult;

fun semiring_numeral_word A_ =
  {monoid_mult_semiring_numeral = monoid_mult_word (len0_len A_),
    numeral_semiring_numeral = numeral_word (len0_len A_),
    semiring_semiring_numeral = semiring_word (len0_len A_)}
  : 'a word semiring_numeral;

fun zero_neq_one_word A_ =
  {one_zero_neq_one = one_word (len0_len A_),
    zero_zero_neq_one = zero_word (len0_len A_)}
  : 'a word zero_neq_one;

fun semiring_1_word A_ =
  {semiring_numeral_semiring_1 = semiring_numeral_word A_,
    semiring_0_semiring_1 = semiring_0_word (len0_len A_),
    zero_neq_one_semiring_1 = zero_neq_one_word A_}
  : 'a word semiring_1;

val equal_char = {equal = (fn a => fn b => ((a : char) = b))} : char equal;

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

fun equal_word A_ k l = equal_int (uint A_ k) (uint A_ l);

datatype 'a bitrange = Bitrange of 'a word * 'a word |
  RangeUnion of 'a bitrange * 'a bitrange;

fun equal_bitrangea A_ (Bitrange (word1, word2))
  (RangeUnion (bitrange1, bitrange2)) = false
  | equal_bitrangea A_ (RangeUnion (bitrange1, bitrange2))
    (Bitrange (word1, word2)) = false
  | equal_bitrangea A_ (RangeUnion (bitrange1a, bitrange2a))
    (RangeUnion (bitrange1, bitrange2)) =
    equal_bitrangea A_ bitrange1a bitrange1 andalso
      equal_bitrangea A_ bitrange2a bitrange2
  | equal_bitrangea A_ (Bitrange (word1a, word2a)) (Bitrange (word1, word2)) =
    equal_word (len0_len A_) word1a word1 andalso
      equal_word (len0_len A_) word2a word2;

fun equal_bitrange A_ = {equal = equal_bitrangea A_} : 'a bitrange equal;

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun nat_of_integer k = Nat (max ord_integer 0 k);

type 'a finite = {};

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ x =
  times_nat (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

datatype num1 = One_num1;

fun len_of_num1 x = one_nat;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype action = Accept | Drop | Log | Reject | Call of char list | Return |
  Empty | Unknown;

fun equal_actiona Empty Unknown = false
  | equal_actiona Unknown Empty = false
  | equal_actiona Return Unknown = false
  | equal_actiona Unknown Return = false
  | equal_actiona Return Empty = false
  | equal_actiona Empty Return = false
  | equal_actiona (Call lista) Unknown = false
  | equal_actiona Unknown (Call lista) = false
  | equal_actiona (Call lista) Empty = false
  | equal_actiona Empty (Call lista) = false
  | equal_actiona (Call lista) Return = false
  | equal_actiona Return (Call lista) = false
  | equal_actiona Reject Unknown = false
  | equal_actiona Unknown Reject = false
  | equal_actiona Reject Empty = false
  | equal_actiona Empty Reject = false
  | equal_actiona Reject Return = false
  | equal_actiona Return Reject = false
  | equal_actiona Reject (Call lista) = false
  | equal_actiona (Call lista) Reject = false
  | equal_actiona Log Unknown = false
  | equal_actiona Unknown Log = false
  | equal_actiona Log Empty = false
  | equal_actiona Empty Log = false
  | equal_actiona Log Return = false
  | equal_actiona Return Log = false
  | equal_actiona Log (Call lista) = false
  | equal_actiona (Call lista) Log = false
  | equal_actiona Log Reject = false
  | equal_actiona Reject Log = false
  | equal_actiona Drop Unknown = false
  | equal_actiona Unknown Drop = false
  | equal_actiona Drop Empty = false
  | equal_actiona Empty Drop = false
  | equal_actiona Drop Return = false
  | equal_actiona Return Drop = false
  | equal_actiona Drop (Call lista) = false
  | equal_actiona (Call lista) Drop = false
  | equal_actiona Drop Reject = false
  | equal_actiona Reject Drop = false
  | equal_actiona Drop Log = false
  | equal_actiona Log Drop = false
  | equal_actiona Accept Unknown = false
  | equal_actiona Unknown Accept = false
  | equal_actiona Accept Empty = false
  | equal_actiona Empty Accept = false
  | equal_actiona Accept Return = false
  | equal_actiona Return Accept = false
  | equal_actiona Accept (Call lista) = false
  | equal_actiona (Call lista) Accept = false
  | equal_actiona Accept Reject = false
  | equal_actiona Reject Accept = false
  | equal_actiona Accept Log = false
  | equal_actiona Log Accept = false
  | equal_actiona Accept Drop = false
  | equal_actiona Drop Accept = false
  | equal_actiona (Call listaa) (Call lista) =
    equal_lista equal_char listaa lista
  | equal_actiona Unknown Unknown = true
  | equal_actiona Empty Empty = true
  | equal_actiona Return Return = true
  | equal_actiona Reject Reject = true
  | equal_actiona Log Log = true
  | equal_actiona Drop Drop = true
  | equal_actiona Accept Accept = true;

val equal_action = {equal = equal_actiona} : action equal;

datatype 'a negation_type = Pos of 'a | Neg of 'a;

fun equal_negation_typea A_ (Pos aa) (Neg a) = false
  | equal_negation_typea A_ (Neg aa) (Pos a) = false
  | equal_negation_typea A_ (Neg aa) (Neg a) = eq A_ aa a
  | equal_negation_typea A_ (Pos aa) (Pos a) = eq A_ aa a;

fun equal_negation_type A_ = {equal = equal_negation_typea A_} :
  'a negation_type equal;

datatype ipt_ipv4range = Ip4Addr of (nat * (nat * (nat * nat))) |
  Ip4AddrNetmask of (nat * (nat * (nat * nat))) * nat;

fun equal_ipt_ipv4range (Ip4Addr proda) (Ip4AddrNetmask (prod, nat)) = false
  | equal_ipt_ipv4range (Ip4AddrNetmask (proda, nat)) (Ip4Addr prod) = false
  | equal_ipt_ipv4range (Ip4AddrNetmask (proda, nata))
    (Ip4AddrNetmask (prod, nat)) =
    equal_proda equal_nat
      (equal_prod equal_nat (equal_prod equal_nat equal_nat)) proda prod andalso
      equal_nata nata nat
  | equal_ipt_ipv4range (Ip4Addr proda) (Ip4Addr prod) =
    equal_proda equal_nat
      (equal_prod equal_nat (equal_prod equal_nat equal_nat)) proda prod;

datatype ipt_protocol = ProtAll | ProtTCP | ProtUDP;

fun equal_ipt_protocol ProtTCP ProtUDP = false
  | equal_ipt_protocol ProtUDP ProtTCP = false
  | equal_ipt_protocol ProtAll ProtUDP = false
  | equal_ipt_protocol ProtUDP ProtAll = false
  | equal_ipt_protocol ProtAll ProtTCP = false
  | equal_ipt_protocol ProtTCP ProtAll = false
  | equal_ipt_protocol ProtUDP ProtUDP = true
  | equal_ipt_protocol ProtTCP ProtTCP = true
  | equal_ipt_protocol ProtAll ProtAll = true;

datatype iptrule_match = Src of ipt_ipv4range | Dst of ipt_ipv4range |
  Prot of ipt_protocol | Extra of char list;

fun equal_iptrule_matcha (Prot x3) (Extra x4) = false
  | equal_iptrule_matcha (Extra x4) (Prot x3) = false
  | equal_iptrule_matcha (Dst x2) (Extra x4) = false
  | equal_iptrule_matcha (Extra x4) (Dst x2) = false
  | equal_iptrule_matcha (Dst x2) (Prot x3) = false
  | equal_iptrule_matcha (Prot x3) (Dst x2) = false
  | equal_iptrule_matcha (Src x1) (Extra x4) = false
  | equal_iptrule_matcha (Extra x4) (Src x1) = false
  | equal_iptrule_matcha (Src x1) (Prot x3) = false
  | equal_iptrule_matcha (Prot x3) (Src x1) = false
  | equal_iptrule_matcha (Src x1) (Dst x2) = false
  | equal_iptrule_matcha (Dst x2) (Src x1) = false
  | equal_iptrule_matcha (Extra x4) (Extra y4) = equal_lista equal_char x4 y4
  | equal_iptrule_matcha (Prot x3) (Prot y3) = equal_ipt_protocol x3 y3
  | equal_iptrule_matcha (Dst x2) (Dst y2) = equal_ipt_ipv4range x2 y2
  | equal_iptrule_matcha (Src x1) (Src y1) = equal_ipt_ipv4range x1 y1;

val equal_iptrule_match = {equal = equal_iptrule_matcha} : iptrule_match equal;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype 'a match_expr = Match of 'a | MatchNot of 'a match_expr |
  MatchAnd of 'a match_expr * 'a match_expr | MatchAny;

datatype 'a rule = Rule of 'a match_expr * action;

datatype 'a packet_set =
  PacketSet of (('a negation_type * action negation_type) list) list;

datatype match_Ln_uncompressed =
  UncompressedFormattedMatch of
    ipt_ipv4range negation_type list * ipt_ipv4range negation_type list *
      ipt_protocol negation_type list * (char list) negation_type list;

fun id x = (fn xa => xa) x;

fun nat x = (nat_of_integer o integer_of_int) x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nat;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun minus_word A_ a b = word_of_int A_ (minus_int (uint A_ a) (uint A_ b));

fun bit k b =
  plus_int
    (plus_int (if b then Int_of_integer (1 : IntInf.int) else zero_int) k) k;

fun shiftl1 A_ w = word_of_int A_ (bit (uint A_ w) false);

fun funpow n f =
  (if equal_nata n zero_nat then id else f o funpow (minus_nat n one_nat) f);

fun shiftl_word A_ w n = funpow n (shiftl1 A_) w;

fun mask A_ n =
  minus_word (len0_len A_)
    (shiftl_word (len0_len A_) (one_worda (len0_len A_)) n)
    (one_worda (len0_len A_));

fun unat A_ w = nat (uint A_ w);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun fst (x1, x2) = x1;

fun div_integer k l = fst (divmod_integer k l);

fun div_int k l =
  Int_of_integer (div_integer (integer_of_int k) (integer_of_int l));

fun bin_rest w = div_int w (Int_of_integer (2 : IntInf.int));

fun shiftr1 A_ w = word_of_int A_ (bin_rest (uint A_ w));

fun map fi [] = []
  | map fi (x21a :: x22) = fi x21a :: map fi x22;

fun max_word A_ =
  word_of_int (len0_len A_)
    (minus_int
      (powera power_int (Int_of_integer (2 : IntInf.int))
        (len_of (len0_len A_) Type))
      (Int_of_integer (1 : IntInf.int)));

fun pred_list p [] = true
  | pred_list p (x :: xs) = p x andalso pred_list p xs;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun the (SOME x2) = x2;

fun word_next A_ a =
  (if equal_word (len0_len A_) a (max_word A_) then max_word A_
    else plus_worda (len0_len A_) a (one_worda (len0_len A_)));

fun word_prev A_ a =
  (if equal_word (len0_len A_) a (zero_worda (len0_len A_))
    then zero_worda (len0_len A_)
    else minus_word (len0_len A_) a (one_worda (len0_len A_)));

fun mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

fun div_nat m n = Nat (div_integer (integer_of_nat m) (integer_of_nat n));

fun divmod_nat m n = (div_nat m n, mod_nat m n);

fun add_match m rs = map (fn Rule (ma, a) => Rule (MatchAnd (m, ma), a)) rs;

fun getNeg [] = []
  | getNeg (Neg x :: xs) = x :: getNeg xs
  | getNeg (Pos v :: xs) = getNeg xs;

fun getPos [] = []
  | getPos (Pos x :: xs) = x :: getPos xs
  | getPos (Neg v :: xs) = getPos xs;

fun invert (Pos x) = Neg x
  | invert (Neg x) = Pos x;

fun bitrange_UNIV A_ = Bitrange (zero_worda (len0_len A_), max_word A_);

fun empty_Bitrange A_ =
  Bitrange (one_worda (len0_len A_), zero_worda (len0_len A_));

fun bitrange_empty A_ (Bitrange (s, e)) = less_word (len0_len A_) e s
  | bitrange_empty A_ (RangeUnion (r1, r2)) =
    bitrange_empty A_ r1 andalso bitrange_empty A_ r2;

fun bitrange_union A_ r1 r2 = RangeUnion (r1, r2);

fun rmMatchFalse [] = []
  | rmMatchFalse (Rule (MatchNot MatchAny, uu) :: rs) = rmMatchFalse rs
  | rmMatchFalse (Rule (Match vb, va) :: rs) =
    Rule (Match vb, va) :: rmMatchFalse rs
  | rmMatchFalse (Rule (MatchNot (Match vc), va) :: rs) =
    Rule (MatchNot (Match vc), va) :: rmMatchFalse rs
  | rmMatchFalse (Rule (MatchNot (MatchNot vc), va) :: rs) =
    Rule (MatchNot (MatchNot vc), va) :: rmMatchFalse rs
  | rmMatchFalse (Rule (MatchNot (MatchAnd (vc, vd)), va) :: rs) =
    Rule (MatchNot (MatchAnd (vc, vd)), va) :: rmMatchFalse rs
  | rmMatchFalse (Rule (MatchAnd (vb, vc), va) :: rs) =
    Rule (MatchAnd (vb, vc), va) :: rmMatchFalse rs
  | rmMatchFalse (Rule (MatchAny, va) :: rs) =
    Rule (MatchAny, va) :: rmMatchFalse rs;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun invertt (n, a) = (n, invert a);

fun bitrange_setminus A_ (Bitrange (s, e)) (Bitrange (ms, me)) =
  (if less_word (len0_len A_) e s orelse less_word (len0_len A_) me ms
    then Bitrange (s, e)
    else (if less_eq_word (len0_len A_) e me
           then Bitrange
                  ((if equal_word (len0_len A_) ms (zero_worda (len0_len A_))
                     then one_worda (len0_len A_) else s),
                    min (ord_word (len0_len A_)) e (word_prev A_ ms))
           else (if less_eq_word (len0_len A_) ms s
                  then Bitrange
                         (max (ord_word (len0_len A_)) s (word_next A_ me),
                           (if equal_word (len0_len A_) me (max_word A_)
                             then zero_worda (len0_len A_) else e))
                  else RangeUnion
                         (Bitrange
                            ((if equal_word (len0_len A_) ms
                                   (zero_worda (len0_len A_))
                               then one_worda (len0_len A_) else s),
                              word_prev A_ ms),
                           Bitrange
                             (word_next A_ me,
                               (if equal_word (len0_len A_) me (max_word A_)
                                 then zero_worda (len0_len A_) else e))))))
  | bitrange_setminus A_ (RangeUnion (r1, r2)) t =
    RangeUnion (bitrange_setminus A_ r1 t, bitrange_setminus A_ r2 t)
  | bitrange_setminus A_ (Bitrange (v, va)) (RangeUnion (r1, r2)) =
    bitrange_setminus A_ (bitrange_setminus A_ (Bitrange (v, va)) r1) r2;

fun bitrange_invert A_ r = bitrange_setminus A_ (bitrange_UNIV A_) r;

fun bitrange_subset A_ r1 r2 = bitrange_empty A_ (bitrange_setminus A_ r1 r2);

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun of_nat A_ n =
  (if equal_nata n zero_nat
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
                A_)
    else let
           val (m, q) = divmod_nat n (nat_of_integer (2 : IntInf.int));
           val ma =
             times ((times_power o power_monoid_mult o
                      monoid_mult_semiring_numeral o
                      semiring_numeral_semiring_1)
                     A_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1) A_)
                 (Bit0 One))
               (of_nat A_ m);
         in
           (if equal_nata q zero_nat then ma
             else plus ((plus_semigroup_add o semigroup_add_numeral o
                          numeral_semiring_numeral o
                          semiring_numeral_semiring_1)
                         A_)
                    ma (one ((one_numeral o numeral_semiring_numeral o
                               semiring_numeral_semiring_1)
                              A_)))
         end);

fun ipv4addr_of_nat n =
  of_nat
    (semiring_1_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    n;

fun ipv4range_empty rg =
  bitrange_empty (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
    rg;

fun ipv4range_range ip_start ip_end = Bitrange (ip_start, ip_end);

fun nat_of_ipv4addr a =
  unat (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) a;

fun bitrange_to_list A_ (RangeUnion (r1, r2)) =
  bitrange_to_list A_ r1 @ bitrange_to_list A_ r2
  | bitrange_to_list A_ (Bitrange (v, va)) =
    (if bitrange_empty A_ (Bitrange (v, va)) then [] else [Bitrange (v, va)]);

fun list_to_bitrange A_ [r] = r
  | list_to_bitrange A_ (r :: v :: va) =
    RangeUnion (r, list_to_bitrange A_ (v :: va))
  | list_to_bitrange A_ [] = empty_Bitrange A_;

fun match_Ln_uncompressed_append
  (UncompressedFormattedMatch (src1, dst1, proto1, extra1))
  (UncompressedFormattedMatch (src2, dst2, proto2, extra2)) =
  UncompressedFormattedMatch
    (src1 @ src2, dst1 @ dst2, proto1 @ proto2, extra1 @ extra2);

fun iptrule_match_collect MatchAny accu = accu
  | iptrule_match_collect (Match (Src ip))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (Pos ip :: src, dst, proto, extra)
  | iptrule_match_collect (Match (Dst ip))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, Pos ip :: dst, proto, extra)
  | iptrule_match_collect (Match (Prot p))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, dst, Pos p :: proto, extra)
  | iptrule_match_collect (Match (Extra e))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, dst, proto, Pos e :: extra)
  | iptrule_match_collect (MatchNot (Match (Src ip)))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (Neg ip :: src, dst, proto, extra)
  | iptrule_match_collect (MatchNot (Match (Dst ip)))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, Neg ip :: dst, proto, extra)
  | iptrule_match_collect (MatchNot (Match (Prot p)))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, dst, Neg p :: proto, extra)
  | iptrule_match_collect (MatchNot (Match (Extra e)))
    (UncompressedFormattedMatch (src, dst, proto, extra)) =
    UncompressedFormattedMatch (src, dst, proto, Neg e :: extra)
  | iptrule_match_collect (MatchAnd (m1, m2)) fmt =
    match_Ln_uncompressed_append (iptrule_match_collect m1 fmt)
      (match_Ln_uncompressed_append (iptrule_match_collect m2 fmt) fmt);

fun format_Ln_match m =
  iptrule_match_collect m (UncompressedFormattedMatch ([], [], [], []));

fun ipv4range_single ip = Bitrange (ip, ip);

fun ipv4range_subset r1 r2 =
  bitrange_subset
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun bin_last w =
  equal_int (mod_int w (Int_of_integer (2 : IntInf.int)))
    (Int_of_integer (1 : IntInf.int));

fun ipv4range_setminus r1 r2 =
  bitrange_setminus
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun listprepend [] ns = []
  | listprepend (a :: asa) ns = map (fn b => a :: b) ns @ listprepend asa ns;

fun rw_Reject [] = []
  | rw_Reject (Rule (m, Reject) :: rs) = Rule (m, Drop) :: rw_Reject rs
  | rw_Reject (Rule (v, Accept) :: rs) = Rule (v, Accept) :: rw_Reject rs
  | rw_Reject (Rule (v, Drop) :: rs) = Rule (v, Drop) :: rw_Reject rs
  | rw_Reject (Rule (v, Log) :: rs) = Rule (v, Log) :: rw_Reject rs
  | rw_Reject (Rule (v, Call vb) :: rs) = Rule (v, Call vb) :: rw_Reject rs
  | rw_Reject (Rule (v, Return) :: rs) = Rule (v, Return) :: rw_Reject rs
  | rw_Reject (Rule (v, Empty) :: rs) = Rule (v, Empty) :: rw_Reject rs
  | rw_Reject (Rule (v, Unknown) :: rs) = Rule (v, Unknown) :: rw_Reject rs;

fun normalize_match MatchAny = [MatchAny]
  | normalize_match (Match m) = [Match m]
  | normalize_match (MatchAnd (m1, m2)) =
    maps (fn x => map (fn a => MatchAnd (x, a)) (normalize_match m2))
      (normalize_match m1)
  | normalize_match (MatchNot (MatchAnd (m1, m2))) =
    normalize_match (MatchNot m1) @ normalize_match (MatchNot m2)
  | normalize_match (MatchNot (MatchNot m)) = normalize_match m
  | normalize_match (MatchNot MatchAny) = []
  | normalize_match (MatchNot (Match m)) = [MatchNot (Match m)];

fun normalize_rules [] = []
  | normalize_rules (Rule (m, a) :: rs) =
    map (fn ma => Rule (ma, a)) (normalize_match m) @ normalize_rules rs;

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
          (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun size_list x = gen_length zero_nat x;

fun to_negation_type_nnf MatchAny = []
  | to_negation_type_nnf (Match a) = [Pos a]
  | to_negation_type_nnf (MatchNot (Match a)) = [Neg a]
  | to_negation_type_nnf (MatchAnd (a, b)) =
    to_negation_type_nnf a @ to_negation_type_nnf b;

fun to_packet_set a m =
  PacketSet
    (map (map (fn ma => (ma, Pos a)) o to_negation_type_nnf)
      (normalize_match m));

fun rm_LogEmpty [] = []
  | rm_LogEmpty (Rule (uu, Empty) :: rs) = rm_LogEmpty rs
  | rm_LogEmpty (Rule (uv, Log) :: rs) = rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Accept) :: rs) = Rule (v, Accept) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Drop) :: rs) = Rule (v, Drop) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Reject) :: rs) = Rule (v, Reject) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Call vb) :: rs) = Rule (v, Call vb) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Return) :: rs) = Rule (v, Return) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Unknown) :: rs) = Rule (v, Unknown) :: rm_LogEmpty rs;

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun bitNOT_int x =
  (fn xa => minus_int (uminus_int xa) (Int_of_integer (1 : IntInf.int))) x;

fun bitAND_int x y =
  (if equal_int x zero_int then zero_int
    else (if equal_int x (uminus_int (Int_of_integer (1 : IntInf.int))) then y
           else bit (bitAND_int (bin_rest x) (bin_rest y))
                  (bin_last x andalso bin_last y)));

fun bitOR_int x =
  (fn xa => fn y => bitNOT_int (bitAND_int (bitNOT_int xa) (bitNOT_int y))) x;

fun bitOR_word A_ a b = word_of_int A_ (bitOR_int (uint A_ a) (uint A_ b));

fun bitrange_optimize_same A_ rs =
  list_to_bitrange A_ (remdups (equal_bitrange A_) (bitrange_to_list A_ rs));

fun bitrange_intersection A_ r1 r2 =
  bitrange_optimize_same A_
    (bitrange_setminus A_ (bitrange_union A_ r1 r2)
      (bitrange_union A_ (bitrange_invert A_ r1) (bitrange_invert A_ r2)));

fun get_match (Rule (x1, x2)) = x1;

fun packet_set_union (PacketSet olist1) (PacketSet olist2) =
  PacketSet (olist1 @ olist2);

fun packet_set_opt4_internal_internal A_ cs =
  pred_list
    (fn (m, a) =>
      not (member
            (equal_prod (equal_negation_type A_)
              (equal_negation_type equal_action))
            cs (m, invert a)))
    cs;

fun packet_set_opt4 A_ (PacketSet ps) =
  PacketSet (filter (packet_set_opt4_internal_internal A_) ps);

fun packet_set_opt3 (PacketSet ps) =
  PacketSet (sort_key linorder_nat size_list ps);

fun packet_set_opt2_internal A_ [] = []
  | packet_set_opt2_internal A_ ([] :: ps) = [[]]
  | packet_set_opt2_internal A_ ((v :: va) :: ps) =
    (v :: va) ::
      (if less_eq_nat (size_list (v :: va)) (nat_of_integer (5 : IntInf.int))
        then packet_set_opt2_internal A_
               (filter
                 (fn ass =>
                   not (pred_list
                         (member
                           (equal_prod (equal_negation_type A_)
                             (equal_negation_type equal_action))
                           ass)
                         (v :: va)))
                 ps)
        else packet_set_opt2_internal A_ ps);

fun packet_set_opt2 A_ (PacketSet ps) =
  PacketSet (packet_set_opt2_internal A_ ps);

fun packet_set_opt1 A_ (PacketSet ps) =
  PacketSet
    (map (remdups
           (equal_prod (equal_negation_type A_)
             (equal_negation_type equal_action)))
      (remdups
        (equal_list
          (equal_prod (equal_negation_type A_)
            (equal_negation_type equal_action)))
        ps));

fun packet_set_opt A_ ps =
  packet_set_opt1 A_
    (packet_set_opt2 A_ (packet_set_opt3 (packet_set_opt4 A_ ps)));

fun packet_set_not_internal [] = [[]]
  | packet_set_not_internal (ns :: nss) =
    listprepend (map invertt ns) (packet_set_not_internal nss);

fun packet_set_not (PacketSet ps) = PacketSet (packet_set_not_internal ps);

fun collect_allow_compl_impl_tailrec A_ [] p pAs = pAs
  | collect_allow_compl_impl_tailrec A_ (Rule (m, Accept) :: rs) p pAs =
    collect_allow_compl_impl_tailrec A_ rs
      (packet_set_opt A_ (packet_set_union p (to_packet_set Accept m)))
      (packet_set_union p (packet_set_not (to_packet_set Accept m)) :: pAs)
  | collect_allow_compl_impl_tailrec A_ (Rule (m, Drop) :: rs) p pAs =
    collect_allow_compl_impl_tailrec A_ rs
      (packet_set_opt A_ (packet_set_union p (to_packet_set Drop m))) pAs;

val packet_set_Empty : 'a packet_set = PacketSet [];

fun allow_set_not_inter A_ rs =
  collect_allow_compl_impl_tailrec A_ rs packet_set_Empty [];

fun bitAND_word A_ a b = word_of_int A_ (bitAND_int (uint A_ a) (uint A_ b));

fun bitNOT_word A_ a = word_of_int A_ (bitNOT_int (uint A_ a));

fun get_action (Rule (x1, x2)) = x2;

fun ipv4addr_of_dotteddecimal (a, (b, (c, d))) =
  ipv4addr_of_nat
    (plus_nat
      (plus_nat (plus_nat d (times_nat (nat_of_integer (256 : IntInf.int)) c))
        (times_nat (nat_of_integer (65536 : IntInf.int)) b))
      (times_nat (nat_of_integer (16777216 : IntInf.int)) a));

fun ipv4range_set_from_bitmask_to_executable_ipv4range
  (Ip4AddrNetmask (pre, len)) =
  ipv4range_range
    (bitAND_word
      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
      (ipv4addr_of_dotteddecimal pre)
      (shiftl_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (mask (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          len)
        (minus_nat (nat_of_integer (32 : IntInf.int)) len)))
    (bitOR_word
      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
      (ipv4addr_of_dotteddecimal pre)
      (mask (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
        (minus_nat (nat_of_integer (32 : IntInf.int)) len)))
  | ipv4range_set_from_bitmask_to_executable_ipv4range (Ip4Addr ip) =
    ipv4range_single (ipv4addr_of_dotteddecimal ip);

fun ipv4range_intersection r1 r2 =
  bitrange_intersection
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun intersect_netmask_empty_executable x =
  (fn base1 => fn m1 => fn base2 => fn m2 =>
    ipv4range_empty
      (ipv4range_intersection
        (ipv4range_set_from_bitmask_to_executable_ipv4range
          (Ip4AddrNetmask (base1, m1)))
        (ipv4range_set_from_bitmask_to_executable_ipv4range
          (Ip4AddrNetmask (base2, m2)))))
    x;

fun intersect_netmask_empty x = intersect_netmask_empty_executable x;

fun subset_netmask_executable x =
  (fn base1 => fn m1 => fn base2 => fn m2 =>
    ipv4range_subset
      (ipv4range_set_from_bitmask_to_executable_ipv4range
        (Ip4AddrNetmask (base1, m1)))
      (ipv4range_set_from_bitmask_to_executable_ipv4range
        (Ip4AddrNetmask (base2, m2))))
    x;

fun subset_netmask x = subset_netmask_executable x;

fun intersect_ips (Ip4Addr ip) (Ip4AddrNetmask (base, m)) =
  (if less_eq_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (bitAND_word
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          (ipv4addr_of_dotteddecimal base)
          (shiftl_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (mask (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              m)
            (minus_nat (nat_of_integer (32 : IntInf.int)) m)))
        (ipv4addr_of_dotteddecimal ip) andalso
        less_eq_word
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          (ipv4addr_of_dotteddecimal ip)
          (bitOR_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (ipv4addr_of_dotteddecimal base)
            (mask (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
              (minus_nat (nat_of_integer (32 : IntInf.int)) m)))
    then SOME (Ip4Addr ip) else NONE)
  | intersect_ips (Ip4AddrNetmask (base, m)) (Ip4Addr ip) =
    (if less_eq_word
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          (bitAND_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (ipv4addr_of_dotteddecimal base)
            (shiftl_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (mask (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                m)
              (minus_nat (nat_of_integer (32 : IntInf.int)) m)))
          (ipv4addr_of_dotteddecimal ip) andalso
          less_eq_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (ipv4addr_of_dotteddecimal ip)
            (bitOR_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (ipv4addr_of_dotteddecimal base)
              (mask (len_bit0
                      (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                (minus_nat (nat_of_integer (32 : IntInf.int)) m)))
      then SOME (Ip4Addr ip) else NONE)
  | intersect_ips (Ip4Addr ip1) (Ip4Addr ip2) =
    (if equal_word
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          (ipv4addr_of_dotteddecimal ip2) (ipv4addr_of_dotteddecimal ip1)
      then SOME (Ip4Addr ip1) else NONE)
  | intersect_ips (Ip4AddrNetmask (base1, m1)) (Ip4AddrNetmask (base2, m2)) =
    (if intersect_netmask_empty base1 m1 base2 m2 then NONE
      else (if subset_netmask base1 m1 base2 m2
             then SOME (Ip4AddrNetmask (base1, m1))
             else (if subset_netmask base2 m2 base1 m1
                    then SOME (Ip4AddrNetmask (base2, m2)) else NONE)));

fun compress_pos_ips [] =
  SOME (Ip4AddrNetmask ((zero_nat, (zero_nat, (zero_nat, zero_nat))), zero_nat))
  | compress_pos_ips [ip] = SOME ip
  | compress_pos_ips (a :: b :: cs) =
    (case intersect_ips a b of NONE => NONE
      | SOME x => compress_pos_ips (x :: cs));

fun collect_to_range [] =
  empty_Bitrange (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
  | collect_to_range (r :: rs) =
    RangeUnion
      (ipv4range_set_from_bitmask_to_executable_ipv4range r,
        collect_to_range rs);

fun compress_ips l =
  (if null (getPos l) then SOME l
    else (case compress_pos_ips (getPos l) of NONE => NONE
           | SOME ip =>
             (if ipv4range_empty
                   (ipv4range_setminus
                     (ipv4range_set_from_bitmask_to_executable_ipv4range ip)
                     (collect_to_range (getNeg l)))
               then NONE else SOME (Pos ip :: map Neg (getNeg l)))));

val packet_set_UNIV : 'a packet_set = PacketSet [[]];

fun shiftr_word A_ w n = funpow n (shiftr1 A_) w;

fun equal_packet_set A_ (PacketSet x) (PacketSet ya) =
  equal_lista
    (equal_list
      (equal_prod (equal_negation_type A_) (equal_negation_type equal_action)))
    x ya;

fun deny_set rs =
  filter (fn a => not (equal_packet_set equal_iptrule_match a packet_set_UNIV))
    (map (packet_set_opt equal_iptrule_match)
      (allow_set_not_inter equal_iptrule_match rs));

fun process_ret [] = []
  | process_ret (Rule (m, Return) :: rs) =
    add_match (MatchNot m) (process_ret rs)
  | process_ret (Rule (v, Accept) :: rs) = Rule (v, Accept) :: process_ret rs
  | process_ret (Rule (v, Drop) :: rs) = Rule (v, Drop) :: process_ret rs
  | process_ret (Rule (v, Log) :: rs) = Rule (v, Log) :: process_ret rs
  | process_ret (Rule (v, Reject) :: rs) = Rule (v, Reject) :: process_ret rs
  | process_ret (Rule (v, Call vb) :: rs) = Rule (v, Call vb) :: process_ret rs
  | process_ret (Rule (v, Empty) :: rs) = Rule (v, Empty) :: process_ret rs
  | process_ret (Rule (v, Unknown) :: rs) = Rule (v, Unknown) :: process_ret rs;

fun compress_Ln_ips [] = []
  | compress_Ln_ips
    ((UncompressedFormattedMatch (src, dst, proto, extra), a) :: rs) =
    (case (compress_ips src, compress_ips dst)
      of (NONE, xa) => compress_Ln_ips rs
      | (SOME aa, NONE) => compress_Ln_ips rs
      | (SOME aa, SOME dsta) =>
        (UncompressedFormattedMatch (aa, dsta, proto, extra), a) ::
          compress_Ln_ips rs);

fun process_call gamma [] = []
  | process_call gamma (Rule (m, Call chain) :: rs) =
    add_match m (process_ret (the (gamma chain))) @ process_call gamma rs
  | process_call gamma (Rule (v, Accept) :: rs) =
    Rule (v, Accept) :: process_call gamma rs
  | process_call gamma (Rule (v, Drop) :: rs) =
    Rule (v, Drop) :: process_call gamma rs
  | process_call gamma (Rule (v, Log) :: rs) =
    Rule (v, Log) :: process_call gamma rs
  | process_call gamma (Rule (v, Reject) :: rs) =
    Rule (v, Reject) :: process_call gamma rs
  | process_call gamma (Rule (v, Return) :: rs) =
    Rule (v, Return) :: process_call gamma rs
  | process_call gamma (Rule (v, Empty) :: rs) =
    Rule (v, Empty) :: process_call gamma rs
  | process_call gamma (Rule (v, Unknown) :: rs) =
    Rule (v, Unknown) :: process_call gamma rs;

fun opt_simple_matcher (Match (Prot ProtAll)) = MatchAny
  | opt_simple_matcher (Match (Src (Ip4Addr va))) = Match (Src (Ip4Addr va))
  | opt_simple_matcher (Match (Dst (Ip4Addr va))) = Match (Dst (Ip4Addr va))
  | opt_simple_matcher (Match (Prot ProtTCP)) = Match (Prot ProtTCP)
  | opt_simple_matcher (Match (Prot ProtUDP)) = Match (Prot ProtUDP)
  | opt_simple_matcher (Match (Extra v)) = Match (Extra v)
  | opt_simple_matcher (MatchNot m) = MatchNot (opt_simple_matcher m)
  | opt_simple_matcher (MatchAnd (m1, m2)) =
    MatchAnd (opt_simple_matcher m1, opt_simple_matcher m2)
  | opt_simple_matcher MatchAny = MatchAny
  | opt_simple_matcher
    (Match (Src (Ip4AddrNetmask ((ve, (vg, (vi, via))), vc)))) =
    (if equal_nata vc zero_nat
      then (if equal_nata via zero_nat
             then (if equal_nata vi zero_nat
                    then (if equal_nata vg zero_nat
                           then (if equal_nata ve zero_nat then MatchAny
                                  else Match
 (Src (Ip4AddrNetmask
        ((suc (minus_nat ve one_nat), (zero_nat, (zero_nat, zero_nat))),
          zero_nat))))
                           else Match (Src
(Ip4AddrNetmask
  ((ve, (suc (minus_nat vg one_nat), (zero_nat, zero_nat))), zero_nat))))
                    else Match (Src (Ip4AddrNetmask
                                      ((ve,
 (vg, (suc (minus_nat vi one_nat), zero_nat))),
zero_nat))))
             else Match (Src (Ip4AddrNetmask
                               ((ve, (vg, (vi, suc (minus_nat via one_nat)))),
                                 zero_nat))))
      else Match (Src (Ip4AddrNetmask
                        ((ve, (vg, (vi, via))), suc (minus_nat vc one_nat)))))
  | opt_simple_matcher
    (Match (Dst (Ip4AddrNetmask ((ve, (vg, (vi, via))), vc)))) =
    (if equal_nata vc zero_nat
      then (if equal_nata via zero_nat
             then (if equal_nata vi zero_nat
                    then (if equal_nata vg zero_nat
                           then (if equal_nata ve zero_nat then MatchAny
                                  else Match
 (Dst (Ip4AddrNetmask
        ((suc (minus_nat ve one_nat), (zero_nat, (zero_nat, zero_nat))),
          zero_nat))))
                           else Match (Dst
(Ip4AddrNetmask
  ((ve, (suc (minus_nat vg one_nat), (zero_nat, zero_nat))), zero_nat))))
                    else Match (Dst (Ip4AddrNetmask
                                      ((ve,
 (vg, (suc (minus_nat vi one_nat), zero_nat))),
zero_nat))))
             else Match (Dst (Ip4AddrNetmask
                               ((ve, (vg, (vi, suc (minus_nat via one_nat)))),
                                 zero_nat))))
      else Match (Dst (Ip4AddrNetmask
                        ((ve, (vg, (vi, via))), suc (minus_nat vc one_nat)))));

fun dotteddecimal_of_ipv4addr a =
  (nat_of_ipv4addr
     (bitAND_word
       (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
       (shiftr_word
         (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) a
         (nat_of_integer (24 : IntInf.int)))
       (word_of_int
         (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
         (Int_of_integer (255 : IntInf.int)))),
    (nat_of_ipv4addr
       (bitAND_word
         (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
         (shiftr_word
           (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
           a (nat_of_integer (16 : IntInf.int)))
         (word_of_int
           (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
           (Int_of_integer (255 : IntInf.int)))),
      (nat_of_ipv4addr
         (bitAND_word
           (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
           (shiftr_word
             (len0_bit0
               (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
             a (nat_of_integer (8 : IntInf.int)))
           (word_of_int
             (len0_bit0
               (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
             (Int_of_integer (255 : IntInf.int)))),
        nat_of_ipv4addr
          (bitAND_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            a (word_of_int
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                (Int_of_integer (255 : IntInf.int)))))));

fun optimize_matches f rs =
  map (fn r => Rule (f (get_match r), get_action r)) rs;

fun optimize_matches_a f rs =
  map (fn r => Rule (f (get_action r) (get_match r), get_action r)) rs;

fun equal_match_expr A_ (MatchAnd (match_expr1, match_expr2)) MatchAny = false
  | equal_match_expr A_ MatchAny (MatchAnd (match_expr1, match_expr2)) = false
  | equal_match_expr A_ (MatchNot match_expr) MatchAny = false
  | equal_match_expr A_ MatchAny (MatchNot match_expr) = false
  | equal_match_expr A_ (MatchNot match_expr)
    (MatchAnd (match_expr1, match_expr2)) = false
  | equal_match_expr A_ (MatchAnd (match_expr1, match_expr2))
    (MatchNot match_expr) = false
  | equal_match_expr A_ (Match a) MatchAny = false
  | equal_match_expr A_ MatchAny (Match a) = false
  | equal_match_expr A_ (Match a) (MatchAnd (match_expr1, match_expr2)) = false
  | equal_match_expr A_ (MatchAnd (match_expr1, match_expr2)) (Match a) = false
  | equal_match_expr A_ (Match a) (MatchNot match_expr) = false
  | equal_match_expr A_ (MatchNot match_expr) (Match a) = false
  | equal_match_expr A_ (MatchAnd (match_expr1a, match_expr2a))
    (MatchAnd (match_expr1, match_expr2)) =
    equal_match_expr A_ match_expr1a match_expr1 andalso
      equal_match_expr A_ match_expr2a match_expr2
  | equal_match_expr A_ (MatchNot match_expra) (MatchNot match_expr) =
    equal_match_expr A_ match_expra match_expr
  | equal_match_expr A_ (Match aa) (Match a) = eq A_ aa a
  | equal_match_expr A_ MatchAny MatchAny = true;

fun opt_simple_matcher_in_doubt_deny_extra uu MatchAny = MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Accept (Match (Extra uv)) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Reject (Match (Extra uw)) = MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Drop (Match (Extra ux)) = MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Drop (Match (Src v)) = Match (Src v)
  | opt_simple_matcher_in_doubt_deny_extra Drop (Match (Dst v)) = Match (Dst v)
  | opt_simple_matcher_in_doubt_deny_extra Drop (Match (Prot v)) =
    Match (Prot v)
  | opt_simple_matcher_in_doubt_deny_extra Log (Match m) = Match m
  | opt_simple_matcher_in_doubt_deny_extra Reject (Match (Src v)) =
    Match (Src v)
  | opt_simple_matcher_in_doubt_deny_extra Reject (Match (Dst v)) =
    Match (Dst v)
  | opt_simple_matcher_in_doubt_deny_extra Reject (Match (Prot v)) =
    Match (Prot v)
  | opt_simple_matcher_in_doubt_deny_extra (Call v) (Match m) = Match m
  | opt_simple_matcher_in_doubt_deny_extra Return (Match m) = Match m
  | opt_simple_matcher_in_doubt_deny_extra Empty (Match m) = Match m
  | opt_simple_matcher_in_doubt_deny_extra Unknown (Match m) = Match m
  | opt_simple_matcher_in_doubt_deny_extra uy (Match (Src v)) = Match (Src v)
  | opt_simple_matcher_in_doubt_deny_extra uy (Match (Dst v)) = Match (Dst v)
  | opt_simple_matcher_in_doubt_deny_extra uy (Match (Prot v)) = Match (Prot v)
  | opt_simple_matcher_in_doubt_deny_extra Reject (MatchNot (Match (Extra uz)))
    = MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot (Match (Extra va))) =
    MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot (Match (Extra vb)))
    = MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra a (MatchNot (MatchNot m)) =
    opt_simple_matcher_in_doubt_deny_extra a m
  | opt_simple_matcher_in_doubt_deny_extra a (MatchNot (MatchAnd (m1, m2))) =
    (if equal_match_expr equal_iptrule_match
          (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1))
          MatchAny orelse
          equal_match_expr equal_iptrule_match
            (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2)) MatchAny
      then MatchAny
      else (if equal_match_expr equal_iptrule_match
                 (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1))
                 (MatchNot MatchAny)
             then opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2)
             else (if equal_match_expr equal_iptrule_match
                        (opt_simple_matcher_in_doubt_deny_extra a (MatchNot m2))
                        (MatchNot MatchAny)
                    then opt_simple_matcher_in_doubt_deny_extra a (MatchNot m1)
                    else MatchNot (MatchAnd (m1, m2)))))
  | opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_deny_extra Accept (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_deny_extra Drop (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Log (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_deny_extra Log (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra (Call v) (MatchNot (Match va)) =
    MatchNot (Match va)
  | opt_simple_matcher_in_doubt_deny_extra (Call v) (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Return (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_deny_extra Return (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Empty (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_deny_extra Empty (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra Unknown (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_deny_extra Unknown (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra vc (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_deny_extra vc (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_deny_extra vc (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_deny_extra vc (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_deny_extra a (MatchAnd (m1, m2)) =
    MatchAnd
      (opt_simple_matcher_in_doubt_deny_extra a m1,
        opt_simple_matcher_in_doubt_deny_extra a m2);

fun opt_MatchAny_match_expr MatchAny = MatchAny
  | opt_MatchAny_match_expr (Match a) = Match a
  | opt_MatchAny_match_expr (MatchNot (MatchNot m)) = opt_MatchAny_match_expr m
  | opt_MatchAny_match_expr (MatchNot (Match v)) =
    MatchNot (opt_MatchAny_match_expr (Match v))
  | opt_MatchAny_match_expr (MatchNot (MatchAnd (v, va))) =
    MatchNot (opt_MatchAny_match_expr (MatchAnd (v, va)))
  | opt_MatchAny_match_expr (MatchNot MatchAny) =
    MatchNot (opt_MatchAny_match_expr MatchAny)
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, MatchAny)) = MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, Match v)) = Match v
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, MatchNot v)) = MatchNot v
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, MatchAnd (v, va))) =
    MatchAnd (v, va)
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchAny)) = Match v
  | opt_MatchAny_match_expr (MatchAnd (MatchNot v, MatchAny)) = MatchNot v
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), MatchAny)) =
    MatchAnd (v, va)
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchNot MatchAny)) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchNot v, MatchNot MatchAny)) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), MatchNot MatchAny)) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny, Match v)) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny, MatchNot (Match va)))
    = MatchNot MatchAny
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot MatchAny, MatchNot (MatchNot va))) = MatchNot MatchAny
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot MatchAny, MatchNot (MatchAnd (va, vb)))) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (MatchNot MatchAny, MatchAnd (v, va))) =
    MatchNot MatchAny
  | opt_MatchAny_match_expr (MatchAnd (Match v, Match va)) =
    MatchAnd
      (opt_MatchAny_match_expr (Match v), opt_MatchAny_match_expr (Match va))
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchNot (Match vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (Match v),
        opt_MatchAny_match_expr (MatchNot (Match vb)))
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchNot (MatchNot vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (Match v),
        opt_MatchAny_match_expr (MatchNot (MatchNot vb)))
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchNot (MatchAnd (vb, vc)))) =
    MatchAnd
      (opt_MatchAny_match_expr (Match v),
        opt_MatchAny_match_expr (MatchNot (MatchAnd (vb, vc))))
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchAnd (va, vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (Match v),
        opt_MatchAny_match_expr (MatchAnd (va, vb)))
  | opt_MatchAny_match_expr (MatchAnd (MatchNot (Match vb), Match va)) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (Match vb)),
        opt_MatchAny_match_expr (Match va))
  | opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchNot vb), Match va)) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchNot vb)),
        opt_MatchAny_match_expr (Match va))
  | opt_MatchAny_match_expr (MatchAnd (MatchNot (MatchAnd (vb, vc)), Match va))
    = MatchAnd
        (opt_MatchAny_match_expr (MatchNot (MatchAnd (vb, vc))),
          opt_MatchAny_match_expr (Match va))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (Match va), MatchNot (Match vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (Match va)),
        opt_MatchAny_match_expr (MatchNot (Match vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchNot va), MatchNot (Match vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchNot va)),
        opt_MatchAny_match_expr (MatchNot (Match vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchAnd (va, vc)), MatchNot (Match vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchAnd (va, vc))),
        opt_MatchAny_match_expr (MatchNot (Match vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (Match va), MatchNot (MatchNot vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (Match va)),
        opt_MatchAny_match_expr (MatchNot (MatchNot vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchNot va), MatchNot (MatchNot vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchNot va)),
        opt_MatchAny_match_expr (MatchNot (MatchNot vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchAnd (va, vc)), MatchNot (MatchNot vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchAnd (va, vc))),
        opt_MatchAny_match_expr (MatchNot (MatchNot vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (Match va), MatchNot (MatchAnd (vb, vc)))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (Match va)),
        opt_MatchAny_match_expr (MatchNot (MatchAnd (vb, vc))))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchNot va), MatchNot (MatchAnd (vb, vc)))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchNot va)),
        opt_MatchAny_match_expr (MatchNot (MatchAnd (vb, vc))))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchAnd (va, vd)), MatchNot (MatchAnd (vb, vc)))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchAnd (va, vd))),
        opt_MatchAny_match_expr (MatchNot (MatchAnd (vb, vc))))
  | opt_MatchAny_match_expr (MatchAnd (MatchNot (Match vc), MatchAnd (va, vb)))
    = MatchAnd
        (opt_MatchAny_match_expr (MatchNot (Match vc)),
          opt_MatchAny_match_expr (MatchAnd (va, vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchNot vc), MatchAnd (va, vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchNot vc)),
        opt_MatchAny_match_expr (MatchAnd (va, vb)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchNot (MatchAnd (vc, vd)), MatchAnd (va, vb))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchNot (MatchAnd (vc, vd))),
        opt_MatchAny_match_expr (MatchAnd (va, vb)))
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), Match vb)) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchAnd (v, va)),
        opt_MatchAny_match_expr (Match vb))
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), MatchNot (Match vc))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchAnd (v, va)),
        opt_MatchAny_match_expr (MatchNot (Match vc)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchAnd (v, va), MatchNot (MatchNot vc))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchAnd (v, va)),
        opt_MatchAny_match_expr (MatchNot (MatchNot vc)))
  | opt_MatchAny_match_expr
    (MatchAnd (MatchAnd (v, va), MatchNot (MatchAnd (vc, vd)))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchAnd (v, va)),
        opt_MatchAny_match_expr (MatchNot (MatchAnd (vc, vd))))
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), MatchAnd (vb, vc))) =
    MatchAnd
      (opt_MatchAny_match_expr (MatchAnd (v, va)),
        opt_MatchAny_match_expr (MatchAnd (vb, vc)));

fun lower_closure rs =
  rmMatchFalse
    (funpow (nat_of_integer (2000 : IntInf.int))
      (optimize_matches opt_MatchAny_match_expr)
      (optimize_matches_a opt_simple_matcher_in_doubt_deny_extra rs));

fun map_of_string rs = map_of (equal_list equal_char) rs;

fun opt_simple_matcher_in_doubt_allow_extra uu MatchAny = MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Accept (Match (Extra uv)) = MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Reject (Match (Extra uw)) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Drop (Match (Extra ux)) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Drop (Match (Src v)) = Match (Src v)
  | opt_simple_matcher_in_doubt_allow_extra Drop (Match (Dst v)) = Match (Dst v)
  | opt_simple_matcher_in_doubt_allow_extra Drop (Match (Prot v)) =
    Match (Prot v)
  | opt_simple_matcher_in_doubt_allow_extra Log (Match m) = Match m
  | opt_simple_matcher_in_doubt_allow_extra Reject (Match (Src v)) =
    Match (Src v)
  | opt_simple_matcher_in_doubt_allow_extra Reject (Match (Dst v)) =
    Match (Dst v)
  | opt_simple_matcher_in_doubt_allow_extra Reject (Match (Prot v)) =
    Match (Prot v)
  | opt_simple_matcher_in_doubt_allow_extra (Call v) (Match m) = Match m
  | opt_simple_matcher_in_doubt_allow_extra Return (Match m) = Match m
  | opt_simple_matcher_in_doubt_allow_extra Empty (Match m) = Match m
  | opt_simple_matcher_in_doubt_allow_extra Unknown (Match m) = Match m
  | opt_simple_matcher_in_doubt_allow_extra uy (Match (Src v)) = Match (Src v)
  | opt_simple_matcher_in_doubt_allow_extra uy (Match (Dst v)) = Match (Dst v)
  | opt_simple_matcher_in_doubt_allow_extra uy (Match (Prot v)) = Match (Prot v)
  | opt_simple_matcher_in_doubt_allow_extra Accept (MatchNot (Match (Extra uz)))
    = MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot (Match (Extra va))) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot (Match (Extra vb)))
    = MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchNot m)) =
    opt_simple_matcher_in_doubt_allow_extra a m
  | opt_simple_matcher_in_doubt_allow_extra a (MatchNot (MatchAnd (m1, m2))) =
    (if equal_match_expr equal_iptrule_match
          (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1))
          MatchAny orelse
          equal_match_expr equal_iptrule_match
            (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2)) MatchAny
      then MatchAny
      else (if equal_match_expr equal_iptrule_match
                 (opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1))
                 (MatchNot MatchAny)
             then opt_simple_matcher_in_doubt_allow_extra a (MatchNot m2)
             else (if equal_match_expr equal_iptrule_match
                        (opt_simple_matcher_in_doubt_allow_extra a
                          (MatchNot m2))
                        (MatchNot MatchAny)
                    then opt_simple_matcher_in_doubt_allow_extra a (MatchNot m1)
                    else MatchNot (MatchAnd (m1, m2)))))
  | opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_allow_extra Drop (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Log (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_allow_extra Log (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot (Match (Prot va)))
    = MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_allow_extra Reject (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra (Call v) (MatchNot (Match va)) =
    MatchNot (Match va)
  | opt_simple_matcher_in_doubt_allow_extra (Call v) (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Return (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_allow_extra Return (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Empty (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_allow_extra Empty (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra Unknown (MatchNot (Match v)) =
    MatchNot (Match v)
  | opt_simple_matcher_in_doubt_allow_extra Unknown (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra vc (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | opt_simple_matcher_in_doubt_allow_extra vc (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | opt_simple_matcher_in_doubt_allow_extra vc (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | opt_simple_matcher_in_doubt_allow_extra vc (MatchNot MatchAny) =
    MatchNot MatchAny
  | opt_simple_matcher_in_doubt_allow_extra a (MatchAnd (m1, m2)) =
    MatchAnd
      (opt_simple_matcher_in_doubt_allow_extra a m1,
        opt_simple_matcher_in_doubt_allow_extra a m2);

fun upper_closure rs =
  rmMatchFalse
    (funpow (nat_of_integer (2000 : IntInf.int))
      (optimize_matches opt_MatchAny_match_expr)
      (optimize_matches_a opt_simple_matcher_in_doubt_allow_extra rs));

fun format_Ln_rules_uncompressed rs =
  map (fn r => (format_Ln_match (get_match r), get_action r))
    (normalize_rules rs);

fun does_I_has_compressed_prots [] = []
  | does_I_has_compressed_prots
    ((UncompressedFormattedMatch (src, dst, [], []), a) :: rs) =
    does_I_has_compressed_prots rs
  | does_I_has_compressed_prots
    ((UncompressedFormattedMatch (src, dst, [proto], []), a) :: rs) =
    does_I_has_compressed_prots rs
  | does_I_has_compressed_prots
    ((UncompressedFormattedMatch (vb, vc, vf :: v :: vd, ve), va) :: rs) =
    (UncompressedFormattedMatch (vb, vc, vf :: v :: vd, ve), va) ::
      does_I_has_compressed_prots rs
  | does_I_has_compressed_prots
    ((UncompressedFormattedMatch (vb, vc, vf :: vg, v :: vd), va) :: rs) =
    (UncompressedFormattedMatch (vb, vc, vf :: vg, v :: vd), va) ::
      does_I_has_compressed_prots rs
  | does_I_has_compressed_prots
    ((UncompressedFormattedMatch (vb, vc, vd, vf :: vg), va) :: rs) =
    (UncompressedFormattedMatch (vb, vc, vd, vf :: vg), va) ::
      does_I_has_compressed_prots rs;

fun does_I_has_compressed_rules [] = []
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch ([], [dst], proto, []), a) :: rs) =
    does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch ([src], [], proto, []), a) :: rs) =
    does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch ([src], [dst], proto, []), a) :: rs) =
    does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch ([], [], proto, []), a) :: rs) =
    does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vf :: v :: vb, vc, vd, ve), va) :: rs) =
    (UncompressedFormattedMatch (vf :: v :: vb, vc, vd, ve), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vf :: vg, v :: vc :: vh, vd, ve), va) :: rs) =
    (UncompressedFormattedMatch (vf :: vg, v :: vc :: vh, vd, ve), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vf :: vg, v :: vb, vd, vc :: vh), va) :: rs) =
    (UncompressedFormattedMatch (vf :: vg, v :: vb, vd, vc :: vh), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vf :: vg, vc, vd, v :: vb), va) :: rs) =
    (UncompressedFormattedMatch (vf :: vg, vc, vd, v :: vb), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch ([], [], vd, v :: vb), va) :: rs) =
    (UncompressedFormattedMatch ([], [], vd, v :: vb), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vb, [], vd, v :: vc), va) :: rs) =
    (UncompressedFormattedMatch (vb, [], vd, v :: vc), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vb, vf :: vh :: vi, vd, ve), va) :: rs) =
    (UncompressedFormattedMatch (vb, vf :: vh :: vi, vd, ve), va) ::
      does_I_has_compressed_rules rs
  | does_I_has_compressed_rules
    ((UncompressedFormattedMatch (vb, vc, vd, vf :: vg), va) :: rs) =
    (UncompressedFormattedMatch (vb, vc, vd, vf :: vg), va) ::
      does_I_has_compressed_rules rs;

fun unfold_ruleset_FORWARD rs =
  funpow (nat_of_integer (10 : IntInf.int))
    (optimize_matches opt_MatchAny_match_expr)
    (optimize_matches opt_simple_matcher
      (rw_Reject
        (rm_LogEmpty
          (funpow (nat_of_integer (5 : IntInf.int)) (process_call rs)
            [Rule (MatchAny,
                    Call [#"F", #"O", #"R", #"W", #"A", #"R", #"D"])]))));

fun bitmask_to_strange_inverse_cisco_mask n =
  dotteddecimal_of_ipv4addr
    (bitNOT_word
      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
      (shiftl_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (mask (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) n)
        (minus_nat (nat_of_integer (32 : IntInf.int)) n)));

end; (*struct Test*)
