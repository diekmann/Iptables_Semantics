structure Test : sig
  type int
  type num
  type nat
  val integer_of_nat : nat -> IntInf.int
  type 'a word
  val nat_of_integer : IntInf.int -> nat
  datatype iface = Iface of char list
  type 'a bit0
  type num1
  type 'a wordinterval
  datatype ipt_ipv4range = Ip4Addr of (nat * (nat * (nat * nat))) |
    Ip4AddrNetmask of (nat * (nat * (nat * nat))) * nat
  datatype primitive_protocol = TCP | UDP | ICMP
  datatype protocol = ProtoAny | Proto of primitive_protocol
  datatype common_primitive = Src of ipt_ipv4range | Dst of ipt_ipv4range |
    IIface of iface | OIface of iface | Prot of protocol |
    Src_Ports of
      (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) list
    | Dst_Ports of
        (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) list
    | Extra of char list
  type nibble
  datatype 'a match_expr = Match of 'a | MatchNot of 'a match_expr |
    MatchAnd of 'a match_expr * 'a match_expr | MatchAny
  datatype action = Accept | Drop | Log | Reject | Call of char list | Return |
    Empty | Unknown
  datatype 'a rule = Rule of 'a match_expr * action
  type ternaryvalue
  type 'a simple_match_ext
  datatype simple_action = Accepta | Dropa
  datatype simple_rule = SimpleRule of unit simple_match_ext * simple_action
  type state
  type 'a simple_packet_ext
  val ifaceAny : iface
  val no_spoofing_iface :
    iface ->
      (iface -> ((num1 bit0 bit0 bit0 bit0 bit0 word * nat) list) option) ->
        common_primitive rule list -> bool
  val dotdecimal_of_ipv4addr :
    num1 bit0 bit0 bit0 bit0 bit0 word -> nat * (nat * (nat * nat))
  val lower_closure : common_primitive rule list -> common_primitive rule list
  val map_of_string :
    (char list * common_primitive rule list) list ->
      char list -> (common_primitive rule list) option
  val port_toString : num1 bit0 bit0 bit0 bit0 word -> char list
  val upper_closure : common_primitive rule list -> common_primitive rule list
  val counter_example : common_primitive rule list -> state
  val iface_toString : char list -> iface -> char list
  val ports_toString :
    char list ->
      num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word -> char list
  val integer_to_16word : IntInf.int -> num1 bit0 bit0 bit0 bit0 word
  val protocol_toString : protocol -> char list
  val ipv4_cidr_toString : num1 bit0 bit0 bit0 bit0 bit0 word * nat -> char list
  val simple_action_toString : simple_action -> char list
  val simple_rule_toString : simple_rule -> char list
  val dst : 'a simple_match_ext -> num1 bit0 bit0 bit0 bit0 bit0 word * nat
  val src : 'a simple_match_ext -> num1 bit0 bit0 bit0 bit0 bit0 word * nat
  val unfold_ruleset_FORWARD :
    (char list -> (common_primitive rule list) option) ->
      common_primitive rule list
  val proto : 'a simple_match_ext -> protocol
  val to_simple_firewall : common_primitive rule list -> simple_rule list
  val dports :
    'a simple_match_ext ->
      num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word
  val iiface : 'a simple_match_ext -> iface
  val oiface : 'a simple_match_ext -> iface
  val sports :
    'a simple_match_ext ->
      num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word
  val example_ipassignment_nospoof : common_primitive rule list -> bool
  val simple_rule_iptables_save_toString : char list -> simple_rule -> char list
  val check_simple_fw_preconditions : common_primitive rule list -> bool
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

val one_nata : nat = Nat (1 : IntInf.int);

val one_nat = {one = one_nata} : nat one;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

val times_nat = {times = times_nata} : nat times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

val top_set : 'a set = Coset [];

fun pred_list p [] = true
  | pred_list p (x :: xs) = p x andalso pred_list p xs;

fun ball (Set xs) p = pred_list p xs;

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

datatype 'a word = Word of int;

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

fun enum_all_word A_ p = ball top_set p;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun enum_ex_word A_ p = bex top_set p;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val zero_nat : nat = Nat (0 : IntInf.int);

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

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

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun abs_integer k = (if IntInf.< (k, (0 : IntInf.int)) then IntInf.~ k else k);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_integer l, s)))
                         end)));

fun snd (x1, x2) = x2;

fun mod_integer k l = snd (divmod_integer k l);

fun mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

fun fst (x1, x2) = x1;

fun div_integer k l = fst (divmod_integer k l);

fun div_nat m n = Nat (div_integer (integer_of_nat m) (integer_of_nat n));

fun divmod_nat m n = (div_nat m n, mod_nat m n);

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

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

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

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

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun power one times a n =
  (if equal_nata n zero_nat then one
    else times a (power one times a (minus_nat n one_nata)));

fun powera A_ = power (one (one_power A_)) (times (times_power A_));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nata;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun mod_int k l =
  Int_of_integer (mod_integer (integer_of_int k) (integer_of_int l));

fun word_of_int A_ k =
  Word (mod_int k
         (powera power_int (Int_of_integer (2 : IntInf.int)) (len_of A_ Type)));

fun uint A_ (Word x) = x;

fun times_worda A_ a b = word_of_int A_ (times_inta (uint A_ a) (uint A_ b));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun zero_worda A_ = word_of_int A_ zero_int;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun plus_worda A_ a b = word_of_int A_ (plus_int (uint A_ a) (uint A_ b));

fun one_worda A_ = word_of_int A_ (Int_of_integer (1 : IntInf.int));

fun times_word A_ = {times = times_worda A_} : 'a word times;

fun semigroup_mult_word A_ = {times_semigroup_mult = times_word A_} :
  'a word semigroup_mult;

fun one_word A_ = {one = one_worda A_} : 'a word one;

fun power_word A_ = {one_power = one_word A_, times_power = times_word A_} :
  'a word power;

fun monoid_mult_word A_ =
  {semigroup_mult_monoid_mult = semigroup_mult_word A_,
    power_monoid_mult = power_word A_}
  : 'a word monoid_mult;

fun plus_word A_ = {plus = plus_worda A_} : 'a word plus;

fun semigroup_add_word A_ = {plus_semigroup_add = plus_word A_} :
  'a word semigroup_add;

fun ab_semigroup_add_word A_ =
  {semigroup_add_ab_semigroup_add = semigroup_add_word A_} :
  'a word ab_semigroup_add;

fun semiring_word A_ =
  {ab_semigroup_add_semiring = ab_semigroup_add_word A_,
    semigroup_mult_semiring = semigroup_mult_word A_}
  : 'a word semiring;

fun numeral_word A_ =
  {one_numeral = one_word A_, semigroup_add_numeral = semigroup_add_word A_} :
  'a word numeral;

fun semiring_numeral_word A_ =
  {monoid_mult_semiring_numeral = monoid_mult_word (len0_len A_),
    numeral_semiring_numeral = numeral_word (len0_len A_),
    semiring_semiring_numeral = semiring_word (len0_len A_)}
  : 'a word semiring_numeral;

fun zero_word A_ = {zero = zero_worda A_} : 'a word zero;

fun zero_neq_one_word A_ =
  {one_zero_neq_one = one_word (len0_len A_),
    zero_zero_neq_one = zero_word (len0_len A_)}
  : 'a word zero_neq_one;

fun monoid_add_word A_ =
  {semigroup_add_monoid_add = semigroup_add_word A_,
    zero_monoid_add = zero_word A_}
  : 'a word monoid_add;

fun comm_monoid_add_word A_ =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_word A_,
    monoid_add_comm_monoid_add = monoid_add_word A_}
  : 'a word comm_monoid_add;

fun mult_zero_word A_ =
  {times_mult_zero = times_word A_, zero_mult_zero = zero_word A_} :
  'a word mult_zero;

fun semiring_0_word A_ =
  {comm_monoid_add_semiring_0 = comm_monoid_add_word A_,
    mult_zero_semiring_0 = mult_zero_word A_,
    semiring_semiring_0 = semiring_word A_}
  : 'a word semiring_0;

fun semiring_1_word A_ =
  {semiring_numeral_semiring_1 = semiring_numeral_word A_,
    semiring_0_semiring_1 = semiring_0_word (len0_len A_),
    zero_neq_one_semiring_1 = zero_neq_one_word A_}
  : 'a word semiring_1;

fun enum_worda A_ =
  map (of_nat (semiring_1_word A_))
    (upt zero_nat
      (powera power_nat (nat_of_integer (2 : IntInf.int))
        (len_of (len0_len A_) Type)));

type 'a finite = {};

type 'a enum =
  {finite_enum : 'a finite, enum : 'a list, enum_all : ('a -> bool) -> bool,
    enum_ex : ('a -> bool) -> bool};
val finite_enum = #finite_enum : 'a enum -> 'a finite;
val enum = #enum : 'a enum -> 'a list;
val enum_all = #enum_all : 'a enum -> ('a -> bool) -> bool;
val enum_ex = #enum_ex : 'a enum -> ('a -> bool) -> bool;

fun finite_word A_ = {} : 'a word finite;

fun enum_word A_ =
  {finite_enum = finite_word (len0_len A_), enum = enum_worda A_,
    enum_all = enum_all_word A_, enum_ex = enum_ex_word A_}
  : 'a word enum;

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

fun equal_worda A_ k l = equal_int (uint A_ k) (uint A_ l);

fun equal_word A_ = {equal = equal_worda A_} : 'a word equal;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun less_eq_word A_ a b = less_eq_int (uint A_ a) (uint A_ b);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun less_word A_ a b = less_int (uint A_ a) (uint A_ b);

fun ord_word A_ = {less_eq = less_eq_word A_, less = less_word A_} :
  'a word ord;

datatype iface = Iface of char list;

val equal_char = {equal = (fn a => fn b => ((a : char) = b))} : char equal;

fun equal_ifacea (Iface x) (Iface ya) = equal_lista equal_char x ya;

val equal_iface = {equal = equal_ifacea} : iface equal;

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ x =
  times_nata (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

datatype num1 = One_num1;

fun len_of_num1 x = one_nata;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype 'a wordinterval = WordInterval of 'a word * 'a word |
  RangeUnion of 'a wordinterval * 'a wordinterval;

fun equal_wordintervala A_ (WordInterval (x11, x12)) (RangeUnion (x21, x22)) =
  false
  | equal_wordintervala A_ (RangeUnion (x21, x22)) (WordInterval (x11, x12)) =
    false
  | equal_wordintervala A_ (RangeUnion (x21, x22)) (RangeUnion (y21, y22)) =
    equal_wordintervala A_ x21 y21 andalso equal_wordintervala A_ x22 y22
  | equal_wordintervala A_ (WordInterval (x11, x12)) (WordInterval (y11, y12)) =
    equal_worda (len0_len A_) x11 y11 andalso equal_worda (len0_len A_) x12 y12;

fun equal_wordinterval A_ = {equal = equal_wordintervala A_} :
  'a wordinterval equal;

datatype ipt_ipv4range = Ip4Addr of (nat * (nat * (nat * nat))) |
  Ip4AddrNetmask of (nat * (nat * (nat * nat))) * nat;

fun equal_ipt_ipv4range (Ip4Addr x1) (Ip4AddrNetmask (x21, x22)) = false
  | equal_ipt_ipv4range (Ip4AddrNetmask (x21, x22)) (Ip4Addr x1) = false
  | equal_ipt_ipv4range (Ip4AddrNetmask (x21, x22)) (Ip4AddrNetmask (y21, y22))
    = equal_proda equal_nat
        (equal_prod equal_nat (equal_prod equal_nat equal_nat)) x21 y21 andalso
        equal_nata x22 y22
  | equal_ipt_ipv4range (Ip4Addr x1) (Ip4Addr y1) =
    equal_proda equal_nat
      (equal_prod equal_nat (equal_prod equal_nat equal_nat)) x1 y1;

datatype primitive_protocol = TCP | UDP | ICMP;

datatype protocol = ProtoAny | Proto of primitive_protocol;

datatype common_primitive = Src of ipt_ipv4range | Dst of ipt_ipv4range |
  IIface of iface | OIface of iface | Prot of protocol |
  Src_Ports of
    (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) list
  | Dst_Ports of
      (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) list
  | Extra of char list;

fun equal_primitive_protocol UDP ICMP = false
  | equal_primitive_protocol ICMP UDP = false
  | equal_primitive_protocol TCP ICMP = false
  | equal_primitive_protocol ICMP TCP = false
  | equal_primitive_protocol TCP UDP = false
  | equal_primitive_protocol UDP TCP = false
  | equal_primitive_protocol ICMP ICMP = true
  | equal_primitive_protocol UDP UDP = true
  | equal_primitive_protocol TCP TCP = true;

fun equal_protocol ProtoAny (Proto x2) = false
  | equal_protocol (Proto x2) ProtoAny = false
  | equal_protocol (Proto x2) (Proto y2) = equal_primitive_protocol x2 y2
  | equal_protocol ProtoAny ProtoAny = true;

fun equal_common_primitivea (Dst_Ports x7) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (Dst_Ports x7) = false
  | equal_common_primitivea (Src_Ports x6) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (Src_Ports x6) = false
  | equal_common_primitivea (Prot x5) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (Prot x5) = false
  | equal_common_primitivea (OIface x4) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (OIface x4) = false
  | equal_common_primitivea (IIface x3) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (IIface x3) = false
  | equal_common_primitivea (Dst x2) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (Dst x2) = false
  | equal_common_primitivea (Src x1) (Extra x8) = false
  | equal_common_primitivea (Extra x8) (Src x1) = false
  | equal_common_primitivea (Src x1) (Dst_Ports x7) = false
  | equal_common_primitivea (Dst_Ports x7) (Src x1) = false
  | equal_common_primitivea (Src x1) (Src_Ports x6) = false
  | equal_common_primitivea (Src_Ports x6) (Src x1) = false
  | equal_common_primitivea (Src x1) (Prot x5) = false
  | equal_common_primitivea (Prot x5) (Src x1) = false
  | equal_common_primitivea (Src x1) (OIface x4) = false
  | equal_common_primitivea (OIface x4) (Src x1) = false
  | equal_common_primitivea (Src x1) (IIface x3) = false
  | equal_common_primitivea (IIface x3) (Src x1) = false
  | equal_common_primitivea (Src x1) (Dst x2) = false
  | equal_common_primitivea (Dst x2) (Src x1) = false
  | equal_common_primitivea (Extra x8) (Extra y8) = equal_lista equal_char x8 y8
  | equal_common_primitivea (Dst_Ports x7) (Dst_Ports y7) =
    equal_lista
      (equal_prod
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))
      x7 y7
  | equal_common_primitivea (Src_Ports x6) (Src_Ports y6) =
    equal_lista
      (equal_prod
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))
      x6 y6
  | equal_common_primitivea (Prot x5) (Prot y5) = equal_protocol x5 y5
  | equal_common_primitivea (OIface x4) (OIface y4) = equal_ifacea x4 y4
  | equal_common_primitivea (IIface x3) (IIface y3) = equal_ifacea x3 y3
  | equal_common_primitivea (Dst x2) (Dst y2) = equal_ipt_ipv4range x2 y2
  | equal_common_primitivea (Src x1) (Src y1) = equal_ipt_ipv4range x1 y1;

val equal_common_primitive = {equal = equal_common_primitivea} :
  common_primitive equal;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype 'a match_expr = Match of 'a | MatchNot of 'a match_expr |
  MatchAnd of 'a match_expr * 'a match_expr | MatchAny;

datatype action = Accept | Drop | Log | Reject | Call of char list | Return |
  Empty | Unknown;

datatype 'a rule = Rule of 'a match_expr * action;

datatype ternaryvalue = TernaryTrue | TernaryFalse | TernaryUnknown;

datatype ternaryformula = TernaryAnd of ternaryformula * ternaryformula |
  TernaryOr of ternaryformula * ternaryformula | TernaryNot of ternaryformula |
  TernaryValue of ternaryvalue;

datatype 'a negation_type = Pos of 'a | Neg of 'a;

datatype 'a simple_match_ext =
  Simple_match_ext of
    iface * iface * (num1 bit0 bit0 bit0 bit0 bit0 word * nat) *
      (num1 bit0 bit0 bit0 bit0 bit0 word * nat) * protocol *
      (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) *
      (num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word) * 'a;

datatype simple_action = Accepta | Dropa;

datatype simple_rule = SimpleRule of unit simple_match_ext * simple_action;

datatype final_decision = FinalAllow | FinalDeny;

datatype state = Undecided | Decision of final_decision;

datatype 'a simple_packet_ext =
  Simple_packet_ext of
    char list * char list * num1 bit0 bit0 bit0 bit0 bit0 word *
      num1 bit0 bit0 bit0 bit0 bit0 word * primitive_protocol *
      num1 bit0 bit0 bit0 bit0 word * num1 bit0 bit0 bit0 bit0 word * 'a;

fun id x = (fn xa => xa) x;

fun nat x = (nat_of_integer o integer_of_int) x;

fun find f [] = NONE
  | find f (x :: xs) = (if f x then SOME x else find f xs);

fun const x = (fn _ => x);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nat then [] else x :: take (minus_nat n one_nata) xs);

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun upto_aux i j js =
  (if less_int j i then js
    else upto_aux i (minus_int j (Int_of_integer (1 : IntInf.int))) (j :: js));

fun upto i j = upto_aux i j [];

fun minus_word A_ a b = word_of_int A_ (minus_int (uint A_ a) (uint A_ b));

fun bit k b =
  plus_int
    (plus_int (if b then Int_of_integer (1 : IntInf.int) else zero_int) k) k;

fun shiftl1 A_ w = word_of_int A_ (bit (uint A_ w) false);

fun funpow n f =
  (if equal_nata n zero_nat then id else f o funpow (minus_nat n one_nata) f);

fun shiftl_word A_ w n = funpow n (shiftl1 A_) w;

fun mask A_ n =
  minus_word (len0_len A_)
    (shiftl_word (len0_len A_) (one_worda (len0_len A_)) n)
    (one_worda (len0_len A_));

fun unat A_ w = nat (uint A_ w);

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun remove A_ x (Coset xs) = Coset (inserta A_ x xs)
  | remove A_ x (Set xs) = Set (removeAll A_ x xs);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun collect A_ p = Set (filter p (enum A_));

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun div_int k l =
  Int_of_integer (div_integer (integer_of_int k) (integer_of_int l));

fun bin_rest w = div_int w (Int_of_integer (2 : IntInf.int));

fun shiftr1 A_ w = word_of_int A_ (bin_rest (uint A_ w));

fun max_word A_ =
  word_of_int (len0_len A_)
    (minus_int
      (powera power_int (Int_of_integer (2 : IntInf.int))
        (len_of (len0_len A_) Type))
      (Int_of_integer (1 : IntInf.int)));

val ifaceAny : iface = Iface [#"+"];

val pfxes : nat list =
  map nat (upto zero_int (Int_of_integer (32 : IntInf.int)));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun internal_iface_name_match [] [] = true
  | internal_iface_name_match (i :: is) [] = ((i : char) = #"+") andalso null is
  | internal_iface_name_match [] (uu :: uv) = false
  | internal_iface_name_match (i :: is) (p_i :: p_is) =
    (if ((i : char) = #"+") andalso null is then true
      else ((p_i : char) = i) andalso internal_iface_name_match is p_is);

fun match_iface (Iface i) p_iface = internal_iface_name_match i p_iface;

fun the (SOME x2) = x2;

fun add_match m rs = map (fn Rule (ma, a) => Rule (MatchAnd (m, ma), a)) rs;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun word_prev A_ a =
  (if equal_worda (len0_len A_) a (zero_worda (len0_len A_))
    then zero_worda (len0_len A_)
    else minus_word (len0_len A_) a (one_worda (len0_len A_)));

fun word_next A_ a =
  (if equal_worda (len0_len A_) a (max_word A_) then max_word A_
    else plus_worda (len0_len A_) a (one_worda (len0_len A_)));

fun wordinterval_setminus A_ (WordInterval (s, e)) (WordInterval (ms, me)) =
  (if less_word (len0_len A_) e s orelse less_word (len0_len A_) me ms
    then WordInterval (s, e)
    else (if less_eq_word (len0_len A_) e me
           then WordInterval
                  ((if equal_worda (len0_len A_) ms (zero_worda (len0_len A_))
                     then one_worda (len0_len A_) else s),
                    min (ord_word (len0_len A_)) e (word_prev A_ ms))
           else (if less_eq_word (len0_len A_) ms s
                  then WordInterval
                         (max (ord_word (len0_len A_)) s (word_next A_ me),
                           (if equal_worda (len0_len A_) me (max_word A_)
                             then zero_worda (len0_len A_) else e))
                  else RangeUnion
                         (WordInterval
                            ((if equal_worda (len0_len A_) ms
                                   (zero_worda (len0_len A_))
                               then one_worda (len0_len A_) else s),
                              word_prev A_ ms),
                           WordInterval
                             (word_next A_ me,
                               (if equal_worda (len0_len A_) me (max_word A_)
                                 then zero_worda (len0_len A_) else e))))))
  | wordinterval_setminus A_ (RangeUnion (r1, r2)) t =
    RangeUnion (wordinterval_setminus A_ r1 t, wordinterval_setminus A_ r2 t)
  | wordinterval_setminus A_ (WordInterval (v, va)) (RangeUnion (r1, r2)) =
    wordinterval_setminus A_
      (wordinterval_setminus A_ (WordInterval (v, va)) r1) r2;

fun wordinterval_UNIV A_ = WordInterval (zero_worda (len0_len A_), max_word A_);

fun wordinterval_invert A_ r =
  wordinterval_setminus A_ (wordinterval_UNIV A_) r;

fun empty_WordInterval A_ =
  WordInterval (one_worda (len0_len A_), zero_worda (len0_len A_));

fun l2br A_ [] = empty_WordInterval A_
  | l2br A_ [(s, e)] = WordInterval (s, e)
  | l2br A_ ((s, e) :: v :: va) =
    RangeUnion (WordInterval (s, e), l2br A_ (v :: va));

fun br2l A_ (RangeUnion (r1, r2)) = br2l A_ r1 @ br2l A_ r2
  | br2l A_ (WordInterval (s, e)) =
    (if less_word (len0_len A_) e s then [] else [(s, e)]);

fun ports_invert ps =
  br2l (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
    (wordinterval_invert (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
      (l2br (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))) ps));

fun atLeast (A1_, A2_) l = collect A1_ (less_eq A2_ l);

fun atMost (A1_, A2_) u = collect A1_ (fn x => less_eq A2_ x u);

fun inf_set A_ a (Coset xs) = fold (remove A_) xs a
  | inf_set A_ a (Set xs) = Set (filter (fn x => member A_ x a) xs);

fun atLeastAtMost (A1_, A2_, A3_) l u =
  inf_set A2_ (atLeast (A1_, A3_) l) (atMost (A1_, A3_) u);

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

val bot_set : 'a set = Set [];

fun ports_to_set [] = bot_set
  | ports_to_set ((s, e) :: ps) =
    sup_set
      (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
      (atLeastAtMost
        (enum_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))),
          equal_word
            (len0_len (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))),
          ord_word
            (len0_len (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
        s e)
      (ports_to_set ps);

fun char_of_nat x = ((Char.chr o IntInf.toInt) o integer_of_nat) x;

fun size_list x = gen_length zero_nat x;

fun internal_iface_name_wildcard_longest i1 i2 =
  (if equal_lista equal_char
        (take (min ord_nat (minus_nat (size_list i1) one_nata)
                (minus_nat (size_list i2) one_nata))
          i1)
        (take (min ord_nat (minus_nat (size_list i1) one_nata)
                (minus_nat (size_list i2) one_nata))
          i2)
    then SOME (if less_eq_nat (size_list i1) (size_list i2) then i2 else i1)
    else NONE);

fun iface_name_is_wildcard [] = false
  | iface_name_is_wildcard [s] = ((s : char) = #"+")
  | iface_name_is_wildcard (uu :: v :: va) = iface_name_is_wildcard (v :: va);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun iface_conjunct (Iface i1) (Iface i2) =
  (case (iface_name_is_wildcard i1, iface_name_is_wildcard i2)
    of (true, true) =>
      map_option Iface (internal_iface_name_wildcard_longest i1 i2)
    | (true, false) =>
      (if match_iface (Iface i1) i2 then SOME (Iface i2) else NONE)
    | (false, true) =>
      (if match_iface (Iface i2) i1 then SOME (Iface i1) else NONE)
    | (false, false) =>
      (if equal_lista equal_char i1 i2 then SOME (Iface i1) else NONE));

fun match_proto ProtoAny uu = true
  | match_proto (Proto p) p_p = equal_primitive_protocol p_p p;

fun iface_sel (Iface x) = x;

val ipv4range_UNIV : num1 bit0 bit0 bit0 bit0 bit0 wordinterval =
  wordinterval_UNIV
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))));

fun bool_to_ternary true = TernaryTrue
  | bool_to_ternary false = TernaryFalse;

fun eval_ternary_Or TernaryTrue TernaryTrue = TernaryTrue
  | eval_ternary_Or TernaryTrue TernaryFalse = TernaryTrue
  | eval_ternary_Or TernaryFalse TernaryTrue = TernaryTrue
  | eval_ternary_Or TernaryFalse TernaryFalse = TernaryFalse
  | eval_ternary_Or TernaryTrue TernaryUnknown = TernaryTrue
  | eval_ternary_Or TernaryFalse TernaryUnknown = TernaryUnknown
  | eval_ternary_Or TernaryUnknown TernaryTrue = TernaryTrue
  | eval_ternary_Or TernaryUnknown TernaryFalse = TernaryUnknown
  | eval_ternary_Or TernaryUnknown TernaryUnknown = TernaryUnknown;

fun ipv4addr_of_nat n =
  of_nat
    (semiring_1_word
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    n;

fun wordinterval_empty A_ (WordInterval (s, e)) = less_word (len0_len A_) e s
  | wordinterval_empty A_ (RangeUnion (r1, r2)) =
    wordinterval_empty A_ r1 andalso wordinterval_empty A_ r2;

fun ipv4range_empty rg =
  wordinterval_empty
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) rg;

fun ipv4range_range (ip_start, ip_end) = WordInterval (ip_start, ip_end);

fun nat_of_ipv4addr a =
  unat (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) a;

fun ternary_to_bool_unknown_match_tac uu uv uw TernaryTrue = true
  | ternary_to_bool_unknown_match_tac ux uy uz TernaryFalse = false
  | ternary_to_bool_unknown_match_tac alpha a p TernaryUnknown = alpha a p;

fun map_match_tac beta p (MatchAnd (m1, m2)) =
  TernaryAnd (map_match_tac beta p m1, map_match_tac beta p m2)
  | map_match_tac beta p (MatchNot m) = TernaryNot (map_match_tac beta p m)
  | map_match_tac beta p (Match m) = TernaryValue (beta m p)
  | map_match_tac uu uv MatchAny = TernaryValue TernaryTrue;

fun eval_ternary_Not TernaryTrue = TernaryFalse
  | eval_ternary_Not TernaryFalse = TernaryTrue
  | eval_ternary_Not TernaryUnknown = TernaryUnknown;

fun eval_ternary_And TernaryTrue TernaryTrue = TernaryTrue
  | eval_ternary_And TernaryTrue TernaryFalse = TernaryFalse
  | eval_ternary_And TernaryFalse TernaryTrue = TernaryFalse
  | eval_ternary_And TernaryFalse TernaryFalse = TernaryFalse
  | eval_ternary_And TernaryFalse TernaryUnknown = TernaryFalse
  | eval_ternary_And TernaryTrue TernaryUnknown = TernaryUnknown
  | eval_ternary_And TernaryUnknown TernaryFalse = TernaryFalse
  | eval_ternary_And TernaryUnknown TernaryTrue = TernaryUnknown
  | eval_ternary_And TernaryUnknown TernaryUnknown = TernaryUnknown;

fun ternary_ternary_eval (TernaryAnd (t1, t2)) =
  eval_ternary_And (ternary_ternary_eval t1) (ternary_ternary_eval t2)
  | ternary_ternary_eval (TernaryOr (t1, t2)) =
    eval_ternary_Or (ternary_ternary_eval t1) (ternary_ternary_eval t2)
  | ternary_ternary_eval (TernaryNot t) =
    eval_ternary_Not (ternary_ternary_eval t)
  | ternary_ternary_eval (TernaryValue t) = t;

fun matches gamma m a p =
  ternary_to_bool_unknown_match_tac (snd gamma) a p
    (ternary_ternary_eval (map_match_tac (fst gamma) p m));

fun negPos_map uu [] = []
  | negPos_map f (Pos a :: asa) = Pos (f a) :: negPos_map f asa
  | negPos_map f (Neg a :: asa) = Neg (f a) :: negPos_map f asa;

fun ipv4range_lowest_element (WordInterval (s, e)) =
  (if less_eq_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) s
        e
    then SOME s else NONE)
  | ipv4range_lowest_element (RangeUnion (a, b)) =
    (case (ipv4range_lowest_element a, ipv4range_lowest_element b)
      of (NONE, NONE) => NONE | (NONE, SOME aa) => SOME aa
      | (SOME aa, NONE) => SOME aa
      | (SOME aa, SOME ba) =>
        SOME (if less_word
                   (len0_bit0
                     (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                   aa ba
               then aa else ba));

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun bin_last w =
  equal_int (mod_int w (Int_of_integer (2 : IntInf.int)))
    (Int_of_integer (1 : IntInf.int));

fun bitAND_int x y =
  (if equal_int x zero_int then zero_int
    else (if equal_int x (uminus_int (Int_of_integer (1 : IntInf.int))) then y
           else bit (bitAND_int (bin_rest x) (bin_rest y))
                  (bin_last x andalso bin_last y)));

fun bitAND_word A_ a b = word_of_int A_ (bitAND_int (uint A_ a) (uint A_ b));

fun pfxm_prefix p = fst p;

fun pfxm_length p = snd p;

fun pfxm_mask B_ x =
  mask B_ (minus_nat (nat_of_integer (32 : IntInf.int)) (pfxm_length x));

fun valid_prefix A_ pf =
  equal_worda (len0_len A_)
    (bitAND_word (len0_len A_) (pfxm_mask A_ pf) (pfxm_prefix pf))
    (zero_worda (len0_len A_));

fun ipv4range_setminus r1 r2 =
  wordinterval_setminus
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun wordinterval_subset A_ r1 r2 =
  wordinterval_empty A_ (wordinterval_setminus A_ r1 r2);

fun ipv4range_subset r1 r2 =
  wordinterval_subset
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun bitNOT_int x =
  (fn xa => minus_int (uminus_int xa) (Int_of_integer (1 : IntInf.int))) x;

fun bitOR_int x =
  (fn xa => fn y => bitNOT_int (bitAND_int (bitNOT_int xa) (bitNOT_int y))) x;

fun bitOR_word A_ a b = word_of_int A_ (bitOR_int (uint A_ a) (uint A_ b));

fun prefix_to_range pfx =
  WordInterval
    (pfxm_prefix pfx,
      bitOR_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (pfxm_prefix pfx)
        (pfxm_mask
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) pfx));

fun ipv4range_split1 r =
  let
    val a = ipv4range_lowest_element r;
  in
    (case a of NONE => (NONE, r)
      | SOME aa =>
        let
          val cs = map (fn b => (aa, b)) pfxes;
          val cfs =
            filter
              (fn s =>
                valid_prefix
                  (len_bit0
                    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  s andalso
                  ipv4range_subset (prefix_to_range s) r)
              cs;
          val mc = find (const true) cfs;
        in
          (case mc of NONE => (NONE, r)
            | SOME m => (mc, ipv4range_setminus r (prefix_to_range m)))
        end)
  end;

fun ipv4range_split rs =
  (if not (ipv4range_empty rs)
    then (case ipv4range_split1 rs of (NONE, _) => []
           | (SOME s, u) => s :: ipv4range_split u)
    else []);

fun matcheq_matachAny MatchAny = true
  | matcheq_matachAny (MatchNot m) = not (matcheq_matachAny m)
  | matcheq_matachAny (MatchAnd (m1, m2)) =
    matcheq_matachAny m1 andalso matcheq_matachAny m2
  | matcheq_matachAny (Match uu) = (raise Fail "undefined");

fun iiface_sel (IIface x3) = x3;

fun is_Iiface (Src x1) = false
  | is_Iiface (Dst x2) = false
  | is_Iiface (IIface x3) = true
  | is_Iiface (OIface x4) = false
  | is_Iiface (Prot x5) = false
  | is_Iiface (Src_Ports x6) = false
  | is_Iiface (Dst_Ports x7) = false
  | is_Iiface (Extra x8) = false;

fun src_sel (Src x1) = x1;

fun is_Src (Src x1) = true
  | is_Src (Dst x2) = false
  | is_Src (IIface x3) = false
  | is_Src (OIface x4) = false
  | is_Src (Prot x5) = false
  | is_Src (Src_Ports x6) = false
  | is_Src (Dst_Ports x7) = false
  | is_Src (Extra x8) = false;

fun wordinterval_union A_ r1 r2 = RangeUnion (r1, r2);

fun l2br_negation_type_union A_ [] = empty_WordInterval A_
  | l2br_negation_type_union A_ (Pos (s, e) :: ls) =
    wordinterval_union A_ (WordInterval (s, e)) (l2br_negation_type_union A_ ls)
  | l2br_negation_type_union A_ (Neg (s, e) :: ls) =
    wordinterval_union A_ (wordinterval_invert A_ (WordInterval (s, e)))
      (l2br_negation_type_union A_ ls);

fun primitive_extractor uu MatchAny = ([], MatchAny)
  | primitive_extractor (disc, sel) (Match a) =
    (if disc a then ([Pos (sel a)], MatchAny) else ([], Match a))
  | primitive_extractor (disc, sel) (MatchNot (Match a)) =
    (if disc a then ([Neg (sel a)], MatchAny) else ([], MatchNot (Match a)))
  | primitive_extractor c (MatchAnd (ms1, ms2)) =
    let
      val (a1, ms1a) = primitive_extractor c ms1;
      val (a2, ms2a) = primitive_extractor c ms2;
    in
      (a1 @ a2, MatchAnd (ms1a, ms2a))
    end
  | primitive_extractor uv (MatchNot (MatchNot va)) = (raise Fail "undefined")
  | primitive_extractor uv (MatchNot (MatchAnd (va, vb))) =
    (raise Fail "undefined")
  | primitive_extractor uv (MatchNot MatchAny) = (raise Fail "undefined");

fun bitNOT_word A_ a = word_of_int A_ (bitNOT_int (uint A_ a));

fun ipv4cidr_to_interval (pre, len) =
  let
    val netmask =
      shiftl_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (mask (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          len)
        (minus_nat (nat_of_integer (32 : IntInf.int)) len);
    val network_prefix =
      bitAND_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        pre netmask;
  in
    (network_prefix,
      bitOR_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        network_prefix
        (bitNOT_word
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          netmask))
  end;

fun ipv4addr_of_dotdecimal (a, (b, (c, d))) =
  ipv4addr_of_nat
    (plus_nat
      (plus_nat (plus_nat d (times_nata (nat_of_integer (256 : IntInf.int)) c))
        (times_nata (nat_of_integer (65536 : IntInf.int)) b))
      (times_nata (nat_of_integer (16777216 : IntInf.int)) a));

fun ipt_ipv4range_to_interval (Ip4Addr addr) =
  (ipv4addr_of_dotdecimal addr, ipv4addr_of_dotdecimal addr)
  | ipt_ipv4range_to_interval (Ip4AddrNetmask (pre, len)) =
    ipv4cidr_to_interval (ipv4addr_of_dotdecimal pre, len);

fun get_exists_matching_src_ips_executable iface m =
  let
    val (i_matches, _) = primitive_extractor (is_Iiface, iiface_sel) m;
  in
    (if pred_list
          (fn a =>
            (case a of Pos i => match_iface i (iface_sel iface)
              | Neg i => not (match_iface i (iface_sel iface))))
          i_matches
      then let
             val (ip_matches, _) = primitive_extractor (is_Src, src_sel) m;
           in
             (if null ip_matches then ipv4range_UNIV
               else l2br_negation_type_union
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                      (negPos_map ipt_ipv4range_to_interval ip_matches))
           end
      else empty_WordInterval
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
  end;

fun is_Src_Ports (Src x1) = false
  | is_Src_Ports (Dst x2) = false
  | is_Src_Ports (IIface x3) = false
  | is_Src_Ports (OIface x4) = false
  | is_Src_Ports (Prot x5) = false
  | is_Src_Ports (Src_Ports x6) = true
  | is_Src_Ports (Dst_Ports x7) = false
  | is_Src_Ports (Extra x8) = false;

fun is_Dst_Ports (Src x1) = false
  | is_Dst_Ports (Dst x2) = false
  | is_Dst_Ports (IIface x3) = false
  | is_Dst_Ports (OIface x4) = false
  | is_Dst_Ports (Prot x5) = false
  | is_Dst_Ports (Src_Ports x6) = false
  | is_Dst_Ports (Dst_Ports x7) = true
  | is_Dst_Ports (Extra x8) = false;

fun is_Oiface (Src x1) = false
  | is_Oiface (Dst x2) = false
  | is_Oiface (IIface x3) = false
  | is_Oiface (OIface x4) = true
  | is_Oiface (Prot x5) = false
  | is_Oiface (Src_Ports x6) = false
  | is_Oiface (Dst_Ports x7) = false
  | is_Oiface (Extra x8) = false;

fun is_Extra (Src x1) = false
  | is_Extra (Dst x2) = false
  | is_Extra (IIface x3) = false
  | is_Extra (OIface x4) = false
  | is_Extra (Prot x5) = false
  | is_Extra (Src_Ports x6) = false
  | is_Extra (Dst_Ports x7) = false
  | is_Extra (Extra x8) = true;

fun is_Prot (Src x1) = false
  | is_Prot (Dst x2) = false
  | is_Prot (IIface x3) = false
  | is_Prot (OIface x4) = false
  | is_Prot (Prot x5) = true
  | is_Prot (Src_Ports x6) = false
  | is_Prot (Dst_Ports x7) = false
  | is_Prot (Extra x8) = false;

fun wordinterval_to_list A_ (RangeUnion (r1, r2)) =
  wordinterval_to_list A_ r1 @ wordinterval_to_list A_ r2
  | wordinterval_to_list A_ (WordInterval (v, va)) =
    (if wordinterval_empty A_ (WordInterval (v, va)) then []
      else [WordInterval (v, va)]);

fun list_to_wordinterval A_ [r] = r
  | list_to_wordinterval A_ (r :: v :: va) =
    RangeUnion (r, list_to_wordinterval A_ (v :: va))
  | list_to_wordinterval A_ [] = empty_WordInterval A_;

fun wordinterval_optimize_same A_ rs =
  list_to_wordinterval A_
    (remdups (equal_wordinterval A_) (wordinterval_to_list A_ rs));

fun wordinterval_intersection A_ r1 r2 =
  wordinterval_optimize_same A_
    (wordinterval_setminus A_ (wordinterval_union A_ r1 r2)
      (wordinterval_union A_ (wordinterval_invert A_ r1)
        (wordinterval_invert A_ r2)));

fun l2br_negation_type_intersect A_ [] = wordinterval_UNIV A_
  | l2br_negation_type_intersect A_ (Pos (s, e) :: ls) =
    wordinterval_intersection A_ (WordInterval (s, e))
      (l2br_negation_type_intersect A_ ls)
  | l2br_negation_type_intersect A_ (Neg (s, e) :: ls) =
    wordinterval_intersection A_ (wordinterval_invert A_ (WordInterval (s, e)))
      (l2br_negation_type_intersect A_ ls);

fun is_Dst (Src x1) = false
  | is_Dst (Dst x2) = true
  | is_Dst (IIface x3) = false
  | is_Dst (OIface x4) = false
  | is_Dst (Prot x5) = false
  | is_Dst (Src_Ports x6) = false
  | is_Dst (Dst_Ports x7) = false
  | is_Dst (Extra x8) = false;

fun has_disc uu MatchAny = false
  | has_disc disc (Match a) = disc a
  | has_disc disc (MatchNot m) = has_disc disc m
  | has_disc disc (MatchAnd (m1, m2)) =
    has_disc disc m1 orelse has_disc disc m2;

fun get_all_matching_src_ips_executable iface m =
  let
    val (i_matches, rest1) = primitive_extractor (is_Iiface, iiface_sel) m;
  in
    (if pred_list
          (fn a =>
            (case a of Pos i => match_iface i (iface_sel iface)
              | Neg i => not (match_iface i (iface_sel iface))))
          i_matches
      then let
             val (ip_matches, rest2) =
               primitive_extractor (is_Src, src_sel) rest1;
           in
             (if not (has_disc is_Dst rest2) andalso
                   (not (has_disc is_Oiface rest2) andalso
                     (not (has_disc is_Prot rest2) andalso
                       (not (has_disc is_Src_Ports rest2) andalso
                         (not (has_disc is_Dst_Ports rest2) andalso
                           (not (has_disc is_Extra rest2) andalso
                             matcheq_matachAny rest2)))))
               then (if null ip_matches then ipv4range_UNIV
                      else l2br_negation_type_intersect
                             (len_bit0
                               (len_bit0
                                 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                             (negPos_map ipt_ipv4range_to_interval ip_matches))
               else empty_WordInterval
                      (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
           end
      else empty_WordInterval
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
  end;

fun no_spoofing_algorithm_executable iface ipassmt [] allowed denied1 =
  wordinterval_subset
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
    (wordinterval_setminus
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) allowed
      denied1)
    (l2br (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
      (map ipv4cidr_to_interval (the (ipassmt iface))))
  | no_spoofing_algorithm_executable iface ipassmt (Rule (m, Accept) :: rs)
    allowed denied1 =
    no_spoofing_algorithm_executable iface ipassmt rs
      (wordinterval_union
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) allowed
        (get_exists_matching_src_ips_executable iface m))
      denied1
  | no_spoofing_algorithm_executable iface ipassmt (Rule (m, Drop) :: rs)
    allowed denied1 =
    no_spoofing_algorithm_executable iface ipassmt rs allowed
      (wordinterval_union
        (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) denied1
        (wordinterval_setminus
          (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
          (get_all_matching_src_ips_executable iface m) allowed))
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Log) :: va) ux uy =
    (raise Fail "undefined")
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Reject) :: va) ux uy =
    (raise Fail "undefined")
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Call vd) :: va) ux uy =
    (raise Fail "undefined")
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Return) :: va) ux uy =
    (raise Fail "undefined")
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Empty) :: va) ux uy =
    (raise Fail "undefined")
  | no_spoofing_algorithm_executable uu uv (Rule (vb, Unknown) :: va) ux uy =
    (raise Fail "undefined");

fun no_spoofing_iface iface ipassmt rs =
  no_spoofing_algorithm_executable iface ipassmt rs
    (empty_WordInterval
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))
    (empty_WordInterval
      (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))));

fun rw_Reject [] = []
  | rw_Reject (Rule (m, Reject) :: rs) = Rule (m, Drop) :: rw_Reject rs
  | rw_Reject (Rule (v, Accept) :: rs) = Rule (v, Accept) :: rw_Reject rs
  | rw_Reject (Rule (v, Drop) :: rs) = Rule (v, Drop) :: rw_Reject rs
  | rw_Reject (Rule (v, Log) :: rs) = Rule (v, Log) :: rw_Reject rs
  | rw_Reject (Rule (v, Call vb) :: rs) = Rule (v, Call vb) :: rw_Reject rs
  | rw_Reject (Rule (v, Return) :: rs) = Rule (v, Return) :: rw_Reject rs
  | rw_Reject (Rule (v, Empty) :: rs) = Rule (v, Empty) :: rw_Reject rs
  | rw_Reject (Rule (v, Unknown) :: rs) = Rule (v, Unknown) :: rw_Reject rs;

fun equal_match_expr A_ (MatchAnd (x31, x32)) MatchAny = false
  | equal_match_expr A_ MatchAny (MatchAnd (x31, x32)) = false
  | equal_match_expr A_ (MatchNot x2) MatchAny = false
  | equal_match_expr A_ MatchAny (MatchNot x2) = false
  | equal_match_expr A_ (MatchNot x2) (MatchAnd (x31, x32)) = false
  | equal_match_expr A_ (MatchAnd (x31, x32)) (MatchNot x2) = false
  | equal_match_expr A_ (Match x1) MatchAny = false
  | equal_match_expr A_ MatchAny (Match x1) = false
  | equal_match_expr A_ (Match x1) (MatchAnd (x31, x32)) = false
  | equal_match_expr A_ (MatchAnd (x31, x32)) (Match x1) = false
  | equal_match_expr A_ (Match x1) (MatchNot x2) = false
  | equal_match_expr A_ (MatchNot x2) (Match x1) = false
  | equal_match_expr A_ (MatchAnd (x31, x32)) (MatchAnd (y31, y32)) =
    equal_match_expr A_ x31 y31 andalso equal_match_expr A_ x32 y32
  | equal_match_expr A_ (MatchNot x2) (MatchNot y2) = equal_match_expr A_ x2 y2
  | equal_match_expr A_ (Match x1) (Match y1) = eq A_ x1 y1
  | equal_match_expr A_ MatchAny MatchAny = true;

fun lower_closure_matchexpr uu MatchAny = MatchAny
  | lower_closure_matchexpr Accept (Match (Extra uv)) = MatchNot MatchAny
  | lower_closure_matchexpr Reject (Match (Extra uw)) = MatchAny
  | lower_closure_matchexpr Drop (Match (Extra ux)) = MatchAny
  | lower_closure_matchexpr Drop (Match (Src v)) = Match (Src v)
  | lower_closure_matchexpr Drop (Match (Dst v)) = Match (Dst v)
  | lower_closure_matchexpr Drop (Match (IIface v)) = Match (IIface v)
  | lower_closure_matchexpr Drop (Match (OIface v)) = Match (OIface v)
  | lower_closure_matchexpr Drop (Match (Prot v)) = Match (Prot v)
  | lower_closure_matchexpr Drop (Match (Src_Ports v)) = Match (Src_Ports v)
  | lower_closure_matchexpr Drop (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | lower_closure_matchexpr Log (Match m) = Match m
  | lower_closure_matchexpr Reject (Match (Src v)) = Match (Src v)
  | lower_closure_matchexpr Reject (Match (Dst v)) = Match (Dst v)
  | lower_closure_matchexpr Reject (Match (IIface v)) = Match (IIface v)
  | lower_closure_matchexpr Reject (Match (OIface v)) = Match (OIface v)
  | lower_closure_matchexpr Reject (Match (Prot v)) = Match (Prot v)
  | lower_closure_matchexpr Reject (Match (Src_Ports v)) = Match (Src_Ports v)
  | lower_closure_matchexpr Reject (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | lower_closure_matchexpr (Call v) (Match m) = Match m
  | lower_closure_matchexpr Return (Match m) = Match m
  | lower_closure_matchexpr Empty (Match m) = Match m
  | lower_closure_matchexpr Unknown (Match m) = Match m
  | lower_closure_matchexpr uy (Match (Src v)) = Match (Src v)
  | lower_closure_matchexpr uy (Match (Dst v)) = Match (Dst v)
  | lower_closure_matchexpr uy (Match (IIface v)) = Match (IIface v)
  | lower_closure_matchexpr uy (Match (OIface v)) = Match (OIface v)
  | lower_closure_matchexpr uy (Match (Prot v)) = Match (Prot v)
  | lower_closure_matchexpr uy (Match (Src_Ports v)) = Match (Src_Ports v)
  | lower_closure_matchexpr uy (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | lower_closure_matchexpr Accept (MatchNot (Match (Extra uz))) =
    MatchNot MatchAny
  | lower_closure_matchexpr Drop (MatchNot (Match (Extra va))) = MatchAny
  | lower_closure_matchexpr Reject (MatchNot (Match (Extra vb))) = MatchAny
  | lower_closure_matchexpr a (MatchNot (MatchNot m)) =
    lower_closure_matchexpr a m
  | lower_closure_matchexpr a (MatchNot (MatchAnd (m1, m2))) =
    let
      val m1a = lower_closure_matchexpr a (MatchNot m1);
      val m2a = lower_closure_matchexpr a (MatchNot m2);
    in
      (if equal_match_expr equal_common_primitive m1a MatchAny orelse
            equal_match_expr equal_common_primitive m2a MatchAny
        then MatchAny
        else (if equal_match_expr equal_common_primitive m1a (MatchNot MatchAny)
               then m2a
               else (if equal_match_expr equal_common_primitive m2a
                          (MatchNot MatchAny)
                      then m1a
                      else MatchNot (MatchAnd (MatchNot m1a, MatchNot m2a)))))
    end
  | lower_closure_matchexpr Drop (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | lower_closure_matchexpr Drop (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | lower_closure_matchexpr Drop (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | lower_closure_matchexpr Drop (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | lower_closure_matchexpr Drop (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | lower_closure_matchexpr Drop (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | lower_closure_matchexpr Drop (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | lower_closure_matchexpr Drop (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr Log (MatchNot (Match v)) = MatchNot (Match v)
  | lower_closure_matchexpr Log (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr Reject (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | lower_closure_matchexpr Reject (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | lower_closure_matchexpr Reject (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | lower_closure_matchexpr Reject (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | lower_closure_matchexpr Reject (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | lower_closure_matchexpr Reject (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | lower_closure_matchexpr Reject (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | lower_closure_matchexpr Reject (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr (Call v) (MatchNot (Match va)) = MatchNot (Match va)
  | lower_closure_matchexpr (Call v) (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr Return (MatchNot (Match v)) = MatchNot (Match v)
  | lower_closure_matchexpr Return (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr Empty (MatchNot (Match v)) = MatchNot (Match v)
  | lower_closure_matchexpr Empty (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr Unknown (MatchNot (Match v)) = MatchNot (Match v)
  | lower_closure_matchexpr Unknown (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr vc (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | lower_closure_matchexpr vc (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | lower_closure_matchexpr vc (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | lower_closure_matchexpr vc (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | lower_closure_matchexpr vc (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | lower_closure_matchexpr vc (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | lower_closure_matchexpr vc (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | lower_closure_matchexpr vc (MatchNot MatchAny) = MatchNot MatchAny
  | lower_closure_matchexpr a (MatchAnd (m1, m2)) =
    MatchAnd (lower_closure_matchexpr a m1, lower_closure_matchexpr a m2);

fun normalize_primitive_extract disc_sel c f m =
  let
    val (spts, rst) = primitive_extractor disc_sel m;
  in
    map (fn spt => MatchAnd (Match (c spt), rst)) (f spts)
  end;

fun ipt_ipv4range_negation_type_to_br_intersect l =
  l2br_negation_type_intersect
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
    (negPos_map ipt_ipv4range_to_interval l);

fun shiftr_word A_ w n = funpow n (shiftr1 A_) w;

fun dotdecimal_of_ipv4addr a =
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

fun br_2_cidr_ipt_ipv4range_list r =
  map (fn (base, a) => Ip4AddrNetmask (dotdecimal_of_ipv4addr base, a))
    (ipv4range_split r);

fun ipt_ipv4range_compress x =
  (br_2_cidr_ipt_ipv4range_list o ipt_ipv4range_negation_type_to_br_intersect)
    x;

fun normalize_src_ips x =
  normalize_primitive_extract (is_Src, src_sel) Src ipt_ipv4range_compress x;

fun dst_sel (Dst x2) = x2;

fun normalize_dst_ips x =
  normalize_primitive_extract (is_Dst, dst_sel) Dst ipt_ipv4range_compress x;

fun src_ports_sel (Src_Ports x6) = x6;

fun ipt_ports_negation_type_normalize (Pos ps) = ps
  | ipt_ports_negation_type_normalize (Neg ps) = ports_invert ps;

fun ipt_ports_andlist_compress A_ pss =
  br2l A_
    (fold (fn ps => wordinterval_intersection A_ (l2br A_ ps)) pss
      (wordinterval_UNIV A_));

fun ipt_ports_compress pss =
  ipt_ports_andlist_compress
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))
    (map ipt_ports_negation_type_normalize pss);

fun normalize_ports_step disc_sel c =
  normalize_primitive_extract disc_sel c
    (fn me => map (fn pt => [pt]) (ipt_ports_compress me));

fun normalize_src_ports x =
  normalize_ports_step (is_Src_Ports, src_ports_sel) Src_Ports x;

fun dst_ports_sel (Dst_Ports x7) = x7;

fun normalize_dst_ports x =
  normalize_ports_step (is_Dst_Ports, dst_ports_sel) Dst_Ports x;

fun normalize_rules uu [] = []
  | normalize_rules f (Rule (m, a) :: rs) =
    map (fn ma => Rule (ma, a)) (f m) @ normalize_rules f rs;

fun transform_normalize_primitives x =
  (normalize_rules normalize_dst_ips o normalize_rules normalize_src_ips o
     normalize_rules normalize_dst_ports o
    normalize_rules normalize_src_ports)
    x;

fun optimize_primitive_univ (Match (IIface iface)) =
  (if equal_ifacea iface ifaceAny then MatchAny else Match (IIface iface))
  | optimize_primitive_univ (Match (OIface iface)) =
    (if equal_ifacea iface ifaceAny then MatchAny else Match (OIface iface))
  | optimize_primitive_univ (Match (Src_Ports [(s, e)])) =
    (if equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))) s
          (zero_worda
            (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) andalso
          equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
            e (word_of_int
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
                (Int_of_integer (65535 : IntInf.int)))
      then MatchAny else Match (Src_Ports [(s, e)]))
  | optimize_primitive_univ (Match (Dst_Ports [(s, e)])) =
    (if equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))) s
          (zero_worda
            (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) andalso
          equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
            e (word_of_int
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
                (Int_of_integer (65535 : IntInf.int)))
      then MatchAny else Match (Dst_Ports [(s, e)]))
  | optimize_primitive_univ (Match (Prot ProtoAny)) = MatchAny
  | optimize_primitive_univ (Match (Src (Ip4Addr va))) =
    Match (Src (Ip4Addr va))
  | optimize_primitive_univ (Match (Dst (Ip4Addr va))) =
    Match (Dst (Ip4Addr va))
  | optimize_primitive_univ (Match (Prot (Proto va))) = Match (Prot (Proto va))
  | optimize_primitive_univ (Match (Src_Ports [])) = Match (Src_Ports [])
  | optimize_primitive_univ (Match (Src_Ports (va :: vc :: vd))) =
    Match (Src_Ports (va :: vc :: vd))
  | optimize_primitive_univ (Match (Dst_Ports [])) = Match (Dst_Ports [])
  | optimize_primitive_univ (Match (Dst_Ports (va :: vc :: vd))) =
    Match (Dst_Ports (va :: vc :: vd))
  | optimize_primitive_univ (Match (Extra v)) = Match (Extra v)
  | optimize_primitive_univ (MatchNot m) = MatchNot (optimize_primitive_univ m)
  | optimize_primitive_univ (MatchAnd (m1, m2)) =
    MatchAnd (optimize_primitive_univ m1, optimize_primitive_univ m2)
  | optimize_primitive_univ MatchAny = MatchAny
  | optimize_primitive_univ
    (Match (Src (Ip4AddrNetmask ((ve, (vg, (vi, via))), vc)))) =
    (if equal_nata vc zero_nat
      then (if equal_nata via zero_nat
             then (if equal_nata vi zero_nat
                    then (if equal_nata vg zero_nat
                           then (if equal_nata ve zero_nat then MatchAny
                                  else Match
 (Src (Ip4AddrNetmask
        ((suc (minus_nat ve one_nata), (zero_nat, (zero_nat, zero_nat))),
          zero_nat))))
                           else Match (Src
(Ip4AddrNetmask
  ((ve, (suc (minus_nat vg one_nata), (zero_nat, zero_nat))), zero_nat))))
                    else Match (Src (Ip4AddrNetmask
                                      ((ve,
 (vg, (suc (minus_nat vi one_nata), zero_nat))),
zero_nat))))
             else Match (Src (Ip4AddrNetmask
                               ((ve, (vg, (vi, suc (minus_nat via one_nata)))),
                                 zero_nat))))
      else Match (Src (Ip4AddrNetmask
                        ((ve, (vg, (vi, via))), suc (minus_nat vc one_nata)))))
  | optimize_primitive_univ
    (Match (Dst (Ip4AddrNetmask ((ve, (vg, (vi, via))), vc)))) =
    (if equal_nata vc zero_nat
      then (if equal_nata via zero_nat
             then (if equal_nata vi zero_nat
                    then (if equal_nata vg zero_nat
                           then (if equal_nata ve zero_nat then MatchAny
                                  else Match
 (Dst (Ip4AddrNetmask
        ((suc (minus_nat ve one_nata), (zero_nat, (zero_nat, zero_nat))),
          zero_nat))))
                           else Match (Dst
(Ip4AddrNetmask
  ((ve, (suc (minus_nat vg one_nata), (zero_nat, zero_nat))), zero_nat))))
                    else Match (Dst (Ip4AddrNetmask
                                      ((ve,
 (vg, (suc (minus_nat vi one_nata), zero_nat))),
zero_nat))))
             else Match (Dst (Ip4AddrNetmask
                               ((ve, (vg, (vi, suc (minus_nat via one_nata)))),
                                 zero_nat))))
      else Match (Dst (Ip4AddrNetmask
                        ((ve, (vg, (vi, via))), suc (minus_nat vc one_nata)))));

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
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, Match v)) =
    opt_MatchAny_match_expr (Match v)
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, MatchNot v)) =
    opt_MatchAny_match_expr (MatchNot v)
  | opt_MatchAny_match_expr (MatchAnd (MatchAny, MatchAnd (v, va))) =
    opt_MatchAny_match_expr (MatchAnd (v, va))
  | opt_MatchAny_match_expr (MatchAnd (Match v, MatchAny)) =
    opt_MatchAny_match_expr (Match v)
  | opt_MatchAny_match_expr (MatchAnd (MatchNot v, MatchAny)) =
    opt_MatchAny_match_expr (MatchNot v)
  | opt_MatchAny_match_expr (MatchAnd (MatchAnd (v, va), MatchAny)) =
    opt_MatchAny_match_expr (MatchAnd (v, va))
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

fun get_action (Rule (x1, x2)) = x2;

fun get_match (Rule (x1, x2)) = x1;

fun optimize_matches f rs =
  map (fn r => Rule (f (get_match r), get_action r)) rs;

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

fun normalize_rules_dnf [] = []
  | normalize_rules_dnf (Rule (m, a) :: rs) =
    map (fn ma => Rule (ma, a)) (normalize_match m) @ normalize_rules_dnf rs;

fun transform_optimize_dnf_strict x =
  (optimize_matches opt_MatchAny_match_expr o normalize_rules_dnf o
    optimize_matches (opt_MatchAny_match_expr o optimize_primitive_univ))
    x;

fun optimize_matches_a f rs =
  map (fn r => Rule (f (get_action r) (get_match r), get_action r)) rs;

fun lower_closure rs =
  transform_optimize_dnf_strict
    (transform_normalize_primitives
      (transform_optimize_dnf_strict
        (optimize_matches_a lower_closure_matchexpr rs)));

fun map_of_string rs = map_of (equal_list equal_char) rs;

fun string_of_nat n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then [char_of_nat (plus_nat (nat_of_integer (48 : IntInf.int)) n)]
    else string_of_nat (div_nat n (nat_of_integer (10 : IntInf.int))) @
           [char_of_nat
              (plus_nat (nat_of_integer (48 : IntInf.int))
                (mod_nat n (nat_of_integer (10 : IntInf.int))))]);

fun port_toString p =
  string_of_nat
    (unat (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))) p);

fun upper_closure_matchexpr uu MatchAny = MatchAny
  | upper_closure_matchexpr Accept (Match (Extra uv)) = MatchAny
  | upper_closure_matchexpr Reject (Match (Extra uw)) = MatchNot MatchAny
  | upper_closure_matchexpr Drop (Match (Extra ux)) = MatchNot MatchAny
  | upper_closure_matchexpr Drop (Match (Src v)) = Match (Src v)
  | upper_closure_matchexpr Drop (Match (Dst v)) = Match (Dst v)
  | upper_closure_matchexpr Drop (Match (IIface v)) = Match (IIface v)
  | upper_closure_matchexpr Drop (Match (OIface v)) = Match (OIface v)
  | upper_closure_matchexpr Drop (Match (Prot v)) = Match (Prot v)
  | upper_closure_matchexpr Drop (Match (Src_Ports v)) = Match (Src_Ports v)
  | upper_closure_matchexpr Drop (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | upper_closure_matchexpr Log (Match m) = Match m
  | upper_closure_matchexpr Reject (Match (Src v)) = Match (Src v)
  | upper_closure_matchexpr Reject (Match (Dst v)) = Match (Dst v)
  | upper_closure_matchexpr Reject (Match (IIface v)) = Match (IIface v)
  | upper_closure_matchexpr Reject (Match (OIface v)) = Match (OIface v)
  | upper_closure_matchexpr Reject (Match (Prot v)) = Match (Prot v)
  | upper_closure_matchexpr Reject (Match (Src_Ports v)) = Match (Src_Ports v)
  | upper_closure_matchexpr Reject (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | upper_closure_matchexpr (Call v) (Match m) = Match m
  | upper_closure_matchexpr Return (Match m) = Match m
  | upper_closure_matchexpr Empty (Match m) = Match m
  | upper_closure_matchexpr Unknown (Match m) = Match m
  | upper_closure_matchexpr uy (Match (Src v)) = Match (Src v)
  | upper_closure_matchexpr uy (Match (Dst v)) = Match (Dst v)
  | upper_closure_matchexpr uy (Match (IIface v)) = Match (IIface v)
  | upper_closure_matchexpr uy (Match (OIface v)) = Match (OIface v)
  | upper_closure_matchexpr uy (Match (Prot v)) = Match (Prot v)
  | upper_closure_matchexpr uy (Match (Src_Ports v)) = Match (Src_Ports v)
  | upper_closure_matchexpr uy (Match (Dst_Ports v)) = Match (Dst_Ports v)
  | upper_closure_matchexpr Accept (MatchNot (Match (Extra uz))) = MatchAny
  | upper_closure_matchexpr Drop (MatchNot (Match (Extra va))) =
    MatchNot MatchAny
  | upper_closure_matchexpr Reject (MatchNot (Match (Extra vb))) =
    MatchNot MatchAny
  | upper_closure_matchexpr a (MatchNot (MatchNot m)) =
    upper_closure_matchexpr a m
  | upper_closure_matchexpr a (MatchNot (MatchAnd (m1, m2))) =
    let
      val m1a = upper_closure_matchexpr a (MatchNot m1);
      val m2a = upper_closure_matchexpr a (MatchNot m2);
    in
      (if equal_match_expr equal_common_primitive m1a MatchAny orelse
            equal_match_expr equal_common_primitive m2a MatchAny
        then MatchAny
        else (if equal_match_expr equal_common_primitive m1a (MatchNot MatchAny)
               then m2a
               else (if equal_match_expr equal_common_primitive m2a
                          (MatchNot MatchAny)
                      then m1a
                      else MatchNot (MatchAnd (MatchNot m1a, MatchNot m2a)))))
    end
  | upper_closure_matchexpr Drop (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | upper_closure_matchexpr Drop (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | upper_closure_matchexpr Drop (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | upper_closure_matchexpr Drop (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | upper_closure_matchexpr Drop (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | upper_closure_matchexpr Drop (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | upper_closure_matchexpr Drop (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | upper_closure_matchexpr Drop (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr Log (MatchNot (Match v)) = MatchNot (Match v)
  | upper_closure_matchexpr Log (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr Reject (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | upper_closure_matchexpr Reject (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | upper_closure_matchexpr Reject (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | upper_closure_matchexpr Reject (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | upper_closure_matchexpr Reject (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | upper_closure_matchexpr Reject (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | upper_closure_matchexpr Reject (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | upper_closure_matchexpr Reject (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr (Call v) (MatchNot (Match va)) = MatchNot (Match va)
  | upper_closure_matchexpr (Call v) (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr Return (MatchNot (Match v)) = MatchNot (Match v)
  | upper_closure_matchexpr Return (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr Empty (MatchNot (Match v)) = MatchNot (Match v)
  | upper_closure_matchexpr Empty (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr Unknown (MatchNot (Match v)) = MatchNot (Match v)
  | upper_closure_matchexpr Unknown (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr vc (MatchNot (Match (Src va))) =
    MatchNot (Match (Src va))
  | upper_closure_matchexpr vc (MatchNot (Match (Dst va))) =
    MatchNot (Match (Dst va))
  | upper_closure_matchexpr vc (MatchNot (Match (IIface va))) =
    MatchNot (Match (IIface va))
  | upper_closure_matchexpr vc (MatchNot (Match (OIface va))) =
    MatchNot (Match (OIface va))
  | upper_closure_matchexpr vc (MatchNot (Match (Prot va))) =
    MatchNot (Match (Prot va))
  | upper_closure_matchexpr vc (MatchNot (Match (Src_Ports va))) =
    MatchNot (Match (Src_Ports va))
  | upper_closure_matchexpr vc (MatchNot (Match (Dst_Ports va))) =
    MatchNot (Match (Dst_Ports va))
  | upper_closure_matchexpr vc (MatchNot MatchAny) = MatchNot MatchAny
  | upper_closure_matchexpr a (MatchAnd (m1, m2)) =
    MatchAnd (upper_closure_matchexpr a m1, upper_closure_matchexpr a m2);

fun upper_closure rs =
  transform_optimize_dnf_strict
    (transform_normalize_primitives
      (transform_optimize_dnf_strict
        (optimize_matches_a upper_closure_matchexpr rs)));

fun approximating_bigstep_fun gamma p [] s = s
  | approximating_bigstep_fun gamma p (v :: va) (Decision x) = Decision x
  | approximating_bigstep_fun gamma p (Rule (m, a) :: rs) Undecided =
    (if not (matches gamma m a p)
      then approximating_bigstep_fun gamma p rs Undecided
      else (case a of Accept => Decision FinalAllow | Drop => Decision FinalDeny
             | Log => approximating_bigstep_fun gamma p rs Undecided
             | Reject => Decision FinalDeny
             | Empty => approximating_bigstep_fun gamma p rs Undecided));

fun p_oiface
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_oiface;

fun p_iiface
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_iiface;

fun p_sport
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_sport;

fun p_proto
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_proto;

fun p_dport
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_dport;

fun p_src
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_src;

fun p_dst
  (Simple_packet_ext
    (p_iiface, p_oiface, p_src, p_dst, p_proto, p_sport, p_dport, more))
  = p_dst;

fun common_matcher (IIface i) p = bool_to_ternary (match_iface i (p_iiface p))
  | common_matcher (OIface i) p = bool_to_ternary (match_iface i (p_oiface p))
  | common_matcher (Src ip) p =
    bool_to_ternary
      (case ip
        of Ip4Addr ipa =>
          equal_worda
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (p_src p) (ipv4addr_of_dotdecimal ipa)
        | Ip4AddrNetmask (pre, len) =>
          less_eq_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (bitAND_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (ipv4addr_of_dotdecimal pre)
              (shiftl_word
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                (mask (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  len)
                (minus_nat (nat_of_integer (32 : IntInf.int)) len)))
            (p_src p) andalso
            less_eq_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (p_src p)
              (bitOR_word
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                (ipv4addr_of_dotdecimal pre)
                (mask (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (minus_nat (nat_of_integer (32 : IntInf.int)) len))))
  | common_matcher (Dst ip) p =
    bool_to_ternary
      (case ip
        of Ip4Addr ipa =>
          equal_worda
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (p_dst p) (ipv4addr_of_dotdecimal ipa)
        | Ip4AddrNetmask (pre, len) =>
          less_eq_word
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
            (bitAND_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (ipv4addr_of_dotdecimal pre)
              (shiftl_word
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                (mask (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  len)
                (minus_nat (nat_of_integer (32 : IntInf.int)) len)))
            (p_dst p) andalso
            less_eq_word
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (p_dst p)
              (bitOR_word
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                (ipv4addr_of_dotdecimal pre)
                (mask (len_bit0
                        (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
                  (minus_nat (nat_of_integer (32 : IntInf.int)) len))))
  | common_matcher (Prot proto) p =
    bool_to_ternary (match_proto proto (p_proto p))
  | common_matcher (Src_Ports ps) p =
    bool_to_ternary
      (member
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (p_sport p) (ports_to_set ps))
  | common_matcher (Dst_Ports ps) p =
    bool_to_ternary
      (member
        (equal_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (p_dport p) (ports_to_set ps))
  | common_matcher (Extra uu) p = TernaryUnknown;

fun in_doubt_allow Accept uu = true
  | in_doubt_allow Drop uv = false
  | in_doubt_allow Reject uw = false
  | in_doubt_allow Log uy = (raise Fail "undefined")
  | in_doubt_allow (Call v) uy = (raise Fail "undefined")
  | in_doubt_allow Return uy = (raise Fail "undefined")
  | in_doubt_allow Empty uy = (raise Fail "undefined")
  | in_doubt_allow Unknown uy = (raise Fail "undefined");

fun counter_example rs =
  approximating_bigstep_fun (common_matcher, in_doubt_allow)
    (Simple_packet_ext
      ([#"e", #"t", #"h", #"1", #".", #"1", #"0", #"1", #"7"],
        [#"e", #"t", #"h", #"1", #".", #"9", #"6"],
        zero_worda
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))),
        ipv4addr_of_dotdecimal
          (nat_of_integer (131 : IntInf.int),
            (nat_of_integer (159 : IntInf.int),
              (nat_of_integer (14 : IntInf.int),
                nat_of_integer (9 : IntInf.int)))),
        TCP,
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          (Int_of_integer (12345 : IntInf.int)),
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          (Int_of_integer (22 : IntInf.int)),
        ()))
    rs Undecided;

fun iface_toString descr iface =
  (if equal_ifacea iface ifaceAny then []
    else let
           val Iface a = iface;
         in
           descr @ a
         end);

fun ports_toString descr (s, e) =
  (if equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))) s
        (zero_worda
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) andalso
        equal_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))) e
          (max_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
    then []
    else descr @ [#"("] @ port_toString s @ [#","] @ port_toString e @ [#")"]);

fun rm_LogEmpty [] = []
  | rm_LogEmpty (Rule (uu, Empty) :: rs) = rm_LogEmpty rs
  | rm_LogEmpty (Rule (uv, Log) :: rs) = rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Accept) :: rs) = Rule (v, Accept) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Drop) :: rs) = Rule (v, Drop) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Reject) :: rs) = Rule (v, Reject) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Call vb) :: rs) = Rule (v, Call vb) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Return) :: rs) = Rule (v, Return) :: rm_LogEmpty rs
  | rm_LogEmpty (Rule (v, Unknown) :: rs) = Rule (v, Unknown) :: rm_LogEmpty rs;

fun simple_proto_conjunct ProtoAny proto = SOME proto
  | simple_proto_conjunct (Proto v) ProtoAny = SOME (Proto v)
  | simple_proto_conjunct (Proto p1) (Proto p2) =
    (if equal_primitive_protocol p1 p2 then SOME (Proto p1) else NONE);

fun ipv4range_intersection r1 r2 =
  wordinterval_intersection
    (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) r1 r2;

fun integer_to_16word i =
  of_nat (semiring_1_word (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1)))))
    (nat_of_integer i);

fun protocol_toString ProtoAny = [#"a", #"l", #"l"]
  | protocol_toString (Proto TCP) = [#"t", #"c", #"p"]
  | protocol_toString (Proto UDP) = [#"u", #"d", #"p"]
  | protocol_toString (Proto ICMP) = [#"i", #"c", #"m", #"p"];

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

fun ipv4_cidr_toString ip_n =
  let
    val (base, n) = ip_n;
    val (a, b) = dotdecimal_of_ipv4addr base;
    val (ba, c) = b;
    val (ca, d) = c;
  in
    string_of_nat a @
      [#"."] @
        string_of_nat ba @
          [#"."] @
            string_of_nat ca @
              [#"."] @ string_of_nat d @ [#"/"] @ string_of_nat n
  end;

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

fun simple_action_toString Accepta = [#"A", #"C", #"C", #"E", #"P", #"T"]
  | simple_action_toString Dropa = [#"D", #"R", #"O", #"P"];

fun simple_rule_toString
  (SimpleRule (Simple_match_ext (iif, oif, sip, dip, p, sps, dps, ()), a)) =
  simple_action_toString a @
    [#" ", #" ", #" ", #" ", #" "] @
      protocol_toString p @
        [#" ", #" ", #"-", #"-", #" ", #" "] @
          ipv4_cidr_toString sip @
            [#" ", #" ", #" ", #" ", #" ", #" ", #" ", #" ", #" ", #" ", #" ",
              #" "] @
              ipv4_cidr_toString dip @
                [#" "] @
                  iface_toString [#"i", #"n", #":", #" "] iif @
                    [#" "] @
                      iface_toString [#"o", #"u", #"t", #":", #" "] oif @
                        [#" "] @
                          ports_toString
                            [#"s", #"p", #"o", #"r", #"t", #"s", #":", #" "]
                            sps @
                            [#" "] @
                              ports_toString
                                [#"d", #"p", #"o", #"r", #"t", #"s", #":", #" "]
                                dps;

fun dst
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  dst;

fun src
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  src;

val simple_match_any : unit simple_match_ext =
  Simple_match_ext
    (ifaceAny, ifaceAny,
      (zero_worda
         (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))),
        zero_nat),
      (zero_worda
         (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))),
        zero_nat),
      ProtoAny,
      (zero_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))),
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          (Int_of_integer (65535 : IntInf.int))),
      (zero_worda (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))),
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
          (Int_of_integer (65535 : IntInf.int))),
      ());

fun normalized_dst_ports MatchAny = true
  | normalized_dst_ports (Match (Dst_Ports [])) = true
  | normalized_dst_ports (Match (Dst_Ports [uu])) = true
  | normalized_dst_ports (Match (Dst_Ports (v :: vb :: vc))) = false
  | normalized_dst_ports (Match (Src v)) = true
  | normalized_dst_ports (Match (Dst v)) = true
  | normalized_dst_ports (Match (IIface v)) = true
  | normalized_dst_ports (Match (OIface v)) = true
  | normalized_dst_ports (Match (Prot v)) = true
  | normalized_dst_ports (Match (Src_Ports v)) = true
  | normalized_dst_ports (Match (Extra v)) = true
  | normalized_dst_ports (MatchNot (Match (Dst_Ports ux))) = false
  | normalized_dst_ports (MatchNot (Match (Src v))) = true
  | normalized_dst_ports (MatchNot (Match (Dst v))) = true
  | normalized_dst_ports (MatchNot (Match (IIface v))) = true
  | normalized_dst_ports (MatchNot (Match (OIface v))) = true
  | normalized_dst_ports (MatchNot (Match (Prot v))) = true
  | normalized_dst_ports (MatchNot (Match (Src_Ports v))) = true
  | normalized_dst_ports (MatchNot (Match (Extra v))) = true
  | normalized_dst_ports (MatchAnd (m1, m2)) =
    normalized_dst_ports m1 andalso normalized_dst_ports m2
  | normalized_dst_ports (MatchNot (MatchAnd (uz, va))) = false
  | normalized_dst_ports (MatchNot (MatchNot vb)) = false
  | normalized_dst_ports (MatchNot MatchAny) = true;

fun normalized_src_ports MatchAny = true
  | normalized_src_ports (Match (Src_Ports [])) = true
  | normalized_src_ports (Match (Src_Ports [uu])) = true
  | normalized_src_ports (Match (Src_Ports (v :: vb :: vc))) = false
  | normalized_src_ports (Match (Src v)) = true
  | normalized_src_ports (Match (Dst v)) = true
  | normalized_src_ports (Match (IIface v)) = true
  | normalized_src_ports (Match (OIface v)) = true
  | normalized_src_ports (Match (Prot v)) = true
  | normalized_src_ports (Match (Dst_Ports v)) = true
  | normalized_src_ports (Match (Extra v)) = true
  | normalized_src_ports (MatchNot (Match (Src_Ports ux))) = false
  | normalized_src_ports (MatchNot (Match (Src v))) = true
  | normalized_src_ports (MatchNot (Match (Dst v))) = true
  | normalized_src_ports (MatchNot (Match (IIface v))) = true
  | normalized_src_ports (MatchNot (Match (OIface v))) = true
  | normalized_src_ports (MatchNot (Match (Prot v))) = true
  | normalized_src_ports (MatchNot (Match (Dst_Ports v))) = true
  | normalized_src_ports (MatchNot (Match (Extra v))) = true
  | normalized_src_ports (MatchAnd (m1, m2)) =
    normalized_src_ports m1 andalso normalized_src_ports m2
  | normalized_src_ports (MatchNot (MatchAnd (uz, va))) = false
  | normalized_src_ports (MatchNot (MatchNot vb)) = false
  | normalized_src_ports (MatchNot MatchAny) = true;

fun simpl_ports_conjunct (p1s, p1e) (p2s, p2e) =
  (max (ord_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) p1s
     p2s,
    min (ord_word (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))) p1e
      p2e);

fun ipv4_cidr_tuple_to_interval iprng =
  ipv4range_range (ipv4cidr_to_interval iprng);

fun simple_match_and
  (Simple_match_ext (iif1, oif1, sip1, dip1, p1, sps1, dps1, ()))
  (Simple_match_ext (iif2, oif2, sip2, dip2, p2, sps2, dps2, ())) =
  (case (if ipv4range_empty
              (ipv4range_intersection (ipv4_cidr_tuple_to_interval sip1)
                (ipv4_cidr_tuple_to_interval sip2))
          then NONE
          else (if ipv4range_subset (ipv4_cidr_tuple_to_interval sip1)
                     (ipv4_cidr_tuple_to_interval sip2)
                 then SOME sip1 else SOME sip2))
    of NONE => NONE
    | SOME sip =>
      (case (if ipv4range_empty
                  (ipv4range_intersection (ipv4_cidr_tuple_to_interval dip1)
                    (ipv4_cidr_tuple_to_interval dip2))
              then NONE
              else (if ipv4range_subset (ipv4_cidr_tuple_to_interval dip1)
                         (ipv4_cidr_tuple_to_interval dip2)
                     then SOME dip1 else SOME dip2))
        of NONE => NONE
        | SOME dip =>
          (case iface_conjunct iif1 iif2 of NONE => NONE
            | SOME iif =>
              (case iface_conjunct oif1 oif2 of NONE => NONE
                | SOME oif =>
                  (case simple_proto_conjunct p1 p2 of NONE => NONE
                    | SOME p =>
                      SOME (Simple_match_ext
                             (iif, oif, sip, dip, p,
                               simpl_ports_conjunct sps1 sps2,
                               simpl_ports_conjunct dps1 dps2, ())))))));

fun unfold_ruleset_FORWARD rs =
  funpow (nat_of_integer (10 : IntInf.int))
    (optimize_matches opt_MatchAny_match_expr)
    (optimize_matches optimize_primitive_univ
      (rw_Reject
        (rm_LogEmpty
          (funpow (nat_of_integer (10 : IntInf.int)) (process_call rs)
            [Rule (MatchAny,
                    Call [#"F", #"O", #"R", #"W", #"A", #"R", #"D"])]))));

fun normalized_ifaces MatchAny = true
  | normalized_ifaces (Match uu) = true
  | normalized_ifaces (MatchNot (Match (IIface uv))) = false
  | normalized_ifaces (MatchNot (Match (OIface uw))) = false
  | normalized_ifaces (MatchAnd (m1, m2)) =
    normalized_ifaces m1 andalso normalized_ifaces m2
  | normalized_ifaces (MatchNot (MatchAnd (ux, uy))) = false
  | normalized_ifaces (MatchNot (Match (Src va))) = true
  | normalized_ifaces (MatchNot (Match (Dst va))) = true
  | normalized_ifaces (MatchNot (Match (Prot va))) = true
  | normalized_ifaces (MatchNot (Match (Src_Ports va))) = true
  | normalized_ifaces (MatchNot (Match (Dst_Ports va))) = true
  | normalized_ifaces (MatchNot (Match (Extra va))) = true
  | normalized_ifaces (MatchNot (MatchNot v)) = true
  | normalized_ifaces (MatchNot MatchAny) = true;

fun proto
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  proto;

fun ipt_ipv4range_to_ipv4_word_netmask (Ip4Addr ip_ddecim) =
  (ipv4addr_of_dotdecimal ip_ddecim, nat_of_integer (32 : IntInf.int))
  | ipt_ipv4range_to_ipv4_word_netmask (Ip4AddrNetmask (pre, len)) =
    (ipv4addr_of_dotdecimal pre, len);

fun sports_update sportsa
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext
    (iiface, oiface, src, dst, proto, sportsa sports, dports, more);

fun oiface_update oifacea
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext
    (iiface, oifacea oiface, src, dst, proto, sports, dports, more);

fun iiface_update iifacea
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext
    (iifacea iiface, oiface, src, dst, proto, sports, dports, more);

fun dports_update dportsa
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext
    (iiface, oiface, src, dst, proto, sports, dportsa dports, more);

fun proto_update protoa
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext
    (iiface, oiface, src, dst, protoa proto, sports, dports, more);

fun src_update srca
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext (iiface, oiface, srca src, dst, proto, sports, dports, more);

fun dst_update dsta
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  Simple_match_ext (iiface, oiface, src, dsta dst, proto, sports, dports, more);

fun common_primitive_match_to_simple_match MatchAny = SOME simple_match_any
  | common_primitive_match_to_simple_match (MatchNot MatchAny) = NONE
  | common_primitive_match_to_simple_match (Match (IIface iif)) =
    SOME (iiface_update (fn _ => iif) simple_match_any)
  | common_primitive_match_to_simple_match (Match (OIface oif)) =
    SOME (oiface_update (fn _ => oif) simple_match_any)
  | common_primitive_match_to_simple_match (Match (Src ip)) =
    SOME (src_update (fn _ => ipt_ipv4range_to_ipv4_word_netmask ip)
           simple_match_any)
  | common_primitive_match_to_simple_match (Match (Dst ip)) =
    SOME (dst_update (fn _ => ipt_ipv4range_to_ipv4_word_netmask ip)
           simple_match_any)
  | common_primitive_match_to_simple_match (Match (Prot p)) =
    SOME (proto_update (fn _ => p) simple_match_any)
  | common_primitive_match_to_simple_match (Match (Src_Ports [])) = NONE
  | common_primitive_match_to_simple_match (Match (Src_Ports [(s, e)])) =
    SOME (sports_update (fn _ => (s, e)) simple_match_any)
  | common_primitive_match_to_simple_match (Match (Dst_Ports [])) = NONE
  | common_primitive_match_to_simple_match (Match (Dst_Ports [(s, e)])) =
    SOME (dports_update (fn _ => (s, e)) simple_match_any)
  | common_primitive_match_to_simple_match (MatchNot (Match (Prot ProtoAny))) =
    NONE
  | common_primitive_match_to_simple_match (MatchAnd (m1, m2)) =
    (case (common_primitive_match_to_simple_match m1,
            common_primitive_match_to_simple_match m2)
      of (NONE, _) => NONE | (SOME _, NONE) => NONE
      | (SOME a, SOME b) => simple_match_and a b)
  | common_primitive_match_to_simple_match (MatchNot (Match (Prot (Proto v)))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (IIface iif))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (OIface oif))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (Src uv))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (Dst uw))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (MatchAnd (ux, uy))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (MatchNot uz)) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (Match (Src_Ports (va :: v :: vc))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (Match (Dst_Ports (vc :: v :: va))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (Src_Ports ve))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (Dst_Ports vf))) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (Match (Extra vg)) =
    (raise Fail "undefined")
  | common_primitive_match_to_simple_match (MatchNot (Match (Extra vh))) =
    (raise Fail "undefined");

fun action_to_simple_action Accept = Accepta
  | action_to_simple_action Drop = Dropa
  | action_to_simple_action Log = (raise Fail "undefined")
  | action_to_simple_action Reject = (raise Fail "undefined")
  | action_to_simple_action (Call v) = (raise Fail "undefined")
  | action_to_simple_action Return = (raise Fail "undefined")
  | action_to_simple_action Empty = (raise Fail "undefined")
  | action_to_simple_action Unknown = (raise Fail "undefined");

fun to_simple_firewall rs =
  map_filter
    (fn Rule (m, a) =>
      (case common_primitive_match_to_simple_match m of NONE => NONE
        | SOME sm => SOME (SimpleRule (sm, action_to_simple_action a))))
    rs;

fun dports
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  dports;

fun iiface
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  iiface;

fun oiface
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  oiface;

fun sports
  (Simple_match_ext (iiface, oiface, src, dst, proto, sports, dports, more)) =
  sports;

fun normalized_dst_ips MatchAny = true
  | normalized_dst_ips (Match uu) = true
  | normalized_dst_ips (MatchNot (Match (Dst uv))) = false
  | normalized_dst_ips (MatchNot (Match (Src v))) = true
  | normalized_dst_ips (MatchNot (Match (IIface v))) = true
  | normalized_dst_ips (MatchNot (Match (OIface v))) = true
  | normalized_dst_ips (MatchNot (Match (Prot v))) = true
  | normalized_dst_ips (MatchNot (Match (Src_Ports v))) = true
  | normalized_dst_ips (MatchNot (Match (Dst_Ports v))) = true
  | normalized_dst_ips (MatchNot (Match (Extra v))) = true
  | normalized_dst_ips (MatchAnd (m1, m2)) =
    normalized_dst_ips m1 andalso normalized_dst_ips m2
  | normalized_dst_ips (MatchNot (MatchAnd (ux, uy))) = false
  | normalized_dst_ips (MatchNot (MatchNot uz)) = false
  | normalized_dst_ips (MatchNot MatchAny) = true;

fun normalized_src_ips MatchAny = true
  | normalized_src_ips (Match uu) = true
  | normalized_src_ips (MatchNot (Match (Src uv))) = false
  | normalized_src_ips (MatchNot (Match (Dst v))) = true
  | normalized_src_ips (MatchNot (Match (IIface v))) = true
  | normalized_src_ips (MatchNot (Match (OIface v))) = true
  | normalized_src_ips (MatchNot (Match (Prot v))) = true
  | normalized_src_ips (MatchNot (Match (Src_Ports v))) = true
  | normalized_src_ips (MatchNot (Match (Dst_Ports v))) = true
  | normalized_src_ips (MatchNot (Match (Extra v))) = true
  | normalized_src_ips (MatchAnd (m1, m2)) =
    normalized_src_ips m1 andalso normalized_src_ips m2
  | normalized_src_ips (MatchNot (MatchAnd (ux, uy))) = false
  | normalized_src_ips (MatchNot (MatchNot uz)) = false
  | normalized_src_ips (MatchNot MatchAny) = true;

fun normalized_protocols MatchAny = true
  | normalized_protocols (Match uu) = true
  | normalized_protocols (MatchNot (Match (Prot uv))) = false
  | normalized_protocols (MatchAnd (m1, m2)) =
    normalized_protocols m1 andalso normalized_protocols m2
  | normalized_protocols (MatchNot (MatchAnd (uw, ux))) = false
  | normalized_protocols (MatchNot (Match (Src va))) = true
  | normalized_protocols (MatchNot (Match (Dst va))) = true
  | normalized_protocols (MatchNot (Match (IIface va))) = true
  | normalized_protocols (MatchNot (Match (OIface va))) = true
  | normalized_protocols (MatchNot (Match (Src_Ports va))) = true
  | normalized_protocols (MatchNot (Match (Dst_Ports va))) = true
  | normalized_protocols (MatchNot (Match (Extra va))) = true
  | normalized_protocols (MatchNot (MatchNot v)) = true
  | normalized_protocols (MatchNot MatchAny) = true;

fun example_ipassignment_nospoof x =
  no_spoofing_iface
    (Iface [#"e", #"t", #"h", #"1", #".", #"1", #"0", #"1", #"7"])
    (fun_upd equal_iface (fn _ => NONE)
      (Iface [#"e", #"t", #"h", #"1", #".", #"1", #"0", #"1", #"7"])
      (SOME [(ipv4addr_of_dotdecimal
                (nat_of_integer (131 : IntInf.int),
                  (nat_of_integer (159 : IntInf.int),
                    (nat_of_integer (14 : IntInf.int),
                      nat_of_integer (240 : IntInf.int)))),
               nat_of_integer (28 : IntInf.int))]))
    x;

fun equal_action Empty Unknown = false
  | equal_action Unknown Empty = false
  | equal_action Return Unknown = false
  | equal_action Unknown Return = false
  | equal_action Return Empty = false
  | equal_action Empty Return = false
  | equal_action (Call x5) Unknown = false
  | equal_action Unknown (Call x5) = false
  | equal_action (Call x5) Empty = false
  | equal_action Empty (Call x5) = false
  | equal_action (Call x5) Return = false
  | equal_action Return (Call x5) = false
  | equal_action Reject Unknown = false
  | equal_action Unknown Reject = false
  | equal_action Reject Empty = false
  | equal_action Empty Reject = false
  | equal_action Reject Return = false
  | equal_action Return Reject = false
  | equal_action Reject (Call x5) = false
  | equal_action (Call x5) Reject = false
  | equal_action Log Unknown = false
  | equal_action Unknown Log = false
  | equal_action Log Empty = false
  | equal_action Empty Log = false
  | equal_action Log Return = false
  | equal_action Return Log = false
  | equal_action Log (Call x5) = false
  | equal_action (Call x5) Log = false
  | equal_action Log Reject = false
  | equal_action Reject Log = false
  | equal_action Drop Unknown = false
  | equal_action Unknown Drop = false
  | equal_action Drop Empty = false
  | equal_action Empty Drop = false
  | equal_action Drop Return = false
  | equal_action Return Drop = false
  | equal_action Drop (Call x5) = false
  | equal_action (Call x5) Drop = false
  | equal_action Drop Reject = false
  | equal_action Reject Drop = false
  | equal_action Drop Log = false
  | equal_action Log Drop = false
  | equal_action Accept Unknown = false
  | equal_action Unknown Accept = false
  | equal_action Accept Empty = false
  | equal_action Empty Accept = false
  | equal_action Accept Return = false
  | equal_action Return Accept = false
  | equal_action Accept (Call x5) = false
  | equal_action (Call x5) Accept = false
  | equal_action Accept Reject = false
  | equal_action Reject Accept = false
  | equal_action Accept Log = false
  | equal_action Log Accept = false
  | equal_action Accept Drop = false
  | equal_action Drop Accept = false
  | equal_action (Call x5) (Call y5) = equal_lista equal_char x5 y5
  | equal_action Unknown Unknown = true
  | equal_action Empty Empty = true
  | equal_action Return Return = true
  | equal_action Reject Reject = true
  | equal_action Log Log = true
  | equal_action Drop Drop = true
  | equal_action Accept Accept = true;

fun simple_rule_iptables_save_toString chain
  (SimpleRule (Simple_match_ext (iif, oif, sip, dip, p, sps, dps, ()), a)) =
  [#"-", #"A", #" "] @
    chain @
      [#" ", #"-", #"s", #" "] @
        ipv4_cidr_toString sip @
          [#" "] @
            [#"-", #"d", #" "] @
              ipv4_cidr_toString dip @
                [#" "] @
                  [#"-", #"p", #" "] @
                    protocol_toString p @
                      [#" "] @
                        (if not (null (iface_toString [#"i", #"n", #":"] iif @
iface_toString [#"o", #"u", #"t", #":"] oif @
  ports_toString [#"s", #"r", #"c", #"p", #"o", #"r", #"t", #"s", #":"] sps @
    ports_toString [#"d", #"s", #"t", #"p", #"o", #"r", #"t", #"s", #":"] dps))
                          then [#"T", #"O", #"D", #"O", #":", #" ", #"m", #"o",
                                 #"r", #"e", #" ", #"f", #"i", #"e", #"l", #"d",
                                 #"s", #" ", #"t", #"o", #" ", #"d", #"u", #"m",
                                 #"p"]
                          else []) @
                          [#" ", #"-", #"j", #" "] @ simple_action_toString a;

fun check_simple_fw_preconditions rs =
  pred_list
    (fn Rule (m, a) =>
      normalized_src_ports m andalso
        (normalized_dst_ports m andalso
          (normalized_src_ips m andalso
            (normalized_dst_ips m andalso
              (normalized_ifaces m andalso
                (normalized_protocols m andalso
                  (not (has_disc is_Extra m) andalso
                    (equal_action a Accept orelse equal_action a Drop))))))))
    rs;

fun bitmask_to_strange_inverse_cisco_mask n =
  dotdecimal_of_ipv4addr
    (bitNOT_word
      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
      (shiftl_word
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (mask (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))) n)
        (minus_nat (nat_of_integer (32 : IntInf.int)) n)));

end; (*struct Test*)
