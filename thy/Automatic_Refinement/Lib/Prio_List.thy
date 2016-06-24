section {* Priority Lists *}
theory Prio_List
imports Main
begin
ML {*
  (*
    We provide a list of items with insertion operation relative to other
    items (after, before) and relative to absolute positions (first, last).
  *)
  signature PRIO_LIST = sig
    type T
    type item

    val empty: T
    val add_first: T -> item -> T
    val add_last: T -> item -> T
    val add_before: T -> item -> item -> T
    val add_after: T -> item -> item -> T

    val delete: item -> T -> T

    val prio_of: (item -> bool) -> (item * item -> bool) -> T -> int
    val contains: T -> item -> bool

    val dest: T -> item list

    val merge: T * T -> T  (* Ignore conflicts *)
    val merge': T * T -> item list * T (* Return conflicting items *)

  end

  functor Prio_List (
    type item; 
    val eq: item * item -> bool
  ): PRIO_LIST = struct
    type item = item
    type T = item list

    val empty = []
    fun add_first l e = remove eq e l@[e]
    fun add_last l e = e::remove eq e l

    fun add_before l e a = let 
      val l = remove eq e l
      val (l1,(l2,l3)) = take_prefix (fn x => not (eq (x,a))) l ||> chop 1
    in l1@l2@e::l3 end;

    fun add_after l e b = let 
      val l = remove eq e l
      val (l1,l2) = take_prefix (fn x => not (eq (x,b))) l
    in l1@e::l2 end

    val delete = remove eq

    fun prio_of P prefer l = let
      fun do_prefer _ NONE = true
        | do_prefer x (SOME (_,y)) = prefer (x,y)

      fun pr [] _ st = (case st of NONE => ~1 | SOME (i,_) => i)
        | pr (x::l) i st = if P x andalso do_prefer x st then
            pr l (i+1) (SOME (i,x))
          else
            pr l (i+1) st

    in
      pr l 0 NONE
    end

    val contains = member eq

    fun dest l = l

    fun merge' (l1,l2) = let
      val l1' = map (fn ty => (Library.member eq l2 ty,ty)) l1;
      val l2' = map (fn ty => (Library.member eq l1 ty,ty)) l2;

      fun m []                []               = []
        | m []                l                = map (apfst (K false)) l
        | m l                 []               = map (apfst (K false)) l
        | m ((true,t1)::l1)   ((true,t2)::l2)  = 
          (not (eq (t1,t2)),t2) :: m l1 l2 
        | m ((false,t1)::l1)  ((true,t2)::l2)  = 
          (false,t1) :: m l1 ((true,t2)::l2)
        | m ((true,t1)::l1)   ((false,t2)::l2) = 
          (false,t2) :: m ((true,t1)::l1) l2
        | m ((false,t1)::l1)  ((false,t2)::l2) = 
          (false,t2)::(false,t1)::m l1 l2
  
      val r = m l1' l2'
    in
      (map #2 (filter #1 r), map #2 r)
    end;

    fun merge (l1,l2) = #2 (merge' (l1,l2))

  end
*}

end
