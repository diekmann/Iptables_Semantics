theory OpenFlow_Action
imports
	OpenFlow_Matches
begin

(* Beware the differences between Actions and Instructions. OF1.0 doesn't support the former and they're thus not modelled here. *)

(* OF1.0 says actions are a list and executed in-order, OF1.5 has two things: an action set with fixed order in 5.6 and an action list.
So\<dots> list. *)

(* Just those which we need(ed). *)
datatype of_action = Forward (oiface_sel: string) | ModifyField_l2dst "48 word"
(* Note that the 1.0 is not entirely clear that there's no drop action. 1.5 clarifies that this is represented by and empty instruction/action set. *)

(* So each flow entry has a list of these. Semantics\<dots> The actions are executed in order, but the order of the side-effects is not defined. *)
fun of_action_semantics where
"of_action_semantics p [] = {}" |
"of_action_semantics p (a#as) = (case a of
	Forward i \<Rightarrow> insert (i,p) (of_action_semantics p as) |
	ModifyField_l2dst a \<Rightarrow> of_action_semantics (p\<lparr>p_l2dst := a\<rparr>) as)"

value "of_action_semantics p []" (* Drop *)
value "of_action_semantics p [ModifyField_l2dst 66, Forward ''oif'']" (* set mac and send *)

end