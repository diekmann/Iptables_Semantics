signature COND_REWR_CONV = sig
  val cond_rewr_conv: tactic -> thm -> Proof.context -> conv
  val cond_rewrs_conv: tactic -> thm list -> Proof.context -> conv
end

structure Cond_Rewr_Conv :COND_REWR_CONV = struct
  open Refine_Util
  (* Conditional rewrite rule. tac used to discharge conditions *)
  fun cond_rewr_conv_aux tac thm ctxt ct = let
    val lhs = thm |> Thm.concl_of |> Logic.dest_equals |> #1 |> Thm.cterm_of ctxt
    val inst = Thm.match (lhs,ct) 
      handle Pattern.MATCH => raise CTERM ("dis_rewr_conv: MATCH",[lhs,ct])

    val thm' = Thm.instantiate inst thm
    val dprems = Thm.prems_of thm' 
    val dthms = map (fn t => 
      (Goal.prove ctxt [] [] t (K tac)) handle ERROR s 
        => raise TERM ("dis_rew_conv: "^ s,[t])) dprems
    val res = thm' OF dthms
  in res end;

  fun cond_rewr_conv tac thm ctxt = fix_conv ctxt (cond_rewr_conv_aux tac thm ctxt)

  (*fun first_conv [] ct = Conv.no_conv ct
    | first_conv (cv::cvs) ct = (cv else_conv first_conv cvs) ct*)

  fun cond_rewrs_conv tac thms ctxt = 
    Conv.first_conv (map (fn thm => cond_rewr_conv tac thm ctxt) thms) 

end
