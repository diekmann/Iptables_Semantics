theory Iface
imports String "../Output_Format/Negation_Type"
begin

section{*Network Interfaces*}

datatype iface = Iface "string negation_type" | IfaceAny

text_raw{*If the interface name ends in a ``+'', then any interface which begins with this name will match. (man iptables)

Here is how iptables handles this wildcard on my system. A packet for the loopback interface \texttt{lo} is matched by the following expressions
\begin{itemize}
  \item lo
  \item lo+
  \item l+
  \item +
\end{itemize}

It is not matched by the following expressions
\begin{itemize}
  \item lo++
  \item lo+++
  \item lo1+
  \item lo1
\end{itemize}

By the way: \texttt{Warning: weird character in interface ` ' ('/' and ' ' are not allowed by the kernel).}
*}

fun iface_name_eq :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "iface_name_eq [] [] \<longleftrightarrow> True" |
  "iface_name_eq [i1] [] \<longleftrightarrow> (i1 = CHR ''+'')" |
  "iface_name_eq [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
  "iface_name_eq [i1] [i2] \<longleftrightarrow> (i1 = CHR ''+'' \<or> i2 = CHR ''+'' \<or> i1 = i2)" |
  "iface_name_eq (i1#i1s) (i2#i2s) \<longleftrightarrow> (i1 = CHR ''+'' \<and> i1s = [] \<or> i2 = CHR ''+'' \<and> i2s = []) \<or> (i1 = i2 \<and> iface_name_eq i1s i2s)" |
  "iface_name_eq _ _ \<longleftrightarrow> False"


  lemma "iface_name_eq ''lo'' ''lo''" by eval
  lemma "iface_name_eq ''lo'' ''lo+''" by eval
  lemma "iface_name_eq ''lo'' ''l+''" by eval
  lemma "iface_name_eq ''lo'' ''+''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo++''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo+++''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo1+''" by eval
  lemma "\<not> iface_name_eq ''lo'' ''lo1''" by eval
  text{*The wildcard interface name*}
  lemma "iface_name_eq '''' ''+''" by eval

fun iface_name_is_wildcard :: "string \<Rightarrow> bool" where
  "iface_name_is_wildcard [] \<longleftrightarrow> False" |
  "iface_name_is_wildcard [s] \<longleftrightarrow> s = CHR ''+''" |
  "iface_name_is_wildcard (_#ss) \<longleftrightarrow> iface_name_is_wildcard ss"
lemma iface_name_is_wildcard_alt: "iface_name_is_wildcard eth \<longleftrightarrow> eth \<noteq> [] \<and> hd (rev eth) = CHR ''+''"
  apply(induction eth rule: iface_name_is_wildcard.induct)
   apply(simp_all)
  apply(rename_tac s s' ss)
  apply(case_tac "rev ss")
   apply(simp_all)
  done
(*lemma iface_name_is_wildcard_cases: "iface_name_is_wildcard eth \<longleftrightarrow> (case rev eth of [] \<Rightarrow> False | s#ss \<Rightarrow> s = CHR ''+'')"
  apply(induction eth rule: iface_name_is_wildcard.induct)
   apply(simp_all)
  apply(rename_tac s s' ss)
  apply(case_tac "rev ss")
   apply(simp_all)
  done*)

lemma iface_name_eq_alt: "iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2 \<or>
      iface_name_is_wildcard i1 \<and> take ((length i1) - 1) i1 = take ((length i1) - 1) i2 \<or>
      iface_name_is_wildcard i2 \<and> take ((length i2) - 1) i2 = take ((length i2) - 1) i1"
apply(induction i1 i2 rule: iface_name_eq.induct)
       apply(simp_all)
  apply(simp_all add: iface_name_is_wildcard_alt take_Cons' split:split_if_asm)
        apply(safe)
done

lemma iface_name_eq_refl: "iface_name_eq is is"
proof -
{ fix i1 i2
  have "i1 = i2 \<Longrightarrow> iface_name_eq i1 i2"
    by(induction i1 i2 rule: iface_name_eq.induct)(auto)
 } thus ?thesis by simp 
qed
lemma iface_name_eq_sym: "iface_name_eq i1 i2 \<Longrightarrow> iface_name_eq i2 i1"
  by(induction i1 i2 rule: iface_name_eq.induct)(auto split: split_if_asm)

lemma "iface_name_eq (i2 # i2s) [] \<Longrightarrow> i2 = CHR ''+'' \<and> i2s = []"
proof -
assume a: "iface_name_eq (i2 # i2s) []"
{ fix x1 x2
  have "x1 = (i2 # i2s) \<Longrightarrow> x2 = [] \<Longrightarrow> iface_name_eq x1 x2 \<Longrightarrow> i2 = CHR ''+'' \<and> i2s = []"
  by(induction x1 x2 rule: iface_name_eq.induct) (auto)
} thus ?thesis using a by simp
qed



text{*Examples*}
  lemma iface_name_eq_not_trans: "\<lbrakk>i1 = ''eth0''; i2 = ''eth+''; i3 = ''eth1''\<rbrakk> \<Longrightarrow> 
      iface_name_eq i1 i2 \<Longrightarrow> iface_name_eq i2 i3 \<Longrightarrow> \<not> iface_name_eq i1 i3"
    by(simp)
  lemma "iface_name_eq ''eth+'' ''eth3''" by eval
  lemma "iface_name_eq ''eth+'' ''e+''" by eval
  lemma "iface_name_eq ''eth+'' ''eth_tun_foobar''" by eval
  lemma "iface_name_eq ''eth+'' ''eth_tun+++''" by eval
  lemma "\<not> iface_name_eq ''eth+'' ''wlan+''" by eval
  lemma "iface_name_eq ''eth1'' ''eth1''" by eval
  lemma "\<not> iface_name_eq ''eth1'' ''eth2''" by eval
  lemma "iface_name_eq ''eth+'' ''eth''" by eval
  lemma "\<not> iface_name_eq ''a'' ''b+''" by eval
  lemma "iface_name_eq ''+'' ''''" by eval
  lemma "iface_name_eq ''++++'' ''+''" by eval
  text{*If the interfaces don't end in a wildcard, then @{const iface_name_eq} is just simple equality*}
  lemma "\<lbrakk> hd (rev i1) \<noteq> CHR ''+''; hd (rev i2) \<noteq> CHR ''+'' \<rbrakk> \<Longrightarrow> iface_name_eq i1 i2 \<longleftrightarrow> i1 = i2"
    apply(induction i1 i2 rule: iface_name_eq.induct)
    apply(simp_all)
apply (metis append_Nil hd_Cons_tl hd_append2 iface_name_eq.simps(3) iface_name_eq.simps(8) iface_name_eq_sym list.sel(1) rev_is_Nil_conv)
by (metis append_Nil hd_Cons_tl hd_append2 iface_name_eq.simps(2) iface_name_eq.simps(7) iface_name_eq_sym list.sel(1) rev_is_Nil_conv)
    

  
  fun iface_name_leq :: "string \<Rightarrow> string \<Rightarrow> bool" where
    "iface_name_leq [] [] \<longleftrightarrow> True" |
    "iface_name_leq [i1] [] \<longleftrightarrow> False" |
    "iface_name_leq [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
    "iface_name_leq [i1] [i2] \<longleftrightarrow> (i1 = i2 \<or> i2 = CHR ''+'')" |
    "iface_name_leq (i1#i1s) (i2#i2s) \<longleftrightarrow> (i2 = CHR ''+'' \<and> i2s = []) \<or> (i1 = i2 \<and> iface_name_leq i1s i2s)" |
    "iface_name_leq _ _ \<longleftrightarrow> False"

  lemma "iface_name_leq i1 i2 \<longleftrightarrow> card {i. iface_name_eq i1 i} \<le> card {i. iface_name_eq i2 i}"
    oops
  lemma "iface_name_leq i1 i2 \<longleftrightarrow> iface_name_eq i1 i2 \<and> (
            i1 = i2 \<or> 
            iface_name_is_wildcard i2 \<and> \<not> iface_name_is_wildcard i1 \<or>
            iface_name_is_wildcard i1 \<and> iface_name_is_wildcard i2 \<and> take ((length i2) - 1) i2 = take ((length i2) - 1) i1)"
    apply(induction i1 i2 rule: iface_name_leq.induct)
     apply(simp_all)
     apply(safe)
     apply(simp_all)
     apply(auto elim: iface_name_leq.elims) (* OMG WTF *)
     done


subsection{*Matching*}
    
fun match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
  "match_iface IfaceAny p_iface \<longleftrightarrow> True" |
  "match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> iface_name_eq p_iface i" |
  "match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> \<not> iface_name_eq p_iface i"


fun match_iface_and :: "iface \<Rightarrow> iface \<Rightarrow> iface option" where
  "match_iface_and i IfaceAny = Some i" |
  "match_iface_and IfaceAny i = Some i" |
  "match_iface_and (Iface (Pos i1)) (Iface (Pos i2)) = (if iface_name_eq i1 i2 \<dots>)" (*we need the 'shorter' iface. probably we want a pseudo order on the ifaces*)
    (*An order which is not transitive?*)

end
