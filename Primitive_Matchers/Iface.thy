theory Iface
imports String "../Output_Format/Negation_Type"
begin

datatype iface = Iface "string negation_type" | IfaceAny

text{*If the interface name ends in a "+", then any interface which begins with this name will match. (man iptables)*}
fun cmp_iface_name :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "cmp_iface_name [] [] \<longleftrightarrow> True" |
  "cmp_iface_name [i1] [] \<longleftrightarrow> (i1 = CHR ''+'')" |
  "cmp_iface_name [] [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
  "cmp_iface_name [i1] [i2] \<longleftrightarrow> (i1 = CHR ''+'' \<or> i2 = CHR ''+'' \<or> i1 = i2)" |
  "cmp_iface_name [i1] i2s \<longleftrightarrow> (i1 = CHR ''+'')" |
  "cmp_iface_name i1s [i2] \<longleftrightarrow> (i2 = CHR ''+'')" |
  "cmp_iface_name (i1#i1s) (i2#i2s) \<longleftrightarrow> (if i1 = i2 then cmp_iface_name i1s i2s else False)" |
  "cmp_iface_name _ _ \<longleftrightarrow> False"

lemma cmp_iface_name_refl: "cmp_iface_name is is"
proof -
{ fix i1 i2
  have "i1 = i2 \<Longrightarrow> cmp_iface_name i1 i2"
    by(induction i1 i2 rule: cmp_iface_name.induct)(auto)
 } thus ?thesis by simp 
qed
lemma cmp_iface_name_sym: "cmp_iface_name i1 i2 \<Longrightarrow> cmp_iface_name i2 i1"
  by(induction i1 i2 rule: cmp_iface_name.induct)(auto split: split_if_asm)

lemma "cmp_iface_name (i2 # i2s) [] \<Longrightarrow> i2 = CHR ''+''"
proof -
assume a: "cmp_iface_name (i2 # i2s) []"
{ fix x1 x2
  have "x1 = (i2 # i2s) \<Longrightarrow> x2 = [] \<Longrightarrow> cmp_iface_name x1 x2 \<Longrightarrow> i2 = CHR ''+''"
  by(induction x1 x2 rule: cmp_iface_name.induct) (auto)
} thus ?thesis using a by simp
qed

text{*Examples*}
  lemma cmp_iface_name_not_trans: "\<lbrakk>i1 = ''eth0''; i2 = ''eth+''; i3 = ''eth1''\<rbrakk> \<Longrightarrow> cmp_iface_name i1 i2 \<Longrightarrow> cmp_iface_name i2 i3 \<Longrightarrow> \<not> cmp_iface_name i1 i3"
    by(simp)
  lemma "cmp_iface_name ''+'' i2"
    by(induction "''+''" i2 rule: cmp_iface_name.induct) (simp_all)
  lemma "cmp_iface_name ''eth+'' ''eth3''" by eval
  lemma "cmp_iface_name ''eth+'' ''e+''" by eval
  lemma "cmp_iface_name ''eth+'' ''eth_tun_foobar''" by eval
  lemma "cmp_iface_name ''eth+'' ''eth_tun+++''" by eval
  lemma "\<not> cmp_iface_name ''eth+'' ''wlan+''" by eval
  lemma "cmp_iface_name ''eth1'' ''eth1''" by eval
  lemma "\<not> cmp_iface_name ''eth1'' ''eth2''" by eval
  text{*If the interfaces don't end in a wildcard, then @{const cmp_iface_name} is just simple equality*}
  lemma "\<lbrakk> hd (rev i1) \<noteq> CHR ''+''; hd (rev i2) \<noteq> CHR ''+'' \<rbrakk> \<Longrightarrow> cmp_iface_name i1 i2 \<longleftrightarrow> i1 = i2"
    apply(induction i1 i2 rule: cmp_iface_name.induct)
    apply(simp_all)
    apply (metis append_Nil hd_append2 list.sel(1))+
    done
    
fun match_iface :: "iface \<Rightarrow> string \<Rightarrow> bool" where
  "match_iface IfaceAny p_iface \<longleftrightarrow> True" |
  "match_iface (Iface (Pos i)) p_iface \<longleftrightarrow> cmp_iface_name p_iface i" |
  "match_iface (Iface (Neg i)) p_iface \<longleftrightarrow> \<not> cmp_iface_name p_iface i"

end
