theory No_Spoof
imports Common_Primitive_Matcher
  "../Common/Negation_Type_DNF"
begin

section{*No Spoofing*}
(* we do this in ternary (not simple firewall) to support things such as negated interfaces *)
  text{*assumes: @{const simple_ruleset}*}

  text{*A mapping from an interface to its assigned ip addresses in CIDR notation*}
  type_synonym ipassignment="iface \<rightharpoonup> (ipv4addr \<times> nat) set"

  (*
  check wool: warning if zone-spanning
  
  warning if interface map has wildcards
  
  warning if interface occurs in ruleset but not in ipassignment (typo?)
  *)

  text{*
  No spoofing means:
  Every packet that is (potentially) allowed by the firewall and comes from an interface @{text iface} 
  must have a Source IP Address in the assigned range @{text iface}.
  
  ``potentially allowed'' means we use the upper closure.
  The definition states: For all interfaces which are configured, every packet that comes from this
  interface and is allowed by the firewall must be in the IP range of that interface.
  *}
  definition no_spoofing :: "ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> bool" where
    "no_spoofing ipass rs \<equiv> \<forall> iface \<in> dom ipass.  \<forall>p.
        ((common_matcher, in_doubt_allow),p\<lparr>p_iiface:=iface_sel iface\<rparr>\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow>\<^sub>\<alpha> Decision FinalAllow) \<longrightarrow>
            p_src p \<in> (\<Union>(base, len) \<in> the (ipass iface). ipv4range_set_from_bitmask base len)"

(*
and now code to check this ....
  only need to trace: src_ip and iiface
  try some packet_set dnf with this?
  collect all src_ips allowed for a specific iiface?
  check collected src_ips subseteq ipassignment(iface)
*)

  fun no_spoofing_algorithm :: "iface \<Rightarrow> ipassignment \<Rightarrow> common_primitive rule list \<Rightarrow> (ipv4addr \<times> nat) set \<Rightarrow> bool" where
    "no_spoofing_algorithm iface ipass [] allowed = 
      ((\<Union>(base, len) \<in> allowed. ipv4range_set_from_bitmask base len) \<subseteq> (\<Union>(base, len) \<in> the (ipass iface). ipv4range_set_from_bitmask base len))" |
    "no_spoofing_algorithm iface ipass ((Rule m a)#rs) allowed = True"


end