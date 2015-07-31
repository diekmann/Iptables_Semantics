theory SimpleFw_toString
imports 
        "../Common/Lib_toString"
        "../Primitive_Matchers/Common_Primitive_toString"
        "../Simple_Firewall/SimpleFw_Semantics"
begin


section{*toString Functions*}


fun simple_action_toString :: "simple_action \<Rightarrow> string" where
  "simple_action_toString Accept = ''ACCEPT''" |
  "simple_action_toString Drop = ''DROP''"


fun simple_rule_toString :: "simple_rule \<Rightarrow> string" where
  "simple_rule_toString (SimpleRule \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> a) = 
      simple_action_toString a @ ''     '' @ 
      protocol_toString p @ ''  --  '' @ 
      ipv4_cidr_toString sip @ ''            '' @
      ipv4_cidr_toString dip @ '' '' @ 
      iface_toString ''in: '' iif @ '' '' @ 
      iface_toString ''out: '' oif @ '' '' @ 
      ports_toString ''sports: '' sps @ '' '' @ 
      ports_toString ''dports: '' dps"


fun simple_rule_iptables_save_toString :: "string \<Rightarrow> simple_rule \<Rightarrow> string" where
  "simple_rule_iptables_save_toString chain (SimpleRule \<lparr>iiface=iif, oiface=oif, src=sip, dst=dip, proto=p, sports=sps, dports=dps \<rparr> a) = 
    ''-A ''@chain@'' -s '' @ ipv4_cidr_toString sip @ '' '' @
                  ''-d '' @ ipv4_cidr_toString dip @ '' '' @
                  ''-p '' @ protocol_toString p @ '' '' @
                  (if (iface_toString ''in:'' iif)@(iface_toString ''out:'' oif)@
                      (ports_toString ''srcports:'' sps)@(ports_toString ''dstports:'' dps) \<noteq> ''''
                   then ''TODO: more fields to dump'' else '''') @
                  '' -j '' @ simple_action_toString a"


end
