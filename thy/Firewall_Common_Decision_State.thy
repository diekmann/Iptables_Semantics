theory Firewall_Common_Decision_State
imports Main
begin

datatype final_decision = FinalAllow | FinalDeny (*TODO: Unknown, e.g. for NAT?*)

text{*
The state during packet processing. If undecided, there are some remaining rules to process. If
decided, there is an action which applies to the packet
*}
datatype state = Undecided | Decision final_decision

end
