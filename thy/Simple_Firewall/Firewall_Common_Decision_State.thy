section\<open>The state of a firewall, abstracted only to the packet filtering outcome\<close>
theory Firewall_Common_Decision_State
imports Main
begin

datatype final_decision = FinalAllow | FinalDeny

text\<open>
The state during packet processing. If undecided, there are some remaining rules to process. If
decided, there is an action which applies to the packet
\<close>
datatype state = Undecided | Decision final_decision

end
