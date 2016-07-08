theory Tagged_Packet
imports "../../Simple_Firewall/Simple_Packet" Conntrack_State
begin

section\<open>Tagged Simple Packet\<close>
  text\<open>Packet constants are prefixed with @{text p}\<close>

  text\<open>A packet tagged with the following phantom fields:
             conntrack connection state\<close>

  text\<open>The idea to tag the connection state into the packet is sound.
       See @{file "../Semantics_Stateful.thy"}\<close>

  record (overloaded) 'i tagged_packet = "'i::len simple_packet" +
                         p_tag_ctstate :: ctstate


  value "\<lparr> 
          p_iiface = ''eth1'', p_oiface = '''', 
          p_src = 0, p_dst = 0, 
          p_proto = TCP, p_sport = 0, p_dport = 0, 
          p_tcp_flags = {TCP_SYN},
          p_payload = ''arbitrary payload'',
          p_tag_ctstate = CT_New
         \<rparr>:: 32 tagged_packet"

  definition simple_packet_tag
    :: "ctstate \<Rightarrow> ('i::len, 'a) simple_packet_scheme \<Rightarrow> ('i::len, 'a) tagged_packet_scheme" where
    "simple_packet_tag ct_state p \<equiv>
      \<lparr>p_iiface = p_iiface p, p_oiface = p_oiface p, p_src = p_src p, p_dst = p_dst p, p_proto = p_proto p, 
       p_sport = p_sport p, p_dport = p_dport p, p_tcp_flags = p_tcp_flags p, 
       p_payload = p_payload p,
       p_tag_ctstate = ct_state,
       \<dots> = simple_packet.more p\<rparr>"

  definition tagged_packet_untag
    :: "('i::len, 'a) tagged_packet_scheme \<Rightarrow> ('i::len, 'a) simple_packet_scheme" where
    "tagged_packet_untag p \<equiv>
      \<lparr>p_iiface = p_iiface p, p_oiface = p_oiface p, p_src = p_src p, p_dst = p_dst p, p_proto = p_proto p, 
       p_sport = p_sport p, p_dport = p_dport p, p_tcp_flags = p_tcp_flags p, 
       p_payload = p_payload p,
       \<dots> = tagged_packet.more p\<rparr>"

  lemma "tagged_packet_untag (simple_packet_tag ct_state p) = p"
        "simple_packet_tag ct_state (tagged_packet_untag p) = p\<lparr>p_tag_ctstate := ct_state\<rparr>"
    apply(case_tac [!] p)
     by(simp add: tagged_packet_untag_def simple_packet_tag_def)+
    

end
