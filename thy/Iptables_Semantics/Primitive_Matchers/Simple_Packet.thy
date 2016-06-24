theory Simple_Packet
imports "../../IP_Addresses/IPv4Addr" Protocol Conntrack_State
begin

section\<open>Simple Packet\<close>
  text\<open>Packet constants are prefixed with @{text p}\<close>

  text\<open>@{typ "'i::len word"} is an IP address of variable length. 32bit for IPv4, 128bit for IPv6\<close>

  record (overloaded) 'i simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src :: "'i::len word"
                         p_dst :: "'i::len word"
                         p_proto :: primitive_protocol
                         p_sport :: "16 word"
                         p_dport :: "16 word"
                         p_tcp_flags :: "tcp_flag set"
                         p_tag_ctstate :: ctstate


  value "\<lparr> 
          p_iiface = ''eth1'', p_oiface = '''', 
          p_src = 0, p_dst = 0, 
          p_proto = TCP, p_sport = 0, p_dport = 0, 
          p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New
         \<rparr>"
end
