theory Simple_Packet
imports "../Bitmagic/IPv4Addr" Protocol Conntrack_State
begin

section{*Simple Packet*}
  text{*Packet constants are prefixed with @{text p}*}
  record simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src :: ipv4addr
                         p_dst :: ipv4addr
                         p_proto :: primitive_protocol
                         p_sport :: "16 word"
                         p_dport :: "16 word"
                         p_tcp_flags :: "tcp_flag set"
                         p_tag_ctstate :: ctstate

  value "\<lparr>p_iiface = ''eth1'', p_oiface = '''', p_src = 0, p_dst = 0, p_proto = TCP, p_sport = 0, p_dport = 0, p_tcp_flags = {TCP_SYN}, p_tag_ctstate = CT_New\<rparr>"
end
