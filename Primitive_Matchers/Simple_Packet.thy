theory Simple_Packet
imports "../Bitmagic/IPv4Addr" Protocol
begin

section{*Simple Packet*}
  text{*Packet constants are prefixed with p_*}
  record simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src :: ipv4addr
                         p_dst :: ipv4addr
                         p_proto :: primitive_protocol
                         p_sport :: "16 word"
                         p_dport :: "16 word"

end
