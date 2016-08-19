section\<open>Simple Packet\<close>
theory Simple_Packet
imports "Primitives/L4_Protocol"
begin

  text\<open>Packet constants are prefixed with @{text p}\<close>

  text\<open>@{typ "'i::len word"} is an IP address of variable length. 32bit for IPv4, 128bit for IPv6\<close>

  text\<open>A simple packet with IP addresses and layer four ports.
             Also has the following phantom fields:
             Input and Output network interfaces\<close>

  record (overloaded) 'i simple_packet = p_iiface :: string
                         p_oiface :: string
                         p_src :: "'i::len word"
                         p_dst :: "'i::len word"
                         p_proto :: primitive_protocol
                         p_sport :: "16 word"
                         p_dport :: "16 word"
                         p_tcp_flags :: "tcp_flag set"
                         p_payload :: string


  value "\<lparr> 
          p_iiface = ''eth1'', p_oiface = '''', 
          p_src = 0, p_dst = 0, 
          p_proto = TCP, p_sport = 0, p_dport = 0, 
          p_tcp_flags = {TCP_SYN},
          p_payload = ''arbitrary payload''
         \<rparr>"

  text\<open>We suggest to use @{typ "('i,'pkt_ext) simple_packet_scheme"} instead of 
        @{typ "'i simple_packet"} because of its extensibility which naturally 
        models any payload\<close>

  
  definition simple_packet_unext :: "('i::len, 'a) simple_packet_scheme \<Rightarrow> 'i simple_packet" where
    "simple_packet_unext p \<equiv>
      \<lparr>p_iiface = p_iiface p, p_oiface = p_oiface p, p_src = p_src p, p_dst = p_dst p, p_proto = p_proto p, 
       p_sport = p_sport p, p_dport = p_dport p, p_tcp_flags = p_tcp_flags p, 
       p_payload = p_payload p\<rparr>"

  text\<open>An extended simple packet with MAC addresses and VLAN header\<close>
  
  record (overloaded) 'i simple_packet_ext = "'i::len simple_packet" +
    p_l2type :: "16 word"
    p_l2src :: "48 word"
    p_l2dst :: "48 word"
    p_vlanid :: "16 word"
    p_vlanprio :: "16 word"

end
