theory IPPortSpace_Matcher
imports "../Semantics_Ternary" IPPortSpace_Syntax IPSpace_Matcher "../Bitmagic/IPv4Addr" "../Unknown_Match_Tacs"
begin




subsection{*Primitive Matchers: IP Port Space Matcher*}



fun ipport_matcher :: "(ipport_rule_match, packet_with_ports) exact_match_tac" where
  "ipport_matcher (Src ip) p = bool_to_ternary (src_ip p \<in> ipv4s_to_set ip)" |

  "ipport_matcher (Dst ip) p = bool_to_ternary (dst_ip p \<in> ipv4s_to_set ip)" |

  "ipport_matcher (Prot ProtAll) _ = TernaryTrue" |
  "ipport_matcher (Prot ipt_protocol.ProtTCP) p = bool_to_ternary (prot p = protPacket.ProtTCP)" |
  "ipport_matcher (Prot ipt_protocol.ProtUDP) p = bool_to_ternary (prot p = protPacket.ProtUDP)" |

  "ipport_matcher (Src_Port ps) p = bool_to_ternary (src_port p \<in> ports_to_set ps)" |

  "ipport_matcher (Dst_Port ps) p = bool_to_ternary (dst_port p \<in> ports_to_set ps)" |

  "ipport_matcher (Extra _) p = TernaryUnknown"

end
