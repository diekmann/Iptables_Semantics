theory OpenFlow_Serialize
imports OpenFlow_Matches
        OpenFlow_Action
        Semantics_OpenFlow
        "../Simple_Firewall/Primitives/Primitives_toString"
        "../IP_Addresses/Lib_Word_toString"
        "~~/src/HOL/Library/Code_Char"
begin

definition "serialization_test_entry \<equiv> OFEntry 7 {EtherDst 0x1, IPv4Dst (PrefixMatch 0xA000201 32), IngressPort ''s1-lan'', L4Dst 0x50 0, L4Src 0x400 0x3FF, IPv4Proto 6, EtherType 0x800} [ModifyField_l2dst 0xA641F185E862, Forward ''s1-wan'']"



value "(map (op << (1::48 word) \<circ> op * 8) \<circ> rev) [0..<6]"

definition "serialize_mac (m::48 word) \<equiv> (intersperse (CHR '':'') \<circ> map (hex_string_of_word 1 \<circ> (\<lambda>h. (m >> h * 8) && 0xff)) \<circ> rev) [0..<6]"
lemma "serialize_mac 0xdeadbeefcafe = ''de:ad:be:ef:ca:fe''" by eval

definition "serialize_action pids a \<equiv> (case a of
	Forward oif \<Rightarrow> ''output:'' @ pids oif |
	ModifyField_l2dst na \<Rightarrow> ''mod_dl_dst:'' @ serialize_mac na)" 

definition "serialize_actions pids a \<equiv> if length a = 0 then ''drop'' else (intersperse (CHR '','') \<circ> map (serialize_action pids)) a"

lemma "serialize_actions (\<lambda>oif. ''42'') (ofe_action serialization_test_entry) =
  ''mod_dl_dst:a6:41:f1:85:e8:62,output:42''" by eval
lemma "serialize_actions anything [] = ''drop''"
  by(simp add: serialize_actions_def)

definition "prefix_to_string pfx \<equiv> ipv4_cidr_toString (pfxm_prefix pfx, pfxm_length pfx)"

primrec serialize_of_match where
"serialize_of_match pids (IngressPort p) = ''in_port='' @ pids p" |
"serialize_of_match _ (VlanId i) = ''dl_vlan='' @ dec_string_of_word0 i" |
"serialize_of_match _ (VlanPriority _) = undefined" | (* uh, äh\<dots> We don't use that anyway\<dots> *)
"serialize_of_match _ (EtherType i) = ''dl_type=0x'' @ hex_string_of_word0 i" |
"serialize_of_match _ (EtherSrc m) = ''dl_src='' @ serialize_mac m" |
"serialize_of_match _ (EtherDst m) = ''dl_dst='' @ serialize_mac m" |
"serialize_of_match _ (IPv4Proto i) = ''nw_proto='' @ dec_string_of_word0 i" |
"serialize_of_match _ (IPv4Src p) = ''nw_src='' @ prefix_to_string p" |
"serialize_of_match _ (IPv4Dst p) = ''nw_dst='' @ prefix_to_string p" |
"serialize_of_match _ (L4Src i m) = ''tp_src='' @ dec_string_of_word0 i @ (if m = max_word then [] else ''/0x'' @ hex_string_of_word 3 m)" |
"serialize_of_match _ (L4Dst i m) = ''tp_dst='' @ dec_string_of_word0 i @ (if m = max_word then [] else ''/0x'' @ hex_string_of_word 3 m)"

definition serialize_of_matches :: "(string \<Rightarrow> string) \<Rightarrow> of_match_field set \<Rightarrow> string"
  where
  "serialize_of_matches pids \<equiv> op @ ''hard_timeout=0,idle_timeout=0,'' \<circ> intersperse (CHR '','') \<circ> map (serialize_of_match pids) \<circ> sorted_list_of_set" 

lemma "serialize_of_matches pids of_matches= 
(List.append ''hard_timeout=0,idle_timeout=0,'') 
  (intersperse (CHR '','') (map (serialize_of_match pids) (sorted_list_of_set of_matches)))"
by (simp add: serialize_of_matches_def)

export_code serialize_of_matches checking SML (*needs "~~/src/HOL/Library/Code_Char"*)

lemma "serialize_of_matches (\<lambda>oif. ''42'') (ofe_fields serialization_test_entry) =
  ''hard_timeout=0,idle_timeout=0,in_port=42,dl_type=0x800,dl_dst=00:00:00:00:00:01,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=1024/0x03ff,tp_dst=80/0x0000''"
by eval

definition "serialize_of_entry pids e \<equiv> (case e of (OFEntry p f a) \<Rightarrow> ''priority='' @ dec_string_of_word0 p @ '','' @ serialize_of_matches pids f @ '','' @ ''action='' @ serialize_actions pids a)"

lemma "serialize_of_entry (the \<circ> map_of [(''s1-lan'',''42''),(''s1-wan'',''1337'')]) serialization_test_entry =
  ''priority=7,hard_timeout=0,idle_timeout=0,in_port=42,dl_type=0x800,dl_dst=00:00:00:00:00:01,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=1024/0x03ff,tp_dst=80/0x0000,action=mod_dl_dst:a6:41:f1:85:e8:62,output:1337''"
  by eval


end