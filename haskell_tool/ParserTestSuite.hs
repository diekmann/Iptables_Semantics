module ParserTestSuite ( tests ) where

import Distribution.TestSuite
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import qualified Data.Map as M
import qualified Network.IPTables.Generated as Isabelle


expected_result = "*filter\n\
    \:DOS~Pro-t_ect - [0:0]\n\
    \:FORWARD DROP [0:0]\n\
    \:INPUT ACCEPT [1101:228112]\n\
    \:IPSEC_42 - [0:0]\n\
    \:LOGDROP - [0:0]\n\
    \:OUTPUT ACCEPT [70:23175]\n\
    \:Terminal - [0:0]\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p tcp' `ParsedMatch --dpts [22]' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p tcp' `ParsedMatch -m state --state NEW' `ParsedMatch --dpts [1:65535]' `ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p udp' `ParsedAction -j RETURN'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' `ParsedMatch ~~-m~~' `ParsedMatch ~~icmp~~' `ParsedMatch ~~--icmp-type~~' `ParsedMatch ~~3/4~~' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' `ParsedMatch ~~-m~~' `ParsedMatch ~~comment~~' `ParsedMatch ~~--comment~~' `ParsedMatch ~~\"!\"~~' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' `ParsedMatch ~~-m~~' `ParsedMatch ~~comment~~' `ParsedMatch ~~--comment~~' `ParsedMatch ~~\"has space\"~~' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedNegatedMatch -p icmp'\n\
    \-A DOS~Pro-t_ect `ParsedNegatedMatch -p tcp' `ParsedNegatedMatch -s 131.159.0.0/16'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -i vocb' `ParsedMatch -p udp' `ParsedMatch --spts [67:68]' `ParsedMatch --dpts [67:68]' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -i vocb' `ParsedMatch -p udp' `ParsedNegatedMatch --spts [67:68]' `ParsedNegatedMatch --dpts [67:68]' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedAction -j LOG' `ParsedMatch ~~--log-prefix~~' `ParsedMatch ~~\"!#*~%&/()=?\"~~' `ParsedMatch ~~--log-level~~' `ParsedMatch ~~6~~'\n\
    \-A FORWARD `ParsedMatch -s 127.0.0.0/8' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i wlan0' `ParsedMatch -p tcp' `ParsedNegatedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' `ParsedMatch -m state --state NEW' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' `ParsedMatch --dpts [80, 443]' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch -m state --state NEW' `ParsedMatch --dpts [1:65535]' `ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state NEW,INVALID' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i wlan0' `ParsedMatch -p icmp' `ParsedMatch -m state --state NEW,ESTABLISHED,RELATED,UNTRACKED' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state NEW,UNTRACKED' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state ESTABLISHED,RELATED' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedNegatedMatch -i eth+' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -s 100.0.0.0/24' `ParsedMatch -p tcp' `ParsedAction -j DOS~Pro-t_ect (call)'\n\
    \-A FORWARD `ParsedNegatedMatch -s 131.159.0.0/16' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch --spts [80, 443]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch --dpts [80, 443]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -d 127.0.0.1/32' `ParsedMatch -o eth1.152' `ParsedMatch -p udp' `ParsedMatch --dpts [4569, 5000:65535]' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -i eth0' `ParsedMatch -p tcp' `ParsedMatch --dpts [22]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i eth0' `ParsedMatch -p tcp' `ParsedMatch --dpts [21, 873:874, 5005, 5006, 80, 548, 111, 892, 2049]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -s 192.168.0.1' `ParsedAction -j LOGDROP (call)'\n\
    \-A FORWARD `ParsedMatch -m iprange --src-range 127.0.0.1-127.0.10.0' `ParsedAction -j RETURN'\n\
    \-A FORWARD `ParsedNegatedMatch -m iprange --dst-range 127.0.0.1-127.0.10.0' `ParsedAction -j RETURN'\n\
    \-A FORWARD `ParsedAction -g Terminal'\n\
    \-A FORWARD `ParsedAction -j IPSEC_42 (call)'\n\
    \-A IPSEC_42 `ParsedMatch -p protocolid:50' `ParsedMatch -m state --state NEW' `ParsedAction -j ACCEPT'\n\
    \-A IPSEC_42 `ParsedMatch -p protocolid:47' `ParsedMatch -m state --state NEW' `ParsedAction -j ACCEPT'\n\
    \-A LOGDROP\n\
    \-A LOGDROP `ParsedAction -j DROP'\n\
    \-A Terminal `ParsedMatch -d 127.0.0.1/32' `ParsedMatch -p udp' `ParsedMatch --spts [53]' `ParsedAction -j DROP'\n\
    \-A Terminal `ParsedMatch -d 127.42.0.1/32' `ParsedAction -j REJECT'\n\
    \-A Terminal `ParsedAction -j REJECT'\n\
    \COMMIT"

test_Parser_Test_data :: IO Progress
test_Parser_Test_data = do
    let fileName = "../thy/Examples/Parser_Test/data/iptables-save"
    f <- readFile fileName
    case parseIptablesSave fileName f of
        Left err -> return $ Finished $ Fail (show err)
        Right res -> do
            --putStrLn $ show res
            --putStrLn $ expected_result
            if (show res) == expected_result then
                return $ Finished Pass
            else
                return $ Finished $ Fail "(show res) != expected_result"



-- TODO: refactor!

preprocessForSpoofingProtection = Isabelle.upper_closure . Isabelle.ctstate_assume_new

exampleCertSpoof ipassmt fuc = map (\ifce -> (ifce, Isabelle.no_spoofing_iface ifce ipassmtMap fuc)) interfaces
    where interfaces = map fst ipassmt
          ipassmtMap = Isabelle.map_of_ipassmt ipassmt


ipassmt_i8_hardcoded = "eth0 = [0.0.0.0-255.255.255.255]\n\
\foo = []\n\
\eth1.96 = [131.159.14.3/25]\n\
\eth1.108 = [131.159.14.129/26]\n\
\eth1.109 = [131.159.20.11/24]\n\
\eth1.110 = all_but_those_ips [\n\
\  131.159.14.0/23,\n\
\  131.159.20.0/23,\n\
\  192.168.212.0/23,\n\
\  188.95.233.0/24,\n\
\  188.95.232.192/27,\n\
\  188.95.234.0/23,\n\
\  192.48.107.0/24,\n\
\  188.95.236.0/22,\n\
\  185.86.232.0/22\n\
\  ]\n\
\eth1.116 = [131.159.15.131/26]\n\
\eth1.152 = [131.159.15.252/28]\n\
\eth1.171 = [131.159.15.2/26]\n\
\eth1.173 = [131.159.21.252/24]\n\
\eth1.1010 = [131.159.15.227/28]\n\
\eth1.1011 = [131.159.14.194/27]\n\
\eth1.1012 = [131.159.14.238/28]\n\
\eth1.1014 = [131.159.15.217/27]\n\
\eth1.1016 = [131.159.15.66/26]\n\
\eth1.1017 = [131.159.14.242/28]\n\
\eth1.1111 = [192.168.212.4/24]\n\
\eth1.97 = [188.95.233.2/24]\n\
\eth1.1019 = [188.95.234.2/23]\n\
\eth1.1020 = [192.48.107.2/24]\n\
\eth1.1023 = [188.95.236.2/22]\n\
\eth1.1025 = [185.86.232.2/22]\n\
\eth1.1024 = all_but_those_ips [\n\
\  131.159.14.0/23,\n\
\  131.159.20.0/23,\n\
\  192.168.212.0/23,\n\
\  188.95.233.0/24,\n\
\  188.95.232.192/27,\n\
\  188.95.234.0/23,\n\
\  192.48.107.0/24,\n\
\  188.95.236.0/22,\n\
\  185.86.232.0/22\n\
\  ]"


test_spoofing_TUM_i8 fileName expected_spoofing_result errormsg = do
    ipassmt <- case parseIpAssmt "<hardcoded>" ipassmt_i8_hardcoded of
        Left err -> do print err
                       error $ "could not parse hard-coded ipassmt"
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res
    
    f <- readFile fileName
    
    case parseIptablesSave fileName f of
        Left err -> return $ Finished $ Fail (show err)
        Right res -> do
            checkParsedTables res
            let (fw, defaultPolicies) = rulesetLookup "filter" res
            let Just policy_FORWARD = M.lookup "FORWARD" defaultPolicies
            let unfolded = Isabelle.unfold_ruleset_FORWARD (policy_FORWARD) $ Isabelle.map_of_string (Isabelle.rewrite_Goto fw)
            let fuc = preprocessForSpoofingProtection unfolded --Firewall Under Certification
            putStrLn $ "ipassmt_sanity_defined: " ++ show (Isabelle.ipassmt_sanity_defined fuc (Isabelle.map_of_ipassmt ipassmt))
            mapM_ putStrLn (Isabelle.debug_ipassmt ipassmt fuc)
            let computed_result = map (\ (iface, rslt) -> (show iface, rslt)) (exampleCertSpoof ipassmt fuc)
            putStrLn $ show computed_result
            if computed_result == expected_spoofing_result then
                return $ Finished Pass
            else
                return $ Finished $ Fail errormsg


test_spoofing_TUM_Net1 :: IO Progress
test_spoofing_TUM_Net1 = test_spoofing_TUM_i8 "../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating" expected_spoofing_result "computed_result != expected_spoofing_result (almost all interfaces should have spoofing protection)"
    where expected_spoofing_result = [  ("eth0", True)
                            , ("foo", False)
                            , ("eth1.96", True)
                            , ("eth1.108", True)
                            , ("eth1.109", True)
                            , ("eth1.110", True)
                            , ("eth1.116", True)
                            , ("eth1.152", True)
                            , ("eth1.171", True)
                            , ("eth1.173", True)
                            , ("eth1.1010", True)
                            , ("eth1.1011", True)
                            , ("eth1.1012", True)
                            , ("eth1.1014", True)
                            , ("eth1.1016", True)
                            , ("eth1.1017", True)
                            , ("eth1.1111", True)
                            , ("eth1.97", False)
                            , ("eth1.1019", True)
                            , ("eth1.1020", True)
                            , ("eth1.1023", True)
                            , ("eth1.1025", True)
                            , ("eth1.1024", True)]


test_spoofing_TUM_Net2 = test_spoofing_TUM_i8 "../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_14-14-46_cheating" expected_spoofing_result "computed_result != expected_spoofing_result (ifaces foo, 110, 97, 1024 must fail)"
    where expected_spoofing_result = [  ("eth0", True)
                            , ("foo", False)
                            , ("eth1.96", True)
                            , ("eth1.108", True)
                            , ("eth1.109", True)
                            , ("eth1.110", False)
                            , ("eth1.116", True)
                            , ("eth1.152", True)
                            , ("eth1.171", True)
                            , ("eth1.173", True)
                            , ("eth1.1010", True)
                            , ("eth1.1011", True)
                            , ("eth1.1012", True)
                            , ("eth1.1014", True)
                            , ("eth1.1016", True)
                            , ("eth1.1017", True)
                            , ("eth1.1111", True)
                            , ("eth1.97", False)
                            , ("eth1.1019", True)
                            , ("eth1.1020", True)
                            , ("eth1.1023", True)
                            , ("eth1.1025", True)
                            , ("eth1.1024", False)]


test_spoofing_TUM_Net3 = test_spoofing_TUM_i8 "../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-13_10-53-20_cheating" expected_spoofing_result "computed_result != expected_spoofing_result (only ifaces 96 and eth0 have protection)"
    where expected_spoofing_result = [  ("eth0", True)
                            , ("foo", False)
                            , ("eth1.96", True)
                            , ("eth1.108", False)
                            , ("eth1.109", False)
                            , ("eth1.110", False)
                            , ("eth1.116", False)
                            , ("eth1.152", False)
                            , ("eth1.171", False)
                            , ("eth1.173", False)
                            , ("eth1.1010", False)
                            , ("eth1.1011", False)
                            , ("eth1.1012", False)
                            , ("eth1.1014", False)
                            , ("eth1.1016", False)
                            , ("eth1.1017", False)
                            , ("eth1.1111", False)
                            , ("eth1.97", False)
                            , ("eth1.1019", False)
                            , ("eth1.1020", False)
                            , ("eth1.1023", False)
                            , ("eth1.1025", False)
                            , ("eth1.1024", False)]

test_topoS_generated_service_matrix :: IO Progress
test_topoS_generated_service_matrix = do
    f <- readFile "../thy/Examples/topoS_generated/imaginray_factory_network.iptables-save.by-linux-kernel"
    case parseIptablesSave "topoS generated Service Matrix" f of
        Left err -> return $ Finished $ Fail (show err)
        Right res -> do
            checkParsedTables res
            let (fw, defaultPolicies) = rulesetLookup "filter" res
            let Just policy_FORWARD = M.lookup "FORWARD" defaultPolicies
            let unfolded = Isabelle.unfold_ruleset_FORWARD (policy_FORWARD) $ Isabelle.map_of_string (Isabelle.rewrite_Goto fw)
            let upper_simple = (Isabelle.to_simple_firewall_without_interfaces Isabelle.ipassmt_generic unfolded)
            let service_matrix = Isabelle.access_matrix_pretty Isabelle.parts_connection_ssh upper_simple
            putStrLn $ show service_matrix
            if service_matrix == expected_result then
                return $ Finished Pass
            else
                return $ Finished $ Fail "service marix topoS_generated differs"
    where expected_result = ([("Nodes",":")
            , ("10.8.8.1","10.8.8.1")
            , ("10.8.2.2","10.8.2.2")
            , ("10.8.2.1","10.8.2.1")
            , ("10.8.1.2","10.8.1.2")
            , ("10.8.1.1","10.8.1.1")
            , ("10.8.0.1","10.8.0.1")
            , ("10.0.1.1","{10.0.1.1 .. 10.0.1.4}")
            , ("10.0.0.2","10.0.0.2")
            , ("10.0.0.1","10.0.0.1")
            , ("0.0.0.0","{0.0.0.0 .. 10.0.0.0} u {10.0.0.3 .. 10.0.1.0} u \
                 \{10.0.1.5 .. 10.8.0.0} u {10.8.0.2 .. 10.8.1.0} u \
                 \{10.8.1.3 .. 10.8.2.0} u {10.8.2.3 .. 10.8.8.0} u \
                 \{10.8.8.2 .. 255.255.255.255}")
            ],
            [("Vertices",":")
            , ("10.8.8.1","10.8.2.2")
            , ("10.8.8.1","10.8.2.1")
            , ("10.8.1.2","10.8.2.2")
            , ("10.8.1.1","10.8.2.2")
            , ("10.8.1.1","10.8.2.1")
            , ("10.8.0.1","10.8.1.2")
            , ("10.8.0.1","10.8.1.1")
            , ("10.0.1.1","10.0.0.2")
            , ("10.0.0.2","10.0.0.1")
            ])


tests :: IO [Test]
tests = return [ Test actualTest, Test serviceMatrixTopoSGenerated, Test spoofingTest1, Test spoofingTest2, Test spoofingTest3 ]
  where
    actualTest = TestInstance
        { run = test_Parser_Test_data
        , name = "test the hand-crafted iptables-save"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right actualTest
        }
    spoofingTest1 = TestInstance
        { run = test_spoofing_TUM_Net1
        , name = "test TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating spoofing"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right spoofingTest1
        }
    spoofingTest2 = TestInstance
        { run = test_spoofing_TUM_Net2
        , name = "test TUM_Net_Firewall/iptables-save-2015-05-15_14-14-46_cheating spoofing"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right spoofingTest1
        }
    spoofingTest3 = TestInstance
        { run = test_spoofing_TUM_Net3
        , name = "test TUM_Net_Firewall/iptables-save-2015-05-13_10-53-20_cheating"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right spoofingTest1
        }
    serviceMatrixTopoSGenerated = TestInstance
        { run = test_topoS_generated_service_matrix
        , name = "service matrix imaginray_factory_network.iptables-save.by-linux-kernel"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right serviceMatrixTopoSGenerated
        }
