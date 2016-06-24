module Suites.Parser ( tests ) where

import Data.Functor
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import qualified Network.IPTables.Generated as Isabelle
import Network.IPTables.Analysis as Analysis
import Test.Tasty
import Test.Tasty.HUnit as HU


expected_result = "*filter\n\
    \:DOS~Pro-t_ect - [0:0]\n\
    \:FORWARD DROP [0:0]\n\
    \:INPUT ACCEPT [1101:228112]\n\
    \:IPSEC_42 - [0:0]\n\
    \:LOGDROP - [0:0]\n\
    \:OUTPUT ACCEPT [70:23175]\n\
    \:Terminal - [0:0]\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p tcp' `ParsedMatch --dpts [22]' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p tcp' `ParsedMatch -m state --state NEW' \
        \`ParsedMatch --dpts [1:65535]' \
        \`ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' \
        \`ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p udp' `ParsedAction -j RETURN'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' \
        \`ParsedMatch ~~-m~~' `ParsedMatch ~~icmp~~' \
        \`ParsedMatch ~~--icmp-type~~' \
        \`ParsedMatch ~~3/4~~' \
        \`ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' \
        \`ParsedMatch ~~-m~~' \
        \`ParsedMatch ~~comment~~' \
        \`ParsedMatch ~~--comment~~' \
        \`ParsedMatch ~~\"!\"~~' \
        \`ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' \
        \`ParsedMatch ~~-m~~' \
        \`ParsedMatch ~~comment~~' \
        \`ParsedMatch ~~--comment~~' \
        \`ParsedMatch ~~\"has space\"~~' \
        \`ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -p icmp' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedNegatedMatch -p icmp'\n\
    \-A DOS~Pro-t_ect `ParsedNegatedMatch -p tcp' `ParsedNegatedMatch -s 131.159.0.0/16'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -i vocb' `ParsedMatch -p udp' `ParsedMatch --spts [67:68]' `ParsedMatch --dpts [67:68]' `ParsedAction -j ACCEPT'\n\
    \-A DOS~Pro-t_ect `ParsedMatch -i vocb' `ParsedMatch -p udp' `ParsedNegatedMatch --spts [67:68]' `ParsedNegatedMatch --dpts [67:68]' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedAction -j LOG' `ParsedMatch ~~--log-prefix~~' `ParsedMatch ~~\"!#*~%&/()=?\"~~' `ParsedMatch ~~--log-level~~' `ParsedMatch ~~6~~'\n\
    \-A FORWARD `ParsedMatch -s 127.0.0.0/8' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i wlan0' \
        \`ParsedMatch -p tcp' \
        \`ParsedNegatedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' \
        \`ParsedMatch -m state --state NEW' \
        \`ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' \
        \`ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' \
        \`ParsedMatch --dpts [80, 443]' \
        \`ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -p tcp' \
        \`ParsedMatch -m state --state NEW' \
        \`ParsedMatch --dpts [1:65535]' \
        \`ParsedMatch --tcp-flags [TCP_SYN, TCP_ACK, TCP_FIN, TCP_RST] [TCP_SYN]' \
        \`ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state NEW,INVALID' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i wlan0' \
        \`ParsedMatch -p icmp' \
        \`ParsedMatch -m state --state NEW,ESTABLISHED,RELATED,UNTRACKED' \
        \`ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state NEW,UNTRACKED' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -m state --state ESTABLISHED,RELATED' `ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedNegatedMatch -i eth+' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -s 100.0.0.0/24' `ParsedMatch -p tcp' `ParsedAction -j DOS~Pro-t_ect (call)'\n\
    \-A FORWARD `ParsedNegatedMatch -s 131.159.0.0/16' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch --spts [80, 443]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -p tcp' `ParsedMatch --dpts [80, 443]' `ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -d 127.0.0.1/32' \
        \`ParsedMatch -o eth1.152' `ParsedMatch -p udp' \
        \`ParsedMatch --dpts [4569, 5000:65535]' \
        \`ParsedAction -j ACCEPT'\n\
    \-A FORWARD `ParsedMatch -i eth0' \
        \`ParsedMatch -p tcp' \
        \`ParsedMatch --dpts [22]' \
        \`ParsedAction -j DROP'\n\
    \-A FORWARD `ParsedMatch -i eth0' \
        \`ParsedMatch -p tcp' \
        \`ParsedMatch --dpts [21, 873:874, 5005, 5006, 80, 548, 111, 892, 2049]' \
        \`ParsedAction -j DROP'\n\
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

test_parser_test_data = HU.testCase "parser_test_data" $ do
    let fileName = "../thy/Iptables_Semantics/Examples/Parser_Test/data/iptables-save"
    f <- readFile fileName
    let result = show <$> parseIptablesSave fileName f
    result @?= Right expected_result

test_spoofing_certification table chain ipassmtString fileName expected_spoofing_result errormsg = do
    ipassmt <- case parseIpAssmt "<hardcoded>" ipassmtString of
        Left err -> do print err
                       error "could not parse hard-coded ipassmt"
        Right res -> return $ ipAssmtToIsabelle res
    
    f <- readFile fileName
    
    case parseIptablesSave fileName f of
        Left err -> error $ show err
        Right res -> do
            unfolded <- loadUnfoldedRuleset False table chain res
            let (warnings, spoofResult) = certifySpoofingProtection ipassmt unfolded
            --mapM_ putStrLn warnings
            let computed_result = map (\ (iface, rslt) -> (show iface, rslt)) spoofResult
            --putStrLn $ show computed_result
            if computed_result == expected_spoofing_result then
                return ()
            else
                error errormsg

test_spoofing_SQRL = HU.testCase "spoofing_SQRL" $ test_spoofing_certification "raw" "PREROUTING" ipassmt_sqrl_hardcoded rulesetFile expected_spoofing_result "SQRL Spoofing 2015 failed"
    where rulesetFile = "../thy/Iptables_Semantics/Examples/SQRL_Shorewall/2015_aug_iptables-save-spoofing-protection"
          expected_spoofing_result = [("ldit", True)
                                     , ("lmd", True)
                                     , ("loben", True)
                                     , ("wg", True)
                                     , ("wt", True)
                                     , ("lup", True)
                                     , ("lo", True)
                                     , ("vpriv", True)
                                     , ("vshit", True)
                                     , ("vocb", True)
                                     , ("lua", True)]
          ipassmt_sqrl_hardcoded = "ldit = [10.13.42.136/29]\n\
                                    \lmd = [10.13.42.128/29]\n\
                                    \loben = [10.13.42.144/28]\n\
                                    \wg = [10.13.42.176/28]\n\
                                    \wt = [10.13.42.160/28]\n\
                                    \lup = all_but_those_ips [\n\
                                    \    192.168.0.0/16,\n\
                                    \    172.16.0.0/12,\n\
                                    \    10.0.0.0/8\n\
                                    \]\n\
                                    \lo = [0.0.0.0/0]\n\
                                    \vpriv = [0.0.0.0/0]\n\
                                    \vshit = [0.0.0.0/0]\n\
                                    \vocb = [0.0.0.0/0]\n\
                                    \lua = [0.0.0.0/0]"


test_spoofing_TUM_i8 = test_spoofing_certification "filter" "FORWARD" ipassmt_i8_hardcoded


ipassmt_i8_hardcoded  = "eth0 = [0.0.0.0-255.255.255.255]\n\
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


test_spoofing_TUM_Net1 = HU.testCase "spoofing_TUM_Net1" $ test_spoofing_TUM_i8 rulesetFile expected_spoofing_result "computed_result != expected_spoofing_result (almost all interfaces should have spoofing protection)"
    where rulesetFile = "../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating" 
          expected_spoofing_result = [  ("eth0", True)
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


test_spoofing_TUM_Net2 = HU.testCase "spoofing_TUM_Net2" $ test_spoofing_TUM_i8 rulesetFile expected_spoofing_result "computed_result != expected_spoofing_result (ifaces foo, 110, 97, 1024 must fail)"
    where rulesetFile = "../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_14-14-46_cheating" 
          expected_spoofing_result = [  ("eth0", True)
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


test_spoofing_TUM_Net3 = HU.testCase "spoofing_TUM_Net3" $ test_spoofing_TUM_i8 rulesetFile expected_spoofing_result "computed_result != expected_spoofing_result (only ifaces 96 and eth0 have protection)"
    where rulesetFile = "../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-13_10-53-20_cheating"
          expected_spoofing_result = [  ("eth0", True)
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

test_service_matrix ipassmtMaybeString fileName expected_result errormsg = do 
    ipassmt <- case ipassmtMaybeString of
        Nothing -> return Isabelle.ipassmt_generic
        Just ipassmtString -> case parseIpAssmt "<hardcoded>" ipassmtString of
            Left err -> do print err
                           error "could not parse hard-coded ipassmt"
            Right res -> return $ ipAssmtToIsabelle res
    f <- readFile fileName
    case parseIptablesSave ("file: "++fileName) f of
        Left err -> error $ show err
        Right res -> do
            unfolded <- loadUnfoldedRuleset False "filter" "FORWARD" res
            let service_matrix = Analysis.accessMatrix ipassmt unfolded 10000 22
            --putStrLn $ show service_matrix
            if service_matrix == expected_result then
                return ()
            else
                error errormsg


test_topoS_generated_service_matrix = HU.testCase "test_topoS_generated_service_matrix" $ test_service_matrix Nothing rulesetFile expected_result errormsg
    where rulesetFile = "../thy/Iptables_Semantics/Examples/topoS_generated/imaginray_factory_network.iptables-save.by-linux-kernel"
          errormsg = "service marix topoS_generated differs"
          expected_result = ([
              ("10.8.8.1","10.8.8.1")
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
            [ ("10.8.8.1","10.8.2.2")
            , ("10.8.8.1","10.8.2.1")
            , ("10.8.1.2","10.8.2.2")
            , ("10.8.1.1","10.8.2.2")
            , ("10.8.1.1","10.8.2.1")
            , ("10.8.0.1","10.8.1.2")
            , ("10.8.0.1","10.8.1.1")
            , ("10.0.1.1","10.0.0.2")
            , ("10.0.0.2","10.0.0.1")
            ])

test_i8_2015_service_matrix = HU.testCase "test_i8_2015_service_matrix" $ test_service_matrix (Just ipassmt_i8_hardcoded) rulesetFile expected_result errormsg
    where rulesetFile = "../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating"
          errormsg = "service marix i8 iptables-save-2015-05-15_15-23-41_cheating differs"
          expected_result = ([
                              ("224.0.0.0", "{224.0.0.0 .. 239.255.255.255}")
                            , ("0.0.0.0", "{0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 131.158.255.255} u {131.160.0.0 .. 138.246.253.4} u {138.246.253.6 .. 185.86.231.255} u {185.86.236.0 .. 188.1.239.85} u {188.1.239.87 .. 188.95.232.63} u {188.95.232.224 .. 188.95.232.255} u {188.95.240.0 .. 192.48.106.255} u {192.48.108.0 .. 223.255.255.255} u {240.0.0.0 .. 255.255.255.255}")
                            , ("131.159.14.0", "{131.159.14.0 .. 131.159.14.7} u {131.159.14.12 .. 131.159.14.21} u {131.159.14.23 .. 131.159.14.25} u 131.159.14.27 u {131.159.14.29 .. 131.159.14.33} u {131.159.14.38 .. 131.159.14.39} u 131.159.14.41 u {131.159.14.43 .. 131.159.14.51} u {131.159.14.53 .. 131.159.14.55} u 131.159.14.57 u {131.159.14.59 .. 131.159.14.68} u {131.159.14.70 .. 131.159.14.82} u {131.159.14.84 .. 131.159.14.90} u {131.159.14.92 .. 131.159.14.103} u {131.159.14.105 .. 131.159.14.110} u {131.159.14.112 .. 131.159.14.121} u {131.159.14.123 .. 131.159.14.124} u {131.159.14.126 .. 131.159.14.136} u {131.159.14.138 .. 131.159.14.139} u {131.159.14.141 .. 131.159.14.144} u {131.159.14.147 .. 131.159.14.154} u {131.159.14.157 .. 131.159.14.162} u {131.159.14.164 .. 131.159.14.168} u {131.159.14.170 .. 131.159.14.200} u {131.159.14.202 .. 131.159.14.213} u {131.159.14.215 .. 131.159.15.3} u 131.159.15.6 u 131.159.15.10 u {131.159.15.14 .. 131.159.15.15} u {131.159.15.21 .. 131.159.15.22} u 131.159.15.24 u 131.159.15.26 u 131.159.15.28 u {131.159.15.30 .. 131.159.15.31} u {131.159.15.33 .. 131.159.15.35} u {131.159.15.37 .. 131.159.15.38} u {131.159.15.40 .. 131.159.15.41} u 131.159.15.46 u {131.159.15.49 .. 131.159.15.53} u 131.159.15.55 u 131.159.15.57 u 131.159.15.59 u {131.159.15.61 .. 131.159.15.68} u {131.159.15.70 .. 131.159.15.196} u {131.159.15.198 .. 131.159.15.227} u {131.159.15.229 .. 131.159.15.233} u {131.159.15.235 .. 131.159.15.246} u {131.159.15.250 .. 131.159.15.255} u {131.159.20.0 .. 131.159.20.20} u {131.159.20.22 .. 131.159.20.28} u {131.159.20.31 .. 131.159.20.35} u {131.159.20.37 .. 131.159.20.44} u {131.159.20.46 .. 131.159.20.51} u {131.159.20.53 .. 131.159.20.58} u {131.159.20.60 .. 131.159.20.62} u {131.159.20.64 .. 131.159.20.70} u {131.159.20.72 .. 131.159.20.73} u {131.159.20.75 .. 131.159.20.84} u 131.159.20.86 u {131.159.20.88 .. 131.159.20.96} u {131.159.20.98 .. 131.159.20.117} u 131.159.20.119 u {131.159.20.121 .. 131.159.20.123} u {131.159.20.125 .. 131.159.20.138} u {131.159.20.140 .. 131.159.20.149} u {131.159.20.152 .. 131.159.20.154} u {131.159.20.156 .. 131.159.20.158} u {131.159.20.161 .. 131.159.20.164} u {131.159.20.167 .. 131.159.20.179} u {131.159.20.181 .. 131.159.20.184} u {131.159.20.186 .. 131.159.20.232} u {131.159.20.234 .. 131.159.20.255} u {185.86.232.0 .. 185.86.235.255} u {188.95.233.0 .. 188.95.233.3} u {188.95.233.5 .. 188.95.233.8} u {188.95.233.10 .. 188.95.233.255} u {192.48.107.0 .. 192.48.107.255}")
                            , ("131.159.14.8", "{131.159.14.8 .. 131.159.14.11} u 131.159.14.22 u 131.159.14.26 u 131.159.14.28 u {131.159.14.34 .. 131.159.14.37} u 131.159.14.40 u 131.159.14.42 u 131.159.14.52 u 131.159.14.56 u 131.159.14.58 u 131.159.14.69 u 131.159.14.83 u 131.159.14.91 u 131.159.14.104 u 131.159.14.111 u 131.159.14.122 u 131.159.14.125 u 131.159.14.137 u 131.159.14.140 u {131.159.14.145 .. 131.159.14.146} u {131.159.14.155 .. 131.159.14.156} u 131.159.14.163 u 131.159.14.169 u 131.159.14.201 u 131.159.14.214 u {131.159.15.4 .. 131.159.15.5} u {131.159.15.7 .. 131.159.15.9} u {131.159.15.11 .. 131.159.15.13} u {131.159.15.16 .. 131.159.15.20} u 131.159.15.23 u 131.159.15.25 u 131.159.15.27 u 131.159.15.29 u 131.159.15.32 u 131.159.15.36 u 131.159.15.39 u {131.159.15.42 .. 131.159.15.45} u {131.159.15.47 .. 131.159.15.48} u 131.159.15.56 u 131.159.15.58 u 131.159.15.60 u 131.159.15.69 u 131.159.15.197 u 131.159.15.228 u 131.159.15.234 u {131.159.15.247 .. 131.159.15.249} u 131.159.20.21 u {131.159.20.29 .. 131.159.20.30} u 131.159.20.36 u 131.159.20.45 u 131.159.20.52 u 131.159.20.59 u 131.159.20.63 u 131.159.20.71 u 131.159.20.74 u 131.159.20.85 u 131.159.20.87 u 131.159.20.97 u 131.159.20.118 u 131.159.20.120 u 131.159.20.124 u 131.159.20.139 u {131.159.20.150 .. 131.159.20.151} u 131.159.20.155 u {131.159.20.159 .. 131.159.20.160} u {131.159.20.165 .. 131.159.20.166} u 131.159.20.180 u 131.159.20.185 u 131.159.20.233 u {131.159.21.0 .. 131.159.21.255} u {188.95.232.192 .. 188.95.232.223} u 188.95.233.4 u 188.95.233.9 u {188.95.234.0 .. 188.95.239.255}")
                            , ("188.1.239.86", "188.1.239.86 u {188.95.232.64 .. 188.95.232.191}")
                            , ("138.246.253.5", "138.246.253.5")
                            , ("131.159.0.0", "{131.159.0.0 .. 131.159.13.255} u {131.159.16.0 .. 131.159.19.255} u {131.159.22.0 .. 131.159.255.255}")
                            , ("131.159.15.54", "131.159.15.54")
                            , ("127.0.0.0", "{127.0.0.0 .. 127.255.255.255}")
                            ],
                            [ ("224.0.0.0","224.0.0.0")
                            , ("224.0.0.0","131.159.14.8")
                            , ("0.0.0.0","224.0.0.0")
                            , ("0.0.0.0","131.159.14.8")
                            , ("131.159.14.0","224.0.0.0")
                            , ("131.159.14.0","0.0.0.0")
                            , ("131.159.14.0","131.159.14.0")
                            , ("131.159.14.0","131.159.14.8")
                            , ("131.159.14.0","188.1.239.86")
                            , ("131.159.14.0","138.246.253.5")
                            , ("131.159.14.0","131.159.0.0")
                            , ("131.159.14.0","131.159.15.54")
                            , ("131.159.14.0","127.0.0.0")
                            , ("131.159.14.8","224.0.0.0")
                            , ("131.159.14.8","0.0.0.0")
                            , ("131.159.14.8","131.159.14.0")
                            , ("131.159.14.8","131.159.14.8")
                            , ("131.159.14.8","188.1.239.86")
                            , ("131.159.14.8","138.246.253.5")
                            , ("131.159.14.8","131.159.0.0")
                            , ("131.159.14.8","131.159.15.54")
                            , ("131.159.14.8","127.0.0.0")
                            , ("188.1.239.86","224.0.0.0")
                            , ("188.1.239.86","0.0.0.0")
                            , ("188.1.239.86","131.159.14.0")
                            , ("188.1.239.86","131.159.14.8")
                            , ("188.1.239.86","188.1.239.86")
                            , ("188.1.239.86","138.246.253.5")
                            , ("188.1.239.86","131.159.0.0")
                            , ("188.1.239.86","131.159.15.54")
                            , ("188.1.239.86","127.0.0.0")
                            , ("138.246.253.5","224.0.0.0")
                            , ("138.246.253.5","131.159.14.0")
                            , ("138.246.253.5","131.159.14.8")
                            , ("138.246.253.5","131.159.15.54")
                            , ("131.159.0.0","224.0.0.0")
                            , ("131.159.0.0","131.159.14.8")
                            , ("131.159.0.0","131.159.15.54")
                            , ("131.159.15.54","224.0.0.0")
                            , ("131.159.15.54","0.0.0.0")
                            , ("131.159.15.54","131.159.14.0")
                            , ("131.159.15.54","131.159.14.8")
                            , ("131.159.15.54","188.1.239.86")
                            , ("131.159.15.54","138.246.253.5")
                            , ("131.159.15.54","131.159.0.0")
                            , ("131.159.15.54","131.159.15.54")
                            , ("131.159.15.54","127.0.0.0")
                            ])

tests = testGroup "Parser and Analysis Unit tests" $
  [ test_parser_test_data
  , test_spoofing_SQRL
  , test_spoofing_TUM_Net1
  , test_spoofing_TUM_Net2
  , test_spoofing_TUM_Net3
  , test_topoS_generated_service_matrix
  , test_i8_2015_service_matrix
  ]
