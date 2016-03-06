module ParserTestSuite ( tests ) where

import Distribution.TestSuite
import Network.IPTables.Ruleset
import Network.IPTables.Parser


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
            putStrLn $ show res
            putStrLn $ expected_result
            if (show res) == expected_result then
                return $ Finished Pass
            else
                return $ Finished $ Fail "(show res) != expected_result"

tests :: IO [Test]
tests = return [ Test actualTest ]
  where
    actualTest = TestInstance
        { run = test_Parser_Test_data
        , name = "test the hand-crafted iptables-save"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right actualTest
        }
