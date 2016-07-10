module Suites.ParserHelper ( tests ) where

--import Data.Functor
--import Network.IPTables.Ruleset
--import Network.IPTables.Parser
--import Network.IPTables.IpassmtParser
import qualified Network.IPTables.ParserHelper
import qualified Network.IPTables.Generated as Isabelle
import           Text.Parsec hiding (token)
import Test.Tasty
import Test.Tasty.HUnit as HU




test_parse_show_identiy parser str = HU.testCase ("ParserHelper: parse show identity ("++str++")") $ do
    let result = case runParser eofParser () "<test data>" str
                of Left err -> do error $ show err
                   Right result -> show result
    result @?= str
    where eofParser =
            do v <- parser
               eof
               return v

test_parse_quotedstring str = HU.testCase ("ParserHelper: quoted string (`"++str++"')") $ do
    let result = case runParser eofParser () "<test data>" str
                of Left err -> do error $ show err
                   Right result -> result
    result @?= str
    where eofParser =
            do v <- Network.IPTables.ParserHelper.quotedString
               eof
               return v
                   
--TODO negative tests!

tests = testGroup "ParserHelper Unit tests" $
  [ test_parse_show_identiy Network.IPTables.ParserHelper.ipv4addr "192.168.0.1"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv4cidr "192.168.0.1/24"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv4range "192.168.0.1-192.168.0.255"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6cidr "::/64"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6range "::-::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "2001:db8::8:800:200c:417a"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "ff01::101"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "::8:800:200c:417a"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "2001:db8::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "ff00::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "fe80::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "::"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "::1"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv6addr "2001:db8::1"
  , test_parse_quotedstring "\"foo\""
  , test_parse_quotedstring "\"foo with some \\\" escaped quote \""
  , test_parse_quotedstring "\"foo with some escaped escape (\\\\) and proper ending quote \\\\\""
  , test_parse_quotedstring "\"asd ' adsa \v \\v \\\v \\\\v sad \\' asd \' \\\' \\\\' sa\""
  ]
