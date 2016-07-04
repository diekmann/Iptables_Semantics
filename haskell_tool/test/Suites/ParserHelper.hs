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


--TODO negative tests?

tests = testGroup "ParserHelper Unit tests" $
  [ test_parse_show_identiy Network.IPTables.ParserHelper.ipv4addr "192.168.0.1"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv4cidr "192.168.0.1/24"
  , test_parse_show_identiy Network.IPTables.ParserHelper.ipv4range "192.168.0.1-192.168.0.255"
  ]
