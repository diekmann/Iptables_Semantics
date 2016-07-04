module Network.IPTables.IpassmtParser
( parseIpAssmt
, IpAssmt
, IsabelleIpAssmt
, ipAssmtToIsabelle) where

import           Text.Parsec hiding (token)
import           Data.Functor ((<$>), ($>))
import           Control.Applicative ((<*), (*>))
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.ParserHelper
import           Network.IPTables.IsabelleToString(Word32)

type IpRange = Isabelle.Negation_type [Isabelle.Ipt_iprange Word32]

data IpAssmt =  IpAssmt [(Isabelle.Iface, IpRange)] deriving (Show)


type IsabelleIPv4AddrWord = Isabelle.Word Word32
type IsabelleIpAssmt = [(Isabelle.Iface, [(IsabelleIPv4AddrWord, Isabelle.Nat)])]

ipAssmtToIsabelle:: IpAssmt -> IsabelleIpAssmt
ipAssmtToIsabelle (IpAssmt assmt) = Isabelle.to_ipassmt assmt

parseIpAssmt :: SourceName -> String -> Either ParseError IpAssmt
parseIpAssmt = runParser ifconfig ()

ifconfig :: Parsec String s IpAssmt
ifconfig = IpAssmt <$> many (skipWS *> ipAssmt <* skipWS)

ipAssmt :: Parsec String s (Isabelle.Iface, IpRange)
ipAssmt = do
    ifce <- iface
    skipWS *> char '=' <* skipWS
    rng <- choice [try neg, try pos]
    return (ifce, rng)
        where pos = do rng <- ipRange
                       return (Isabelle.Pos rng)
              neg = do skipWS *> string "all_but_those_ips" <* skipWS
                       rng <- ipRange
                       return (Isabelle.Neg rng)

ipRange :: Parsec String s [Isabelle.Ipt_iprange Word32]
ipRange = enclosedList '[' ips ']'
    where ips = choice [try ipv4cidr, try ipv4range, try ipv4addr]

enclosedList :: Char -> Parsec String s a -> Char -> Parsec String s [a]
enclosedList left parser right = between (char left <* skipWS) (char right) $ (parser <* skipWS) `sepBy` (char ',' <* skipWS)

skipWS :: Parsec String s ()
skipWS = (many $ oneOf " \t\n") $> ()
