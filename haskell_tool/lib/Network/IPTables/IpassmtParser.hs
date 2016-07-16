module Network.IPTables.IpassmtParser
( parseIpAssmt_ipv4
, parseIpAssmt_ipv6
, IpAssmt
, IsabelleIpAssmt
, ipAssmtToIsabelle) where

import           Text.Parsec hiding (token)
import           Data.Functor ((<$>), ($>))
import           Control.Applicative ((<*), (*>))
import           Network.IPTables.Ipassmt
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.ParserHelper
import           Network.IPTables.IsabelleToString (Word32, Word128)

ipAssmtToIsabelle :: Isabelle.Len a => IpAssmt a -> IsabelleIpAssmt a
ipAssmtToIsabelle (IpAssmt assmt) = Isabelle.to_ipassmt assmt

-- returns IpAssmt instead of IsabelleIpAssmt because we can only show the former (nicely. TODO change this)
parseIpAssmt_ipv4 :: SourceName -> String -> Either ParseError (IpAssmt Word32)
parseIpAssmt_ipv4 = runParser (ifconfig_generic ipAssmt_ipv4) ()

parseIpAssmt_ipv6 :: SourceName -> String -> Either ParseError (IpAssmt Word128)
parseIpAssmt_ipv6 = runParser (ifconfig_generic ipAssmt_ipv6) ()

ifconfig_generic
    :: Parsec String s (Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])
        -> Parsec String s (IpAssmt a)
ifconfig_generic ipAssmt_parser = IpAssmt <$> many (skipWS *> ipAssmt_parser <* skipWS)


ipAssmt_ipv4 = ipAssmt_generic ipRange_ipv4
ipAssmt_ipv6 = ipAssmt_generic ipRange_ipv6

ipAssmt_generic
    :: Parsec String s [Isabelle.Ipt_iprange a]
        -> Parsec String s (Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])
ipAssmt_generic ipRange_parser = do
    ifce <- iface
    skipWS *> char '=' <* skipWS
    rng <- choice [try neg, try pos]
    return (ifce, rng)
        where pos = do rng <- ipRange_parser 
                       return (Isabelle.Pos rng)
              neg = do skipWS *> string "all_but_those_ips" <* skipWS
                       rng <- ipRange_parser 
                       return (Isabelle.Neg rng)

ipRange_ipv4 :: Parsec String s [Isabelle.Ipt_iprange Word32]
ipRange_ipv4 = enclosedList '[' ips ']'
    where ips = choice [try ipv4cidr, try ipv4range, try ipv4addr]

ipRange_ipv6 :: Parsec String s [Isabelle.Ipt_iprange Word128]
ipRange_ipv6 = enclosedList '[' ips ']'
    where ips = choice [try ipv6cidr, try ipv6range, try ipv6addr]

enclosedList :: Char -> Parsec String s a -> Char -> Parsec String s [a]
enclosedList left parser right = between (char left <* skipWS) (char right) $ (parser <* skipWS) `sepBy` (char ',' <* skipWS)

skipWS :: Parsec String s ()
skipWS = (many $ oneOf " \t\n") $> ()
