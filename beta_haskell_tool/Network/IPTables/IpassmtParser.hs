{-# LANGUAGE NoMonomorphismRestriction #-}
module IpassmtParser where

import           Text.Parsec hiding (token)
import           Control.Applicative ((<$>),(<*),(*>))
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.ParserHelper
import           Network.IPTables.IsabelleToString()

type IpRange = Isabelle.Negation_type [Isabelle.Ipt_ipv4range]

data IpAssmt =  IpAssmt [(Isabelle.Iface, IpRange)] deriving (Show)

ipAssmtToIsabelle (IpAssmt assmt) = Isabelle.to_ipassmt assmt

ifconfig = IpAssmt <$> many (skipWS *> ipAssmt <* skipWS)

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

ipRange = enclosedList '[' ips ']'
    where ips = choice [try ipv4cidr, try ipv4range, try ipv4addr]

enclosedList left parser right = between (char left <* skipWS) (char right) $
              (parser <* skipWS) `sepBy` (char ',' <* skipWS)

skipWS = many $ oneOf " \t\n"
