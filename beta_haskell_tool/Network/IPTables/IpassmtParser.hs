{-# LANGUAGE NoMonomorphismRestriction #-}
module IpassmtParser where

import qualified Data.Map as M
import           Text.Parsec hiding (token)
import           Control.Applicative ((<$>),(<*>),(<*),(*>))
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.ParserHelper
import           Network.IPTables.IsabelleToString()

data IpRange = IpRange [Isabelle.Ipt_ipv4range]

type IpAssmt = M.Map Isabelle.Iface IpRange

ifconfig = many (skipWS *> ipAssmt <* skipWS)

ipAssmt = do
  ifce <- iface
  skipWS *> char '=' <* skipWS
  rng <- ipRange
  return (ifce, rng)

ipRange = enclosedList '[' ips ']'
    where ips = choice [try ipv4cidr, try ipv4range, try ipv4addr]

enclosedList left parser right = between (char left <* skipWS) (char right) $
              (parser <* skipWS) `sepBy` (char ',' <* skipWS)

skipWS = many $ oneOf " \t\n"
