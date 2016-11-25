{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.IPTables.ParserHelper where

import           Data.Functor ((<$>), ($>))
import Network.IPTables.IsabelleToString (Word32, Word128)
import Data.List.Split (splitOn)
import qualified Network.IPTables.Generated as Isabelle
import           Text.Parsec (char, choice, many, many1, Parsec, oneOf, noneOf, string, (<|>), try)


quotedString = do
    a <- string "\""
    b <- concat <$> many quotedChar
    c <- string "\""
    return (a ++ b ++ c)
    where quotedChar = try (string "\\\\") <|> try (string "\\\"") <|> ((noneOf "\"\n") >>= \x -> return [x] )
              
nat :: Parsec String s Integer
nat = do
    n <- read <$> many1 (oneOf ['0'..'9'])
    if n < 0 then
        error ("nat `" ++ show n ++ "' must be greater than or equal to zero")
    else
        return n

natMaxval :: Integer -> Parsec String s Isabelle.Nat
natMaxval maxval = do
    n <- nat
    if n > maxval then
        error ("nat `" ++ show n ++ "' must be smaller than or equal to " ++ show maxval)
    else
        return (Isabelle.nat_of_integer n)

ipv4dotdecimal :: Parsec String s (Isabelle.Word Word32)
ipv4dotdecimal = do
    a <- natMaxval 255
    char '.'
    b <- natMaxval 255
    char '.'
    c <- natMaxval 255
    char '.'
    d <- natMaxval 255
    return $ ipv4word (a, (b, (c, d)))
    where ipv4word :: (Isabelle.Nat, (Isabelle.Nat, (Isabelle.Nat, Isabelle.Nat))) -> Isabelle.Word Word32
          ipv4word = Isabelle.ipv4addr_of_dotdecimal

ipv4addr :: Parsec String s (Isabelle.Ipt_iprange Word32)
ipv4addr = Isabelle.IpAddr <$> ipv4dotdecimal

ipv4cidr :: Parsec String s (Isabelle.Ipt_iprange Word32)
ipv4cidr = do
    ip <- ipv4dotdecimal
    char '/'
    netmask <- natMaxval 32
    return $ Isabelle.IpAddrNetmask ip netmask

ipv4range :: Parsec String s (Isabelle.Ipt_iprange Word32)
ipv4range = do
    ip1 <- ipv4dotdecimal
    char '-'
    ip2 <- ipv4dotdecimal
    return $ Isabelle.IpAddrRange ip1 ip2


ipv6colonsep :: Parsec String s (Isabelle.Word Word128)
ipv6colonsep = do 
    ipv6string <- many1 (oneOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ [':'])
    let ipv6parts = map option_int $ splitOn ":" ipv6string
    let parsed = case Isabelle.mk_ipv6addr ipv6parts
                       of Nothing -> error $ "invalid IPv6 address: " ++ ipv6string
                          Just x -> Isabelle.ipv6preferred_to_int x
    return parsed
    where option_int "" = Nothing
          option_int i  = Just (Isabelle.integer_to_16word (readHex i))
          readHex :: String -> Integer
          readHex x = read ("0x" ++ x)

ipv6addr :: Parsec String s (Isabelle.Ipt_iprange Word128)
ipv6addr = Isabelle.IpAddr <$> ipv6colonsep

ipv6cidr :: Parsec String s (Isabelle.Ipt_iprange Word128)
ipv6cidr = do
    ip <- ipv6colonsep
    char '/'
    netmask <- natMaxval 128
    return $ Isabelle.IpAddrNetmask ip netmask

ipv6range :: Parsec String s (Isabelle.Ipt_iprange Word128)
ipv6range = do
    ip1 <- ipv6colonsep
    char '-'
    ip2 <- ipv6colonsep
    return $ Isabelle.IpAddrRange ip1 ip2

protocol :: Parsec String s Isabelle.Protocol
protocol = choice (map make ps)
    where make (s, p) = try (string s) $> Isabelle.Proto p
          ps = [ ("tcp",       Isabelle.tcp)
               , ("udp",       Isabelle.udp)
               , ("icmpv6",    Isabelle.iPv6ICMP)
               , ("ipv6-icmp", Isabelle.iPv6ICMP)
               , ("icmp",      Isabelle.icmp)
               , ("esp",       Isabelle.esp)
               , ("ah",        Isabelle.ah)
               , ("gre",       Isabelle.gre)
               ]

iface :: Parsec String s Isabelle.Iface
iface = Isabelle.Iface <$> many1 (oneOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['+', '*', '.', '-'])

tcpFlag :: Parsec String s Isabelle.Tcp_flag
tcpFlag = choice $ map make ps
    where make (s, p) = string s $> p
          ps = [ ("SYN", Isabelle.TCP_SYN)
               , ("ACK", Isabelle.TCP_ACK)
               , ("FIN", Isabelle.TCP_FIN)
               , ("PSH", Isabelle.TCP_PSH)
               , ("URG", Isabelle.TCP_URG)
               , ("RST", Isabelle.TCP_RST)
               ]
