{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.IPTables.ParserHelper where

import           Data.Functor ((<$>), ($>))
import qualified Network.IPTables.Generated as Isabelle
import           Text.Parsec (char, choice, many1, Parsec, oneOf, string)

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
        return (Isabelle.Nat n)

ipv4dotdecimal :: Parsec String s (Isabelle.Nat, (Isabelle.Nat, (Isabelle.Nat, Isabelle.Nat)))
ipv4dotdecimal = do
    a <- natMaxval 255
    char '.'
    b <- natMaxval 255
    char '.'
    c <- natMaxval 255
    char '.'
    d <- natMaxval 255
    return (a, (b, (c, d)))

ipv4addr :: Parsec String s Isabelle.Ipt_ipv4range
ipv4addr = Isabelle.Ip4Addr <$> ipv4dotdecimal

ipv4cidr :: Parsec String s Isabelle.Ipt_ipv4range
ipv4cidr = do
    ip <- ipv4dotdecimal
    char '/'
    netmask <- natMaxval 32
    return $ Isabelle.Ip4AddrNetmask ip netmask

ipv4range :: Parsec String s Isabelle.Ipt_ipv4range
ipv4range = do
    ip1 <- ipv4dotdecimal
    char '-'
    ip2 <- ipv4dotdecimal
    return $ Isabelle.Ip4AddrRange ip1 ip2

protocol :: Parsec String s Isabelle.Protocol
protocol = choice (map make ps)
    where make (s, p) = string s $> Isabelle.Proto p
          ps = [ ("tcp",  Isabelle.TCP)
               , ("udp",  Isabelle.UDP)
               , ("icmp", Isabelle.ICMP)
               , ("esp",  Isabelle.OtherProtocol (Isabelle.Nat 50))
               , ("ah",   Isabelle.OtherProtocol (Isabelle.Nat 51))
               , ("gre",  Isabelle.OtherProtocol (Isabelle.Nat 47))
               ]

iface :: Parsec String s Isabelle.Iface
iface = Isabelle.Iface <$> many1 (oneOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['+', '*', '.'])

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
