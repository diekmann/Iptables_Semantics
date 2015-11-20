{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.IPTables.ParserHelper where

import Control.Applicative ((<$>))
import qualified Network.IPTables.Generated as Isabelle
import Text.Parsec (many1, oneOf, char, choice, string)

nat = do
    n <- (read :: String -> Integer) <$> many1 (oneOf ['0'..'9']) -- ['0'..'9']++['-']
    if n < 0
        then error ("nat `"++ show n ++ "' must be geq zero")
        else return n

natMaxval maxval = do
    n <- nat
    if n > maxval
        then error ("nat `"++ show n ++ "' must be smaller than " ++ show maxval)
        else return (Isabelle.Nat n)

ipv4dotdecimal = do
    a <- natMaxval 255
    char '.'
    b <- natMaxval 255
    char '.'
    c <- natMaxval 255
    char '.'
    d <- natMaxval 255
    return (a,(b,(c,d)))


ipv4addr = do
    ip <- ipv4dotdecimal
    return (Isabelle.Ip4Addr ip)

ipv4cidr = do
    ip <- ipv4dotdecimal
    char '/'
    netmask <- natMaxval 32
    return (Isabelle.Ip4AddrNetmask ip netmask)

ipv4range = do
    ip1 <- ipv4dotdecimal
    char '-'
    ip2 <- ipv4dotdecimal
    return (Isabelle.Ip4AddrRange ip1 ip2)
    
protocol = Isabelle.Proto <$> choice [string "tcp" >> return Isabelle.TCP
                                     ,string "udp" >> return Isabelle.UDP
                                     ,string "icmp" >> return Isabelle.ICMP
                                     ,string "esp" >> return (Isabelle.OtherProtocol (Isabelle.Nat 50))
                                     ,string "ah" >> return (Isabelle.OtherProtocol (Isabelle.Nat 51))
                                     ,string "gre" >> return (Isabelle.OtherProtocol (Isabelle.Nat 47))
                                     ]

iface = Isabelle.Iface <$> many1 (oneOf $ ['A'..'Z']++['a'..'z']++['0'..'9']++['+','*','.'])

tcpFlag = choice [string "SYN" >> return Isabelle.TCP_SYN
                 ,string "ACK" >> return Isabelle.TCP_ACK
                 ,string "FIN" >> return Isabelle.TCP_FIN
                 ,string "PSH" >> return Isabelle.TCP_PSH
                 ,string "URG" >> return Isabelle.TCP_URG
                 ,string "RST" >> return Isabelle.TCP_RST]



