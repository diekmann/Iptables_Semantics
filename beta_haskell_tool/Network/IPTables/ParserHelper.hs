{-# LANGUAGE NoMonomorphismRestriction #-}
module Network.IPTables.ParserHelper where


import Control.Applicative ((<$>))
import Text.Parsec (many1, oneOf, char, choice, string)

import qualified Network.IPTables.Generated as Isabelle

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
                                     ]

iface = Isabelle.Iface <$> many1 (oneOf $ ['A'..'Z']++['a'..'z']++['0'..'9']++['+','*','.'])

