{-# Language FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-tabs #-} {- I'm in a murderous mood -}

module Network.RTbl.Parser
( parseRTbl
, rTblToIsabelle) where

import           Text.Parsec
import           Data.Functor ((<$>), ($>))
import           Control.Applicative ((<*), (*>), (<$>))
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.Ruleset
import           Network.IPTables.ParserHelper
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.Generated (metric_update, routing_action_next_hop_update, routing_action_oiface_update, empty_rr_hlp)
import           Data.Maybe (catMaybes, Maybe (Just, Nothing), fromMaybe)
import           Control.Monad (void,liftM)

type Routing_rule = Isabelle.Routing_rule_ext ()
data RTbl = RTbl [Routing_rule]

parseRTbl = flip runParser () $ RTbl . Isabelle.sort_rtbl <$> many parseRTblEntry 

parseRTblEntry :: Parsec String s Routing_rule
parseRTblEntry = do
	pfx <- ipv4addrOrCidr <|> defaultParser
	skipWS
	opts <- parseOpts
	many1 (char '\n')
	return $ opts . empty_rr_hlp $ pfx
	where
		zn = Isabelle.Nat 0
		defaultParser = (Prelude.const (Isabelle.PrefixMatch (Isabelle.ipv4addr_of_dotdecimal (zn,(zn,(zn,zn)))) zn) <$> lit "default")
	
parseOpt :: Parsec String s (Routing_rule -> Routing_rule)
parseOpt = choice (map try [parseOIF, parseNH, parseMetric, ignoreScope, ignoreProto, ignoreSrc])

parseOpts :: Parsec String s (Routing_rule -> Routing_rule)
parseOpts = flip (foldl (flip id)) <$> many (parseOpt <* skipWS)

litornat l =  (void $ nat) <|> void (choice (map lit l))

ignoreScope = do
	lit "scope"
	skipWS
	litornat ["host", "link", "global"]
	return id

ignoreProto = do
	lit "proto"
	skipWS
	litornat ["kernel", "boot", "static", "dhcp"]
	return id

ignoreSrc = do
	lit "src"
	skipWS
	ipv4addr
	return id

parseOIF = do
	lit "dev"
	skipWS
	routing_action_oiface_update <$> siface

parseNH = do
	lit "via"
	skipWS
	routing_action_next_hop_update <$> ipv4dotdecimal

parseMetric = do
	lit "metric"
	skipWS
	metric_update . const . Isabelle.Nat <$> nat

rTblToIsabelle (RTbl t) = t

instance Show RTbl where
	show (RTbl t) = unlines . map show $ t
instance Show (Isabelle.Routing_rule_ext a) where 
	show (Isabelle.Routing_rule_ext pfxm (Isabelle.Nat met) (Isabelle.Routing_action_ext dev nh ()) a) = 
		unwords ([show pfxm, "dev", dev] ++ (fromMaybe [] . liftM (("via" :) . (: []) . Isabelle.ipv4addr_toString) $ nh) ++ ["metric", show met]) 

{- now, for some code duplication, because that's how its done in Ipassmt and IPTables parser -}
skipWS = void $ many $ oneOf " \t"
lit str = (string str)
ipv4addrOrCidr = try (Isabelle.PrefixMatch <$> (ipv4dotdecimal <* char '/') <*> (Isabelle.Nat <$> nat)) 
             <|> try (flip Isabelle.PrefixMatch (Isabelle.Nat 32) <$> ipv4dotdecimal)
siface = many1 (oneOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['+', '*', '.'])
