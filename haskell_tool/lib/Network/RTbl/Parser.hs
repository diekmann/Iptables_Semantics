{-# Language FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-tabs #-} {- I'm in a murderous mood -}

module Network.RTbl.Parser
( parseRTbl
, rTblToIsabelle) where

{- FAT TODO: Sort output. Do in Isabelle -}

import           Text.Parsec
import           Data.Functor ((<$>), ($>))
import           Control.Applicative ((<*), (*>), (<$>))
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.Ruleset
import           Network.IPTables.ParserHelper
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.Generated (metric_update, routing_action_next_hop_update, routing_action_oiface_update, empty_rr_hlp)
import           Data.Maybe (catMaybes, Maybe (Just, Nothing))
import           Control.Monad (void)

data RRuleInfo =
	OutputIface String |
	NextHop (Isabelle.Word Word32) |
	Metric Integer

data RRule = RRule { dstRange :: (Isabelle.Prefix_match Word32), infos :: [RRuleInfo] }

data RTbl = RTbl [RRule]

parseRTbl = flip runParser () $ RTbl <$> many parseRTblEntry 

parseRTblEntry = do
	let zn = Isabelle.Nat 0
	pfx <- ipv4addrOrCidr <|> (Prelude.const (Isabelle.PrefixMatch (Isabelle.ipv4addr_of_dotdecimal (zn,(zn,(zn,zn)))) zn) <$> lit "default")
	skipWS
	opts <- try parseOpts
	many1 (char '\n')
	return $ RRule pfx opts
	
parseOpt = choice (map try [parseOIF, parseNH, parseMetric, ignoreScope, ignoreProto, ignoreSrc])

parseOpts = catMaybes <$> many (parseOpt <* skipWS)

litornat l =  (void $ nat) <|> void (choice (map lit l))

ignoreScope = do
	lit "scope"
	skipWS
	litornat ["host", "link", "global"]
	return Nothing

ignoreProto = do
	lit "proto"
	skipWS
	litornat ["kernel", "boot", "static", "dhcp"]
	return Nothing

ignoreSrc = do
	lit "src"
	skipWS
	ipv4addr
	return Nothing

parseOIF = do
	lit "dev"
	skipWS
	Just . OutputIface <$> siface

parseNH = do
	lit "via"
	skipWS
	Just . NextHop <$> ipv4dotdecimal

parseMetric = do
	lit "metric"
	skipWS
	Just . Metric <$> nat

rTblToIsabelle (RTbl r) = map rTblEntryToIsabelle r

rTblEntryToIsabelle (RRule d i) = foldr info2update (empty_rr_hlp d) i

info2update (OutputIface i) = routing_action_oiface_update i
info2update (Metric m) = metric_update $ const $ Isabelle.Nat 0
info2update (NextHop h) = routing_action_next_hop_update h

instance Show RTbl where
	show (RTbl t) = unlines $ map show t
instance Show RRule where
	show (RRule r i) = unwords $ show r : map show i
instance Show RRuleInfo where
	show (OutputIface i) = unwords ["dev", i]
	show (NextHop i) = unwords ["via", Isabelle.ipv4addr_toString i]
	show (Metric i) = unwords ["metric", show i]

{- now, for some code duplication, because that's how its done in Ipassmt and IPTables parser -}
skipWS = void $ many $ oneOf " \t"
{-lit str = token str (string str)-}
lit str = (string str)
ipv4addrOrCidr = try (Isabelle.PrefixMatch <$> (ipv4dotdecimal <* char '/') <*> (Isabelle.Nat <$> nat)) 
             <|> try (flip Isabelle.PrefixMatch (Isabelle.Nat 0) <$> ipv4dotdecimal)
siface = many1 (oneOf $ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ ['+', '*', '.'])
