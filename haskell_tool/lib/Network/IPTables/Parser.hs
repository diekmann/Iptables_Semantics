{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.IPTables.Parser (parseIptablesSave) where

import           Control.Applicative ((<$>),(<*), (*>))
import           Data.List (isPrefixOf)
import qualified Data.Map as M
import qualified Debug.Trace
import           Text.Parsec hiding (token)
import           Network.IPTables.Ruleset
import           Network.IPTables.IsabelleToString (Word32, Word128)
import           Network.IPTables.ParserHelper
import qualified Network.IPTables.Generated as Isabelle

parseIptablesSave :: SourceName -> String -> Either ParseError (Ruleset Word32)
parseIptablesSave = runParser ruleset_ipv4 initRState

parseIptablesSave_ipv6 :: SourceName -> String -> Either ParseError (Ruleset Word128)
parseIptablesSave_ipv6 = runParser ruleset_ipv6 initRState

data RState a = RState { rstRules  :: Ruleset a
                       , rstActive :: Maybe TableName
                       }
    --deriving (Show)

initRState = RState mkRuleset Nothing

rstRulesM :: (Ruleset a -> Ruleset a) -> RState a -> RState a
rstRulesM  f rst = rst { rstRules  = f (rstRules rst) }

rstActiveM :: (Maybe TableName -> Maybe TableName) -> RState a -> RState a
rstActiveM f rst = rst { rstActive = f (rstActive rst) }


ruleset_ipv6 :: Parsec String (RState Word128) (Ruleset Word128)
ruleset_ipv6 = ruleset_generic rule_ipv6

ruleset_ipv4 :: Parsec String (RState Word32) (Ruleset Word32)
ruleset_ipv4 = ruleset_generic rule_ipv4

ruleset_generic :: Parsec String (RState a) () -> Parsec String (RState a) (Ruleset a)
ruleset_generic rule_parser = do
    many $ choice [table, chain, rule_parser, commit, comment, emptyLine]
    eof
    rstRules <$> getState


comment = line $ do
    char '#' >> skipWS >> restOfLine
    return ()

emptyLine = line (return ())

table = line $ do
    lit "*"
    name <- tableName

    -- table with same name will replace existing table
    modifyState $ (rstRulesM . rsetTablesM) (M.insert name mkTable)
                . rstActiveM (const $ Just name)
    return ()

chain = line $ do
    lit ":"
    name   <- chainName <* skipWS
    defPol <- policy
    ctr    <- counter
    _      <- restOfLine

    let chn = mkChain defPol ctr
    tblname <- getTableName
    modifyState $ (rstRulesM . rsetTablesM . atMap tblname . tblChainsM)
                    (M.insert name chn)

    return ()

probablyNegated parser = ParsedNegatedMatch <$> try (lit "! " >> (lookAheadEOT parser) <* skipWS)
                     <|> ParsedMatch <$> (try (lookAheadEOT parser) <* skipWS)

probablyNegatedSingleton parser = (\x -> [x]) <$> (probablyNegated parser)

parseWithModulePrefix modul parser = try $ skipWS *> string modul *> (many1 parser)


-- This file should be in sync with the SML parser. The SML parser is the reference.

knownMatch_ipv4 :: Parsec String s [ParsedMatchAction Word32]
knownMatch_ipv4 = knownMatch_generic ipv4addrOrCidr ipv4range
    where ipv4addrOrCidr = try ipv4cidr <|> try ipv4addr

knownMatch_ipv6 :: Parsec String s [ParsedMatchAction Word128]
knownMatch_ipv6 = knownMatch_generic ipv6addrOrCidr ipv6range
    where ipv6addrOrCidr = try ipv6cidr <|> try ipv6addr

knownMatch_generic
  :: Parsec String s (Isabelle.Ipt_iprange a) -> 
     Parsec String s (Isabelle.Ipt_iprange a) ->
     Parsec String s [ParsedMatchAction a]
knownMatch_generic parser_ipaddr_cidr parser_iprange = do
    p <-  (probablyNegatedSingleton $ lit "-p " >> Isabelle.Prot <$> protocol)
    
      <|> (probablyNegatedSingleton $ lit "-s " >> Isabelle.Src <$> parser_ipaddr_cidr)
      <|> (probablyNegatedSingleton $ lit "-d " >> Isabelle.Dst <$> parser_ipaddr_cidr)
      
      <|> (parseWithModulePrefix "-m iprange " $
                (probablyNegated $ lit "--src-range " >> Isabelle.Src <$> parser_iprange)
            <|> (probablyNegated $ lit "--dst-range " >> Isabelle.Dst <$> parser_iprange))
      
      <|> (parseWithModulePrefix "-m tcp " $
                (probablyNegated $ lit "--sport " >> Isabelle.Src_Ports <$> (\p -> [p]) <$> parsePortOne)
            <|> (probablyNegated $ lit "--dport " >> Isabelle.Dst_Ports <$> (\p -> [p]) <$> parsePortOne)
            <|> (probablyNegated $ lit "--tcp-flags " >> Isabelle.L4_Flags <$> matchTcpFlags))
                
      <|> (parseWithModulePrefix "-m udp " $ 
                (probablyNegated $ lit "--sport " >> Isabelle.Src_Ports <$> (\p -> [p]) <$> parsePortOne)
            <|> (probablyNegated $ lit "--dport " >> Isabelle.Dst_Ports <$> (\p -> [p]) <$> parsePortOne))
      
      <|> (parseWithModulePrefix "-m multiport "$ 
                (probablyNegated $ lit "--sports " >> Isabelle.Src_Ports <$> parseCommaSeparatedList parsePortOne)
            <|> (probablyNegated $ lit "--dports " >> Isabelle.Dst_Ports <$> parseCommaSeparatedList parsePortOne))
      
      <|> (probablyNegatedSingleton $ lit "-i " >> Isabelle.IIface <$> iface)
      <|> (probablyNegatedSingleton $ lit "-o " >> Isabelle.OIface <$> iface)
      
      -- TODO: can ctstate be negated? never seen or tested this
      <|> (parseWithModulePrefix "-m state " $
                (probablyNegated $ lit "--state " >> Isabelle.CT_State <$> ctstate))
      <|> (parseWithModulePrefix "-m conntrack " $
                (probablyNegated $ lit "--ctstate " >> Isabelle.CT_State <$> ctstate))
      
      
      <|> ((\x -> [x]) <$> ((lookAheadEOT target) <* skipWS)) --TODO: tune
      
    return $ p


unknownMatch = token "unknown match" $ do
    extra <- (many1 (noneOf " \t\n\"") <|> try quotedString)
    let e = if "-j" `isPrefixOf` extra
              then Debug.Trace.trace ("Warning: probably a parse error at "++extra) extra
              else extra
    return $ (\x -> [x]) $ ParsedMatch $ Isabelle.Extra $ e --TODO: tune


rule_ipv4 :: Parsec String (RState Word32) ()
rule_ipv4 = rule_generic knownMatch_ipv4

rule_ipv6 :: Parsec String (RState Word128) ()
rule_ipv6 = rule_generic knownMatch_ipv6

rule_generic
    :: Parsec String (RState a) [ParsedMatchAction a] -> Parsec String (RState a) ()
rule_generic knownMatch_parser = line $ do
    lit "-A"
    chnname <- chainName <* skipWS
    args    <- concat <$> many (knownMatch_parser <|> unknownMatch)
    unparsed <- restOfLine

    let rest    = if unparsed == ""
                  then []
                  else error ("ERROR unparsable : " ++ unparsed)
                       -- Debug.Trace.trace ("ERROR unparsable : " ++ unparsed)
                       -- [ParsedMatch (Isabelle.Extra unparsed)]
        myArgs  = args ++ rest
        rl      = mkParseRule myArgs

    tblname <- getTableName
    modifyState $ (  rstRulesM
                   . rsetTablesM . atMap tblname
                   . tblChainsM  . atMap chnname
                   . chnRulesM)
                  (++ [rl])

    return ()


commit = line $ do
    lit "COMMIT"
    restOfLine

    modifyState $ rstActiveM (const Nothing)

    return ()


getTableName = getState >>=
    safeJust "No active table." return . rstActive

safeJust msg f = maybe (fail msg) f


tableName = token "table name" $ many1 $ oneOf $ ['A'..'Z']++['a'..'z']
chainName = many1 $ oneOf $ ['A'..'Z']++['a'..'z']++['0'..'9']++['_','-','~']

policy  =  token "policy"
        $  (string "ACCEPT" >> return (Just Isabelle.Accept))
       <|> (string "DROP"   >> return (Just Isabelle.Drop))
       <|> (string "-"      >> return Nothing)

counter = token "counter" $ do
    char '['
    packets <- nat
    char ':'
    bytes <- nat
    char ']'
    return (packets,bytes)


-- Parsing Helper --

-- cannot be combined with lookAheadEOT
lit str = token str (string str)

restOfLine = many (noneOf "\n")

line  p      = p <* (skipWS >> eol)
token desc p = (p <* skipWS) <?> desc
skipWS = many $ oneOf ws

eol = char '\n'
ws  = " \t"

-- loook ahead end of token
-- cannot be combined with token
lookAheadEOT parser = do 
    res <- parser
    lookAhead (oneOf ws <|> eol)
    return res

parseCommaSeparatedList parser = sepBy parser (char ',')

parsePortOne = try tuple <|> single
    where port_raw = Isabelle.nat_to_16word <$> natMaxval 65535
          single = do
              p <- port_raw
              return (p,p)
          tuple = do
              p1 <- port_raw
              char ':'
              p2 <- port_raw
              if p2 `Isabelle.word_less_eq` p1 then
                  return (Debug.Trace.trace (concat
                             ["WARNING: port "
                             ,show (Isabelle.word_to_nat p1)
                             ," >= " ++ show (Isabelle.word_to_nat p2)
                             ])
                         (p1,p2))
                  else return (p1,p2)

ctstate = Isabelle.mk_Set <$> parseCommaSeparatedList ctstateOne
    where ctstateOne = choice [string "NEW" >> return Isabelle.CT_New
                              ,string "ESTABLISHED" >> return Isabelle.CT_Established
                              ,string "RELATED" >> return Isabelle.CT_Related
                              ,string "UNTRACKED" >> return Isabelle.CT_Untracked
                              ,string "INVALID" >> return Isabelle.CT_Invalid]              

matchTcpFlags = do 
    mask <- parseTcpFlagSet
    _ <- string " "
    comp <- parseTcpFlagSet
    return $ Isabelle.TCP_Flags mask comp
    where parseTcpFlagSet = Isabelle.mk_Set <$> parseCommaSeparatedList tcpFlag

-- needs LookAheadEOT, otherwise, this might happen to the custom LOG_DROP target:
-- -A ranges_96 `ParsedAction -j LOG' `ParsedMatch ~~_DROP~~'
target = ParsedAction <$> (
           try (string "-j REJECT --reject-with "
                >> many1 (oneOf $ ['a'..'z']++['-']) >> return (Isabelle.Reject))
       <|> try (string "-g " >> Isabelle.Goto <$> lookAheadEOT chainName)
       <|> try (string "-j " >> choice (map (try . lookAheadEOT)
                                       [string "DROP" >> return Isabelle.Drop
                                       ,string "REJECT" >> return Isabelle.Reject
                                       ,string "ACCEPT" >> return Isabelle.Accept
                                       ,string "LOG" >> return Isabelle.Log
                                       ,string "RETURN" >> return Isabelle.Return
                                       ]))
       <|> try (string "-j " >> Isabelle.Call <$> lookAheadEOT chainName)
       )
    
-- Helper --
atMap key f = M.adjust f key
