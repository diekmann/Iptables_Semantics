{-# Language FlexibleContexts #-}
{-# Language UndecidableInstances #-}
module Network.IPTables.Ruleset 
( Ruleset
, TableName
, checkParsedTables
--, rulesetLookup --use loadUnfoldedRuleset instead
, loadUnfoldedRuleset
, mkRuleset
, rsetTablesM
, tblChainsM
, chnRulesM
, mkTable
, mkChain
, mkParseRule
, ParsedMatchAction(..)
) where

import           Data.List (intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L
import qualified Debug.Trace
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString()
import           Control.Monad (when)
import Network.IPTables.IsabelleToString (Word32)


-- where type a is either Word32 for IPv4 or Word128 for IPv6

data Ruleset a = Ruleset { rsetTables :: Map TableName (Table a) }

data Table a = Table { tblChains :: Map ChainName (Chain a)}

data Chain a = Chain { chnDefault :: Maybe Isabelle.Action
                     , chnCounter :: (Integer,Integer)
                     , chnRules   :: [ParseRule a]
                     }


data ParsedMatchAction a = ParsedMatch (Isabelle.Common_primitive a)
                       | ParsedNegatedMatch (Isabelle.Common_primitive a)
                       | ParsedAction Isabelle.Action

instance Show (Isabelle.Common_primitive a) => Show (ParsedMatchAction a) where
    show (ParsedMatch m) = "ParsedMatch " ++ show m
    show (ParsedNegatedMatch m) = "ParsedNegatedMatch " ++ show m
    show (ParsedAction a) = "ParsedAction " ++ show a


data ParseRule a = ParseRule { ruleArgs :: [ParsedMatchAction a] }



type TableName = String
type ChainName = String



mkRuleset       = Ruleset M.empty
mkTable         = Table M.empty
mkChain def ctr = Chain def ctr []
mkParseRule     = ParseRule


rsetTablesM f rset = rset { rsetTables = f (rsetTables rset) }
tblChainsM  f tbl  = tbl  { tblChains  = f (tblChains  tbl ) }
chnDefaultM f chn  = chn  { chnDefault = f (chnDefault chn ) }
chnRulesM   f chn  = chn  { chnRules   = f (chnRules   chn ) }
ruleArgsM   f rule = rule { ruleArgs   = f (ruleArgs   rule) }



example = Ruleset $ M.fromList
    [ ("filter", Table $ M.fromList [("INPUT",Chain (Just Isabelle.Drop) (0,0) [])])
    ]


-- converts a parsed table (e.g. "filter" or "raw") to the type the Isabelle code needs
-- also returns a Map with the default policies
-- may throw an error
rulesetLookup :: Isabelle.Len a => TableName -> Ruleset a ->
    Either String ([(String, [Isabelle.Rule (Isabelle.Common_primitive a)])], Map ChainName Isabelle.Action)
rulesetLookup table r = case M.lookup table (rsetTables r)
    of Nothing -> Left $ "Table with name `"++table++"' not found"
       Just t -> to_Isabelle_ruleset_AssocList t
                 >>= \isabelle_rules -> Right (isabelle_rules, default_policies t)
    where default_policies t = M.mapMaybe chnDefault (tblChains t)


-- input: ruleset from the parser
-- output: rule list our Isabelle algorithms can work on
-- may throw an error; is IO because it dumps debug info at you :)
-- verbose_flag -> table -> chain -> pased_ruleset -> isabelle_ruleset_and_debugging_output
loadUnfoldedRuleset :: Bool -> String -> String -> Ruleset Word32 -> IO [Isabelle.Rule (Isabelle.Common_primitive Word32)]
loadUnfoldedRuleset debug table chain res = do
    when (table /= "filter") $ do 
        putStrLn $ "INFO: Officially, we only support the filter table. \
                    \You requested the `" ++ table ++ "' table. Let's see what happens ;-)"
    when (not (chain `elem` ["FORWARD", "INPUT", "OUTPUT"])) $ do 
        putStrLn $ "INFO: Officially, we only support the chains \
                    \FORWARD, INPUT, OUTPUT. You requested the `" ++ chain ++ 
                    "' chain. Let's see what happens ;-)"
    putStrLn "== Checking which tables are supported for analysis. Usually, only `filter'. =="
    checkParsedTables res
    putStrLn $ "== Transformed to Isabelle type (only " ++ table ++ " table) =="
    let (fw, defaultPolicies) = case rulesetLookup table res of
                    Right rules -> rules
                    Left err -> error err
    let policy = case M.lookup chain defaultPolicies of
                    Just policy -> policy
                    Nothing -> error $ "Default policy for chain " ++ chain ++ " not found"
    -- Theorem: Semantics_Goto.rewrite_Goto_chain_safe
    let noGoto = case Isabelle.rewrite_Goto_safe fw of
                              Nothing -> error "There are gotos in your ruleset which we cannot handle."
                              Just rs -> rs
    -- Theorem: unfold_optimize_common_matcher_univ_ruleset_CHAIN
    let unfolded = case Isabelle.unfold_ruleset_CHAIN_safe chain policy $ Isabelle.map_of_string_ipv4 noGoto of
                              Nothing -> error "Unfolding ruleset failed. Does the Linux kernel load it? Is it cyclic? Are there any actions not supported by this tool?"
                              Just rs -> rs
    
    when debug $ do putStrLn $ show $ fw
                    putStrLn $ "Default Policies: " ++ show defaultPolicies
                    putStrLn $ "== unfolded " ++ chain ++ " chain =="
                    putStrLn $ L.intercalate "\n" $ map show unfolded
    return $ unfolded

-- transforming to Isabelle type

to_Isabelle_ruleset_AssocList :: Isabelle.Len a => Table a -> Either String [(String, [Isabelle.Rule (Isabelle.Common_primitive a)])]
to_Isabelle_ruleset_AssocList t = let rs = convertRuleset (tblChains t) in 
                                        if not (Isabelle.sanity_wf_ruleset rs)
                                        then Left "Reading ruleset failed! sanity_wf_ruleset check failed."
                                        else Debug.Trace.trace "sanity_wf_ruleset passed" (Right rs)
    where convertRules = map to_Isabelle_Rule
          convertRuleset = map (\(k,v) -> (k, convertRules (chnRules v))) . M.toList 
           

to_Isabelle_Rule :: Isabelle.Len a => ParseRule a -> Isabelle.Rule (Isabelle.Common_primitive a)
to_Isabelle_Rule r = Isabelle.Rule
                        (Isabelle.alist_and $ Isabelle.compress_parsed_extra (fMatch (ruleArgs r)))
                        (filter_Isabelle_Action (ruleArgs r))
    where --filter out the Matches (Common_primitive) in ParsedMatchAction
          fMatch :: [ParsedMatchAction a] -> [Isabelle.Negation_type (Isabelle.Common_primitive a)]
          fMatch [] = []
          fMatch (ParsedMatch a : ss) = Isabelle.Pos a : fMatch ss
          fMatch (ParsedNegatedMatch a : ss) = Isabelle.Neg a : fMatch ss
          fMatch (ParsedAction _ : ss) = fMatch ss

filter_Isabelle_Action :: [ParsedMatchAction a] -> Isabelle.Action
filter_Isabelle_Action ps = case fAction ps of [] -> Isabelle.Empty
                                               [a] -> a
                                               as -> error $ "at most one action per rule: " ++ show as
    where --filter out the Action in ParsedMatchAction
          fAction [] = []
          fAction (ParsedMatch _ : ss) = fAction ss
          fAction (ParsedNegatedMatch _ : ss) = fAction ss
          fAction (ParsedAction a : ss) = a : fAction ss



-- this is just DEBUGING
-- tries to catch errors of rulesetLookup
checkParsedTables :: Isabelle.Len a => Ruleset a -> IO ()
checkParsedTables res = check tables
    where tables = M.keys (rsetTables res)
          check :: [TableName] -> IO ()
          check [] = return ()
          check (t:ts) = do
                         case rulesetLookup t res of Right (chain, defaults) -> putStrLn (success t chain)
                                                     Left err -> putStrLn (errormsg t err)
                         check ts
          errormsg t msg = concat ["Table `", t ,"' caught exception: `"
                                   , msg
                                   , "'. Analysis not possible for this table. "
                                   , "This is probably due to unsupportd actions "
                                   , "(or a bug in the parser)."]
          success t chain = concat ["Parsed ", show (length chain)
                                   , " chains in table ", t, ", a total of "
                                   , show (length (concat (map snd chain)))
                                   , " rules"]

-- toString functions

instance Show (Isabelle.Common_primitive a) => Show (Ruleset a) where
    show rset =
        let tables = map renderTable $ M.toList $ rsetTables rset
        in  join tables


renderTable :: Show (Isabelle.Common_primitive a) => (TableName, Table a) -> String
renderTable (name,tbl) = join
    [ "*"++name
    , declareChains (tblChains tbl)
    , addRules (tblChains tbl)
    , "COMMIT"
    ]

declareChains :: Map ChainName (Chain a) -> String
declareChains chnMap =
    join $ map renderDecl (M.toList chnMap)
    where renderDecl (name, chain) =
            let (packets,bytes) = chnCounter chain
            in  concat [ ":", name, " ", renderPolicy (chnDefault chain)
                       , " [", show packets, ":", show bytes, "]"
                       ]

addRules :: Show (Isabelle.Common_primitive a) => Map ChainName (Chain a) -> String
addRules chnMap =
    let rules = concatMap expandChain (M.toList chnMap)
        expandChain (name,chain) = map (\rl -> (name,rl)) $ chnRules chain
        renderRule (chnname, rl) =
            concat ["-A ", chnname
                   , concatMap expandOpt (ruleArgs rl)
                   ]
        expandOpt opt = concat [" `", show opt, "'"]
    in  join $ map renderRule rules


renderPolicy (Just Isabelle.Accept) = "ACCEPT"
renderPolicy (Just Isabelle.Drop)   = "DROP"
renderPolicy Nothing = "-"


join = intercalate "\n"
