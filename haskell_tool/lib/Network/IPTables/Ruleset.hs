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
import qualified Control.Exception
import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString()
import           Control.Monad (when)


data Ruleset = Ruleset { rsetTables :: Map TableName Table } -- deriving (Ord)

data Table = Table { tblChains :: Map ChainName Chain} --deriving (Ord)

data Chain = Chain { chnDefault :: Maybe Isabelle.Action
                   , chnCounter :: (Integer,Integer)
                   , chnRules   :: [ParseRule]
                   }
    --deriving (Show)



data ParsedMatchAction = ParsedMatch Isabelle.Common_primitive
                       | ParsedNegatedMatch Isabelle.Common_primitive
                       | ParsedAction Isabelle.Action
    deriving (Show)

data ParseRule  = ParseRule  { ruleArgs   :: [ParsedMatchAction] } deriving (Show)



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
rulesetLookup :: TableName -> Ruleset ->
    ([(String, [Isabelle.Rule Isabelle.Common_primitive])], Map ChainName Isabelle.Action)
rulesetLookup table r = case M.lookup table (rsetTables r)
    of Nothing -> error $ "Table with name `"++table++"' not found"
       Just t -> (to_Isabelle_ruleset_AssocList t, default_policies t)
    where default_policies t = M.foldWithKey (\ k v acc -> update_action k v acc) M.empty (tblChains t)
          update_action :: ChainName -> Chain -> Map ChainName Isabelle.Action -> Map ChainName Isabelle.Action
          update_action k v acc = case chnDefault v of Just a -> M.insert k a acc
                                                       Nothing -> acc


-- input: ruleset from the parser
-- output: rule list our Isabelle algorithms can work on
-- may throw an error; is IO because it dumps debug info at you :)
-- verbose_flag -> table -> chain -> pased_ruleset -> isabelle_ruleset_and_debugging_output
loadUnfoldedRuleset :: Bool -> String -> String -> Ruleset -> IO [Isabelle.Rule Isabelle.Common_primitive]
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
    let (fw, defaultPolicies) = rulesetLookup table res
    let policy = case M.lookup chain defaultPolicies of
                    Just policy -> policy
                    Nothing -> error $ "Default policy for chain " ++ chain ++ " not found"
    -- Theorem: Semantics_Goto.rewrite_Goto_chain_safe
    let noGoto = case Isabelle.rewrite_Goto_safe fw of
                              Nothing -> error "There are gotos in your ruleset which we cannot handle."
                              Just rs -> rs
    -- Theorem: unfold_optimize_common_matcher_univ_ruleset_CHAIN
    let unfolded = case Isabelle.unfold_ruleset_CHAIN_safe chain policy $ Isabelle.map_of_string noGoto of
                              Nothing -> error "Unfolding ruleset failed. Does the Linux kernel load it? Is it cyclic? Are there any actions not supported by this tool?"
                              Just rs -> rs
    
    when debug $ do putStrLn $ show $ fw
                    putStrLn $ "Default Policies: " ++ show defaultPolicies
                    putStrLn $ "== unfolded " ++ chain ++ " chain =="
                    putStrLn $ L.intercalate "\n" $ map show unfolded
    return $ unfolded

-- transforming to Isabelle type

to_Isabelle_ruleset_AssocList :: Table -> [(String, [Isabelle.Rule Isabelle.Common_primitive])]
to_Isabelle_ruleset_AssocList t = let rs = convertRuleset (tblChains t) in 
                                        if not (Isabelle.sanity_wf_ruleset rs)
                                        then error $ "Reading ruleset failed! sanity_wf_ruleset check failed."
                                        else Debug.Trace.trace "sanity_wf_ruleset passed" rs
    where convertRules = map to_Isabelle_Rule
          convertRuleset = map (\(k,v) -> (k, convertRules (chnRules v))) . M.toList 
           

to_Isabelle_Rule :: ParseRule -> Isabelle.Rule Isabelle.Common_primitive
to_Isabelle_Rule r = Isabelle.Rule
    (Isabelle.alist_and $ Isabelle.compress_parsed_extra (filter_Isabelle_Common_Primitive (ruleArgs r)))
    (filter_Isabelle_Action (ruleArgs r))

filter_Isabelle_Common_Primitive :: [ParsedMatchAction] -> [Isabelle.Negation_type Isabelle.Common_primitive]
filter_Isabelle_Common_Primitive [] = []
filter_Isabelle_Common_Primitive (ParsedMatch a : ss) = Isabelle.Pos a : filter_Isabelle_Common_Primitive ss
filter_Isabelle_Common_Primitive (ParsedNegatedMatch a : ss) = Isabelle.Neg a : filter_Isabelle_Common_Primitive ss
filter_Isabelle_Common_Primitive (ParsedAction _ : ss) = filter_Isabelle_Common_Primitive ss

filter_Isabelle_Action :: [ParsedMatchAction] -> Isabelle.Action
filter_Isabelle_Action ps = case fAction ps of [] -> Isabelle.Empty
                                               [a] -> a
                                               as -> error $ "at most one action per rule: " ++ show as
    where fAction [] = []
          fAction (ParsedMatch _ : ss) = fAction ss
          fAction (ParsedNegatedMatch _ : ss) = fAction ss
          fAction (ParsedAction a : ss) = a : fAction ss



-- this is just DEBUGING
-- tries to catch exceptions of rulesetLookup
checkParsedTables :: Ruleset -> IO ()
checkParsedTables res = check tables
    where tables = M.keys (rsetTables res)
          check :: [TableName] -> IO ()
          check [] = return ()
          check (t:ts) = do
                         let (chain, defaults) = rulesetLookup t res
                         catch t (putStrLn (success t chain))
                         check ts
          catch :: String -> IO () -> IO ()
          catch t fn = Control.Exception.catch fn (putStrLn . (error t))
          error t msg = concat ["Table `", t ,"' caught exception: `"
                               , show (msg::Control.Exception.SomeException)
                               , "'. Analysis not possible for this table. "
                               , "This is probably due to unsupportd actions "
                               , "(or a bug in the parser)."]
          success t chain = concat ["Parsed ", show (length chain)
                                   , " chains in table ", t, ", a total of "
                                   , show (length (concat (map snd chain)))
                                   , " rules"]

-- toString functions

instance Show Ruleset where
    show rset =
        let tables = map renderTable $ M.toList $ rsetTables rset
        in  join tables


renderTable :: (TableName, Table) -> String
renderTable (name,tbl) = join
    [ "*"++name
    , declareChains (tblChains tbl)
    , addRules (tblChains tbl)
    , "COMMIT"
    ]

declareChains :: Map ChainName Chain -> String
declareChains chnMap =
    join $ map renderDecl (M.toList chnMap)
    where renderDecl (name, chain) =
            let (packets,bytes) = chnCounter chain
            in  concat [ ":", name, " ", renderPolicy (chnDefault chain)
                       , " [", show packets, ":", show bytes, "]"
                       ]

addRules :: Map ChainName Chain -> String
addRules chnMap =
    let rules = concatMap expandChain (M.toList chnMap)
        expandChain (name,chain) = map (\rl -> (name,rl)) $ chnRules chain
        renderRule (chnname, rl) =
            concat ["-A ", chnname
                   , concatMap expandOpt (ruleArgs rl)
                   ]
        expandOpt opt = concat [" `", show opt, "'"]
    in  join $ map renderRule rules


renderPolicy (Just Isabelle.Accept)      = "ACCEPT"
renderPolicy (Just Isabelle.Drop)        = "DROP"
renderPolicy Nothing = "-"


join = intercalate "\n"
