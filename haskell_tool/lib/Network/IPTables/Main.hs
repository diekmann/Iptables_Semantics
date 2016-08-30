{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.IPTables.Main (Operations(Operations), main') where


import Data.Functor ((<$>))
import Data.Maybe (fromJust)
import Control.Applicative ((<*>))
import Control.Monad (when, liftM)
import qualified Data.List as L
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import Network.RTbl.Parser (Routing_rule, RTbl, rTblToIsabelle)
import qualified System.IO
import Options.Generic
import Common.Util
import Network.IPTables.Analysis as Analysis
import qualified Network.IPTables.Generated as Isabelle
import Text.Parsec.Error (ParseError)


data Operations a = Operations
    { parseAssmt :: FilePath -> String -> Either ParseError (IpAssmt a)
    , parseRTbl :: FilePath -> String -> Either ParseError (RTbl a)
    , parseSave :: FilePath -> String -> Either ParseError (Ruleset a)
    , genericAssmt :: IsabelleIpAssmt a
    , certifySpoofing :: IsabelleIpAssmt a -> [Isabelle.Rule (Isabelle.Common_primitive a)] -> ([String], [(Isabelle.Iface, Bool)])
    , accessMatrix :: IsabelleIpAssmt a -> Maybe [Routing_rule a] -> [Isabelle.Rule (Isabelle.Common_primitive a)] -> Integer -> Integer -> ([(String, String)], [(String, String)])
    }


putErrStrLn :: String -> IO ()
putErrStrLn = System.IO.hPutStrLn System.IO.stderr

--labeled (and optional) command line arguments. For example: ./fffuu --table "filter"
data CommandLineArgsLabeled = CommandLineArgsLabeled
        { verbose :: Bool <?> "Show verbose debug output (for example, of the parser)."
        , ipassmt :: Maybe FilePath  <?> "Optional path to an IP assignment file. If not specified, it only loads `lo = [127.0.0.0/8]`."
        , routingtbl :: Maybe FilePath  <?> "Optional path to a routing table."
        , table :: Maybe String <?> "The table to load for analysis. Default: `filter`. Note: This tool does not support packet modification, so loading tables such as `nat` will most likeley fail."
        , chain :: Maybe String <?> "The chain to start the analysis. Default: `FORWARD`. Use `INPUT` for a host-based firewall."
        --TODO: we need some grouping for specific options for the analysis
        -- For example ./fffuu --analysis service-matrix --sport 424242 --analysis spoofing --foo
        , service_matrix_sport :: Maybe Integer <?> "Source port for the service matrix. If not specified, the randomly chosen source port 10000 is used. TODO: maybe use an ephemeral port ;-)."
        , service_matrix_dport :: [Integer] <?> "Destination port for the service matrix. If not specified, SSH and HTTP (22 and 80) will be used. Argument may be repeated multiple times."
        } deriving (Generic, Show)

instance ParseRecord CommandLineArgsLabeled


-- unlabeld, mandatory command line arguments. For example: ./fffuu "path/to/iptables-save"
-- http://stackoverflow.com/questions/36375556/haskell-unnamed-command-line-arguments-for-optparse-generic/36382477#36382477
data CommandLineArgsUnlabeled = CommandLineArgsUnlabeled
        (FilePath <?> "Required: Path to `iptables-save` output. This is the input for this tool.")
        deriving (Generic, Show)

instance ParseRecord CommandLineArgsUnlabeled

data CommandLineArgs = CommandLineArgs CommandLineArgsLabeled CommandLineArgsUnlabeled deriving (Show)

instance ParseRecord CommandLineArgs where
    parseRecord = CommandLineArgs <$> parseRecord <*> parseRecord

readIpAssmt ops filename = do
    src <- readFile filename
    case parseAssmt ops filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res

readRTbl ops filename = do
    src <- readFile filename
    case parseRTbl ops filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed routing table"
                        putStrLn (show res)
                        return $ rTblToIsabelle res

readArgs ops (CommandLineArgs labeled unlabeled) = do 
    (verbose, assmt, rtbl, tbl, chn, smOptions) <- readArgsLabeled labeled
    firewall <- readArgsUnlabeled unlabeled
    return (verbose, assmt, rtbl, tbl, chn, smOptions, firewall)
    where
        readArgsUnlabeled (CommandLineArgsUnlabeled (Helpful rsFilePath)) = (rsFilePath,) <$> readFile rsFilePath
            -- TODO: support stdin
            --where readInput [] = ("<stdin>",) <$> getContents

        readArgsLabeled (CommandLineArgsLabeled (Helpful verbose)
                            (Helpful ipassmtFilePath) (Helpful routingtblFilePath) (Helpful table) (Helpful chain)
                            (Helpful serviceMatrixSrcPort) (Helpful serviceMatrixDstPort)
                        ) = do
            assmt <- case ipassmtFilePath of
                        Just ipassmtPath -> readIpAssmt ops ipassmtPath
                        Nothing -> do
                            putErrStrLn "WARNING: no IP assignment specified, loading a generic file"
                            return $ genericAssmt ops
            rtbl <- case routingtblFilePath of
                        Just path -> Just `liftM` readRTbl ops path
                        Nothing -> return Nothing
            let tbl = case table of Just t -> t
                                    Nothing -> "filter"
            let chn = case chain of Just c -> c
                                    Nothing -> "FORWARD"
            smSrcPort <- (case serviceMatrixSrcPort of Just p -> if sanityCheckPort p
                                                                 then return p
                                                                 else error ("Invalid src port " ++ show p)
                                                       Nothing -> return 10000)
            smDstPorts <- case serviceMatrixDstPort of [] -> return [22, 80]
                                                       ps -> if all sanityCheckPort ps
                                                             then return ps
                                                             else error ("Invalid dst ports " ++ (show (filter (not . sanityCheckPort) ps)))
            let smOptions = map (\d -> (smSrcPort, d)) smDstPorts
            return (verbose, assmt, rtbl, tbl, chn, smOptions)
                where sanityCheckPort p = (p >= 0 && p < 65536)


main' ops = do 
    cmdArgs <- getRecord "FFFUU -- Fancy Formal Firewall Universal Understander: \n\n\
                    \Parses `iptables-save` and loads one table and chain. \
                    \By default, it loads the `filter` table and the `FORWARD` chain. \
                    \It unfolds all user-defined chains, generating a linear ruleset where only `ACCEPT` and `DROP` actions remain. \
                    \It abstracts over unknown matches. \
                    \By default, it does an overapproximation, i.e. it loads a more permissive version of the ruleset. \
                    \Then it runs a number of analysis. \
                    \Overapproximation means: if the anaylsis concludes that the packets you want to be dropped are dropped in the loaded overapproximation, then they are also dropped for your real firewall (without approximation)."
    --print (cmdArgs::CommandLineArgs)
    (verbose, ipassmt, rtbl, table, chain, smOptions, (srcname, src)) <- readArgs ops cmdArgs
    
    case parseSave ops srcname src of
        Left err -> do
            if isParseErrorWindowsNewline err
            then putStrLn "WARNING: File has Windows line endings.\n\
                           \Windows newlines are not supported."
            else return ()
            print err
        Right res -> do
            when verbose $ putStrLn $ "== Parser output =="
            when verbose $ putStrLn $ show res
            {- TODO: When a routing table got loaded, show its diff with the ipassmt -}
            unfolded <- loadUnfoldedRuleset verbose table chain res
            putStrLn $"== unfolded "++chain++" chain (upper closure) =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "== to simple firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Analysis.toSimpleFirewall unfolded)
            putStrLn "== to even-simpler firewall =="
            let upper_simple = Analysis.toSimpleFirewallWithoutInterfaces ipassmt rtbl unfolded
            putStrLn $ L.intercalate "\n" $ map show upper_simple
            putStrLn "== checking spoofing protection =="
            let (warnings, spoofResult) = certifySpoofing ops ipassmt unfolded
            mapM_ putStrLn warnings
            putStrLn "Spoofing certification results:"
            mapM_ (putStrLn . showSpoofCertification) spoofResult
            putStrLn "== calculating service matrices =="
            mapM_ (\(s,d) -> 
                        putStrLn ("=========== TCP port "++ show s ++ "->" ++ show d ++" =========")
                     >> putStrLn (showServiceMatrix (accessMatrix ops ipassmt rtbl unfolded s d))) smOptions
        where showServiceMatrix (nodes, edges) = concatMap (\(n, desc) -> renameNode n ++ " |-> " ++ desc ++ "\n") nodes ++ "\n" ++
                                                 concatMap (\e -> (renameEdge e) ++ "\n") edges
                  where renaming = zip (map fst nodes) prettyNames
                        renameNode n = fromJust $ lookup n renaming
                        renameEdge :: (String, String) -> String
                        renameEdge (v1, v2) = concat ["(", renameNode v1, ",", renameNode v2, ")"]

              showSpoofCertification (iface, rslt) = show (show iface, showProbablyFalse rslt)
                  where showProbablyFalse True = "True (certified)"
                        showProbablyFalse False = "Probably not (False)"
