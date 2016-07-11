{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}


module Main where

import Data.Functor ((<$>))
import Data.Maybe (fromJust)
import Control.Applicative ((<*>))
import Control.Monad (when)
import qualified Data.List as L
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import qualified System.IO
import Options.Generic
import Common.Util
import Network.IPTables.Analysis as Analysis
import qualified Network.IPTables.Generated as Isabelle


putErrStrLn :: String -> IO ()
putErrStrLn = System.IO.hPutStrLn System.IO.stderr

--labeled (and optional) command line arguments. For example: ./fffuu --table "filter"
data CommandLineArgsLabeled = CommandLineArgsLabeled
        { verbose :: Bool <?> "Show verbose debug output (for example, of the parser)."
        , ipassmt :: Maybe FilePath  <?> "Optional path to an IP assignment file. If not specified, it only loads `lo = [127.0.0.0/8]`."
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
        (FilePath <?> "Path to the `iptables-save` output.")
        deriving (Generic, Show)

instance ParseRecord CommandLineArgsUnlabeled

data CommandLineArgs = CommandLineArgs CommandLineArgsLabeled CommandLineArgsUnlabeled deriving (Show)

instance ParseRecord CommandLineArgs where
    parseRecord = CommandLineArgs <$> parseRecord <*> parseRecord

--readIpAssmt :: FilePath -> IO IsabelleIpAssmt Word32
readIpAssmt filename = do
    src <- readFile filename
    case parseIpAssmt_ipv4 filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res


readArgs (CommandLineArgs labeled unlabeled) = do 
    (verbose, assmt, tbl, chn, smOptions) <- readArgsLabeled labeled
    firewall <- readArgsUnlabeled unlabeled
    return (verbose, assmt, tbl, chn, smOptions, firewall)
    where
        readArgsUnlabeled (CommandLineArgsUnlabeled (Helpful rsFilePath)) = (rsFilePath,) <$> readFile rsFilePath
            -- TODO: support stdin
            --where readInput [] = ("<stdin>",) <$> getContents

        readArgsLabeled (CommandLineArgsLabeled (Helpful verbose)
                            (Helpful ipassmtFilePath) (Helpful table) (Helpful chain)
                            (Helpful serviceMatrixSrcPort) (Helpful serviceMatrixDstPort)
                        ) = do
            assmt <- case ipassmtFilePath of
                        Just ipassmtPath -> readIpAssmt ipassmtPath
                        Nothing -> do
                            putErrStrLn "WARNING: no IP assignment specified, loading a generic file"
                            return Isabelle.ipassmt_generic_ipv4
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
            return (verbose, assmt, tbl, chn, smOptions)
                where sanityCheckPort p = (p >= 0 && p < 65536)


main :: IO ()
main = do 
    cmdArgs <- getRecord "FFFUU -- Fancy Formal Firewall Universal Understander: \n\n\
                    \Parses `iptables-save` and loads one table and chain. \
                    \By default, it loads the `filter` table and the `FORWARD` chain. \
                    \It unfolds all user-defined chains, generating a linear ruleset where only `ACCEPT` and `DROP` actions remain. \
                    \It abstracts over unknown matches. \
                    \By default, it does an overapproximation, i.e. it loads a more permissive version of the ruleset. \
                    \Then it runs a number of analysis. \
                    \Overapproximation means: if the anaylsis concludes that the packets you want to be dropped are dropped in the loaded overapproximation, then they are also dropped for your real firewall (without approximation)."
    --print (cmdArgs::CommandLineArgs)
    (verbose, ipassmt, table, chain, smOptions, (srcname, src)) <- readArgs cmdArgs
    
    case parseIptablesSave_ipv4 srcname src of
        Left err -> do
            if isParseErrorWindowsNewline err
            then putStrLn "WARNING: File has Windows line endings.\n\
                           \Windows newlines are not supported."
            else return ()
            print err
        Right res -> do
            when verbose $ putStrLn $ "== Parser output =="
            when verbose $ putStrLn $ show res
            unfolded <- loadUnfoldedRuleset verbose table chain res
            putStrLn $"== unfolded "++chain++" chain (upper closure) =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "== to simple firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Analysis.toSimpleFirewall unfolded)
            putStrLn "== to even-simpler firewall =="
            let upper_simple = Analysis.toSimpleFirewallWithoutInterfaces ipassmt unfolded
            putStrLn $ L.intercalate "\n" $ map show upper_simple
            putStrLn "== checking spoofing protection =="
            let (warnings, spoofResult) = certifySpoofingProtection_ipv4 ipassmt unfolded
            mapM_ putStrLn warnings
            putStrLn "Spoofing certification results:"
            mapM_ (putStrLn . showSpoofCertification) spoofResult
            putStrLn "== calculating service matrices =="
            mapM_ (\(s,d) -> 
                        putStrLn ("=========== TCP port "++ show s ++ "->" ++ show d ++" =========")
                     >> putStrLn (showServiceMatrix (Analysis.accessMatrix_ipv4 ipassmt unfolded s d))) smOptions
        where showServiceMatrix (nodes, edges) = concatMap (\(n, desc) -> renameNode n ++ " |-> " ++ desc ++ "\n") nodes ++ "\n" ++
                                                 concatMap (\e -> (renameEdge e) ++ "\n") edges
                  where renaming = zip (map fst nodes) prettyNames
                        renameNode n = fromJust $ lookup n renaming
                        renameEdge :: (String, String) -> String
                        renameEdge (v1, v2) = concat ["(", renameNode v1, ",", renameNode v2, ")"]

              showSpoofCertification (iface, rslt) = show (show iface, showProbablyFalse rslt)
                  where showProbablyFalse True = "True (certified)"
                        showProbablyFalse False = "Probably not (False)"


