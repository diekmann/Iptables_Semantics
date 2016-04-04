{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}


module Main where

import Data.Functor ((<$>))
import Control.Applicative ((<*>))
import qualified Data.List as L
import Network.IPTables.Ruleset
import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import qualified System.IO
import Options.Generic
import Common.Util (isParseErrorWindowsNewline)
import Network.IPTables.Analysis as Analysis
import qualified Network.IPTables.Generated as Isabelle

putErrStrLn = System.IO.hPutStrLn System.IO.stderr

--labeled (and optional) command line arguments. For example: ./fffuu --table "filter"
data CommandLineArgsLabeled = CommandLineArgsLabeled
        { ipassmt :: Maybe FilePath  <?> "Optional path to an IP assignment file. If not specified, it only loads `lo = [127.0.0.0/8]`."
        , table :: Maybe String <?> "The table to load for analysis. Default: `filter`. Note: This tool does not support pcket modification, so loading tables such as `nat` will most likeley fail."
        , chain :: Maybe String <?> "The chain to start the analysis. Default: `FORWARD`. Use `INPUT` for a host-based firewall."
        } deriving (Generic, Show)

instance ParseRecord CommandLineArgsLabeled


-- unlabeld, mandatory command line arguments. For example: ./fffuu "path/to/iptables-save"
-- trying to remove the obligation to alwayse have to type --rs
-- http://stackoverflow.com/questions/36375556/haskell-unnamed-command-line-arguments-for-optparse-generic/36382477#36382477
data CommandLineArgsUnlabeled = CommandLineArgsUnlabeled
        (FilePath <?> "Path to the `iptables-save` output.")
        deriving (Generic, Show)

instance ParseRecord CommandLineArgsUnlabeled

data CommandLineArgs = CommandLineArgs CommandLineArgsLabeled CommandLineArgsUnlabeled deriving (Show)

instance ParseRecord CommandLineArgs where
    parseRecord = CommandLineArgs <$> parseRecord <*> parseRecord

readIpAssmt filename = do
    src <- readFile filename
    case parseIpAssmt filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res


readArgs (CommandLineArgs labeled unlabeled) = do 
    (assmt, tbl, chn) <- readArgsLabeled labeled
    firewall <- readArgsUnlabeled unlabeled
    return (assmt, tbl, chn, firewall)
    where
        readArgsUnlabeled (CommandLineArgsUnlabeled (Helpful rsFilePath)) = (rsFilePath,) <$> readFile rsFilePath
            -- TODO: support stdin
            --where readInput [] = ("<stdin>",) <$> getContents

        readArgsLabeled (CommandLineArgsLabeled (Helpful ipassmtFilePath) (Helpful table) (Helpful chain)) = do
            assmt <- case ipassmtFilePath of
                        Just ipassmtPath -> readIpAssmt ipassmtPath
                        Nothing -> do
                            putErrStrLn "WARNING: no IP assignment specified, loading a generic file"
                            return Isabelle.ipassmt_generic
            let tbl = case table of Just t -> t
                                    Nothing -> "filter"
            let chn = case chain of Just c -> c
                                    Nothing -> "FORWARD"
            return (assmt, tbl, chn)



main :: IO ()
main = do 
    cmdArgs <- getRecord "FFFUU -- Fancy Formal Firewall Universal Understander"
    --print (cmdArgs::CommandLineArgs)
    (ipassmt, table, chain, (srcname, src)) <- readArgs cmdArgs
    
    case parseIptablesSave srcname src of
        Left err -> do
            if isParseErrorWindowsNewline err
            then putStrLn "WARNING: File has Windows line endings.\n\
                           \Windows newlines are not supported."
            else return ()
            print err
        Right res -> do
            let verbose = True
            putStrLn $ "== Parser output =="
            putStrLn $ show res
            unfolded <- loadUnfoldedRuleset verbose table chain res
            putStrLn $"== unfolded "++chain++" chain (upper closure) =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "== to simple firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Analysis.toSimpleFirewall unfolded)
            putStrLn "== to even-simpler firewall =="
            let upper_simple = Analysis.toSimpleFirewallWithoutInterfaces ipassmt unfolded
            putStrLn $ L.intercalate "\n" $ map show upper_simple
            putStrLn "== checking spoofing protection =="
            let (warnings, spoofResult) = certifySpoofingProtection ipassmt unfolded
            mapM_ putStrLn warnings
            putStrLn "Spoofing certification results:"
            mapM_ (putStrLn . showSpoofCertification) spoofResult
            putStrLn "== calculating service matrices =="
            putStrLn "===========SSH========="
            putStrLn $ showServiceMatrix $ Analysis.accessMatrix ipassmt unfolded 10000 22
            putStrLn "===========HTTP========="
            putStrLn $ showServiceMatrix $ Analysis.accessMatrix ipassmt unfolded 10000 80
        where showServiceMatrix (nodes, vertices) = concat (map (\(n, desc) -> n ++ " |-> " ++ desc ++ "\n") nodes) ++ "\n" ++
                                                    concat (map (\v -> show v ++ "\n") vertices)
              showSpoofCertification (iface, rslt) = show (show iface, showProbablyFalse rslt)
                  where showProbablyFalse True = "True (certified)"
                        showProbablyFalse False = "Probably not (False)"


