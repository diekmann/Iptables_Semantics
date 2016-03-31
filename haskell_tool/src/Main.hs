{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}


module Main where

import Data.Functor ((<$>))
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

data CommandLineArgs = CommandLineArgs
        { ipassmt :: Maybe FilePath  <?> "Optional path to an IP assignment file. If not specified, it only loads `lo = [127.0.0.0/8]`."
        , rs :: FilePath <?> "Path to the `iptables-save` output."
        } deriving (Generic, Show)

instance ParseRecord CommandLineArgs

readIpAssmt filename = do
    src <- readFile filename
    case parseIpAssmt filename src of
        Left err -> do print err
                       error $ "could not parse " ++ filename
        Right res -> do putStrLn "Parsed IpAssmt"
                        putStrLn (show res)
                        return $ ipAssmtToIsabelle res


-- TODO: select table and chain
readArgs (CommandLineArgs (Helpful ipassmtFilePath) (Helpful rsFilePath)) = do
    assmt <- case ipassmtFilePath of
                Just ipassmtPath -> readIpAssmt ipassmtPath
                Nothing -> do
                    putErrStrLn "WARNING: no IP assignment specified, loading a generic file"
                    return Isabelle.ipassmt_generic
    firewall <- (rsFilePath,) <$> readFile rsFilePath
    return (assmt, firewall)
    -- TODO: support stdin
    --where readInput [] = ("<stdin>",) <$> getContents



main :: IO ()
main = do 
    cmdArgs <- getRecord "Test program"
    --print (cmdArgs::CommandLineArgs)
    (ipassmt, (srcname, src)) <- readArgs cmdArgs
    
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
            unfolded <- loadUnfoldedRuleset verbose "filter" "FORWARD" res
            putStrLn "== unfolded FORWARD chain (upper closure) =="
            putStrLn $ L.intercalate "\n" $ map show (Isabelle.upper_closure $ unfolded)
            putStrLn "== to simple firewall =="
            putStrLn $ L.intercalate "\n" $ map show (Analysis.toSimpleFirewall unfolded)
            putStrLn "== to even-simpler firewall =="
            let upper_simple = Analysis.toSimpleFirewallWithoutInterfaces ipassmt unfolded
            putStrLn $ L.intercalate "\n" $ map show upper_simple
            putStrLn "== checking spoofing protection =="
            let (warnings, spoofResult) = certifySpoofingProtection ipassmt unfolded
            mapM_ putStrLn warnings
            mapM_ (putStrLn . show) spoofResult
            putStrLn "== calculating service matrices =="
            putStrLn "===========SSH========="
            putStrLn $ showServiceMatrix $ Isabelle.access_matrix_pretty Isabelle.parts_connection_ssh upper_simple
            putStrLn "===========HTTP========="
            putStrLn $ showServiceMatrix $ Isabelle.access_matrix_pretty Isabelle.parts_connection_http upper_simple
        where showServiceMatrix (nodes, vertices) = concat (map (\(n, desc) -> n ++ " |-> " ++ desc ++ "\n") nodes) ++ "\n" ++
                                                    concat (map (\v -> show v ++ "\n") vertices)


