module Main where

import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import Network.IPTables.Analysis as Analysis
import qualified Network.IPTables.Generated as Isabelle
import Network.IPTables.Main

main = main' $
    Operations
        parseIpAssmt_ipv4
        parseIptablesSave_ipv4
        Isabelle.ipassmt_generic_ipv4
        certifySpoofingProtection_ipv4
        Analysis.accessMatrix_ipv4
