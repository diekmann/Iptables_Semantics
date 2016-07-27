module Main where

import Network.IPTables.Parser
import Network.IPTables.IpassmtParser
import Network.IPTables.Analysis as Analysis
import qualified Network.IPTables.Generated as Isabelle
import Network.IPTables.Main

main = main' $
    Operations
        parseIpAssmt_ipv6
        parseIptablesSave_ipv6
        Isabelle.ipassmt_generic_ipv6
        certifySpoofingProtection_ipv6
        Analysis.accessMatrix_ipv6
