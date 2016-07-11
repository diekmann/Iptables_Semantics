{-# Language FlexibleInstances #-}
module Network.IPTables.Ipassmt
( IpAssmt(..)
, IsabelleIpAssmt
) where


import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString (Word32)


data IpAssmt a = IpAssmt [(Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])] --deriving (Show)

instance Show (IpAssmt Word32) where
    show (IpAssmt ipassmt) = show ipassmt

type IsabelleIpAssmt = [(Isabelle.Iface, [(Isabelle.Word Word32, Isabelle.Nat)])]

