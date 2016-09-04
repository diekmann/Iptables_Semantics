{-# Language FlexibleContexts, UndecidableInstances, StandaloneDeriving #-}
module Network.IPTables.Ipassmt
( IpAssmt(..)
, IsabelleIpAssmt) where


import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString (Word32)


data IpAssmt a = IpAssmt [(Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])]

deriving instance Show (Isabelle.Ipt_iprange a) => Show (IpAssmt a)

type IsabelleIpAssmt a = [(Isabelle.Iface, [(Isabelle.Word a, Isabelle.Nat)])]

