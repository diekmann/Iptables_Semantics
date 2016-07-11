{-# Language FlexibleContexts #-}
{-# Language UndecidableInstances #-}
module Network.IPTables.Ipassmt
( IpAssmt(..)
, IsabelleIpAssmt
) where


import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString (Word32)


data IpAssmt a = IpAssmt [(Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])]

instance Show (Isabelle.Ipt_iprange a) => Show (IpAssmt a) where
    show (IpAssmt ipassmt) = "IpAssmt " ++ show ipassmt

type IsabelleIpAssmt a = [(Isabelle.Iface, [(Isabelle.Word a, Isabelle.Nat)])]

