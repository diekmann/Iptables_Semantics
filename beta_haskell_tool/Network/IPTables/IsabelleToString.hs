module Network.IPTables.IsabelleToString where

import           Data.List (intercalate)
import qualified Network.IPTables.Generated as Isabelle


instance Show a => Show (Isabelle.Negation_type a) where
    show (Isabelle.Pos x) = "Pos " ++ show x
    show (Isabelle.Neg x) = "Neg " ++ show x

instance Show Isabelle.Nat where
    show (Isabelle.Nat n) = "Nat " ++ show n

instance Show Isabelle.Common_primitive where
    show = Isabelle.common_primitive_toString

instance Show Isabelle.Action where
    show = Isabelle.action_toString
    
instance Show Isabelle.Simple_rule where
    show = Isabelle.simple_rule_toString

instance Show Isabelle.Iface where
    show (Isabelle.Iface i) = i

instance Show Isabelle.Ipt_ipv4range where
  show (Isabelle.Ip4Addr ip) = "Ip4Addr " ++ showIP ip
  show (Isabelle.Ip4AddrNetmask ip (Isabelle.Nat n)) =
          "Ip4AddrNetmask " ++ showIP ip ++ "/" ++ show n
  show (Isabelle.Ip4AddrRange ip1 ip2) =
           "Ip4AddrRange " ++ showIP ip1 ++ "-" ++ showIP ip2

showIP (Isabelle.Nat a, (Isabelle.Nat b, (Isabelle.Nat c, Isabelle.Nat d))) =
        intercalate "." [show a, show b, show c, show d]

instance Show a => Show (Isabelle.Match_expr a) where
    --show = Isabelle.common_primitive_match_expr_toString -- TODO if we could fix the type, we could reuse this
    show (Isabelle.MatchAny) = ""
    show (Isabelle.Match a) = show a
    show (Isabelle.MatchNot (Isabelle.Match a)) = "! " ++ show a
    show (Isabelle.MatchNot m) = "! (" ++ show m ++ ")"
    show (Isabelle.MatchAnd m1 m2) = show m1 ++ " " ++ show m2

instance Show a => Show (Isabelle.Rule a) where
    show (Isabelle.Rule m a) = "(" ++ show m ++ ", " ++ show a ++ ")"
    
