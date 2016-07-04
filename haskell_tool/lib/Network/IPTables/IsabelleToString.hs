{-# Language FlexibleInstances #-}
module Network.IPTables.IsabelleToString where

import           Data.List (intercalate)
import qualified Network.IPTables.Generated as Isabelle


type Word32 = Isabelle.Bit0 (Isabelle.Bit0
                              (Isabelle.Bit0 (Isabelle.Bit0 (Isabelle.Bit0 Isabelle.Num1))))

type Word128 = Isabelle.Bit0 (Isabelle.Bit0
                               (Isabelle.Bit0 (Isabelle.Bit0 (Isabelle.Bit0
                                 (Isabelle.Bit0 (Isabelle.Bit0 Isabelle.Num1))))))

instance Show a => Show (Isabelle.Negation_type a) where
    show (Isabelle.Pos x) = "Pos " ++ show x
    show (Isabelle.Neg x) = "Neg " ++ show x

instance Show Isabelle.Nat where
    show (Isabelle.Nat n) = "Nat " ++ show n

instance Show (Isabelle.Common_primitive Word32) where
    show = Isabelle.common_primitive_v4_toString

instance Show Isabelle.Action where
    show = Isabelle.action_toString

instance Show (Isabelle.Simple_rule Word32) where
    show = Isabelle.simple_rule_toString

instance Show Isabelle.Iface where
    show (Isabelle.Iface i) = i

instance Show (Isabelle.Ipt_iprange Word32) where
  show = Isabelle.ipt_ipv4range_toString

instance Show (Isabelle.Ipt_iprange Word128) where
  show = Isabelle.ipt_ipv6range_toString

instance Show (Isabelle.Match_expr (Isabelle.Common_primitive Word32)) where
    show = Isabelle.common_primitive_match_expr_toString

instance Show (Isabelle.Rule (Isabelle.Common_primitive Word32)) where
    --TODO: unify with Isabelle.common_primitive_rule_toString
    show (Isabelle.Rule m a) = "(" ++ show m ++ ", " ++ show a ++ ")"
    
