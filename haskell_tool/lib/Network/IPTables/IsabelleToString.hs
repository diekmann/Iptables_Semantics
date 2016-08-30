{-# Language FlexibleInstances #-}
module Network.IPTables.IsabelleToString where

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
    show = Isabelle.common_primitive_ipv4_toString
instance Show (Isabelle.Common_primitive Word128) where
    show = Isabelle.common_primitive_ipv6_toString

instance Show Isabelle.Action where
    show = Isabelle.action_toString

instance Show (Isabelle.Simple_rule Word32) where
    show = Isabelle.simple_rule_ipv4_toString
instance Show (Isabelle.Simple_rule Word128) where
    show = Isabelle.simple_rule_ipv6_toString

instance Show Isabelle.Iface where
    show (Isabelle.Iface i) = i

instance Show (Isabelle.Ipt_iprange Word32) where
  show = Isabelle.ipt_ipv4range_toString
instance Show (Isabelle.Ipt_iprange Word128) where
  show = Isabelle.ipt_ipv6range_toString

instance Show (Isabelle.Match_expr (Isabelle.Common_primitive Word32)) where
    show = Isabelle.common_primitive_match_expr_ipv4_toString
instance Show (Isabelle.Match_expr (Isabelle.Common_primitive Word128)) where
    show = Isabelle.common_primitive_match_expr_ipv6_toString

instance Show (Isabelle.Rule (Isabelle.Common_primitive Word32)) where
    --TODO: unify with Isabelle.common_primitive_rule_toString
    show (Isabelle.Rule m a) = "(" ++ show m ++ ", " ++ show a ++ ")"
instance Show (Isabelle.Rule (Isabelle.Common_primitive Word128)) where
    --TODO: unify with Isabelle.common_primitive_rule_toString
    show (Isabelle.Rule m a) = "(" ++ show m ++ ", " ++ show a ++ ")"    

{- I'm hesitant to make an instance (Show (Isabelle.Word Word32)), there may be other things than IP addresses -}
instance Show (Isabelle.Prefix_match Word32) where
    show = Isabelle.prefix_match_32_toString
instance Show (Isabelle.Routing_rule_ext Word32 ()) where 
    show = Isabelle.routing_rule_32_toString 
instance Show (Isabelle.Routing_rule_ext Word128 ()) where 
    show = Isabelle.routing_rule_128_toString 
