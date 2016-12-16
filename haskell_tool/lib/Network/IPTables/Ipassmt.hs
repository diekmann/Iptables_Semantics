{-# Language FlexibleContexts, UndecidableInstances, StandaloneDeriving #-}
module Network.IPTables.Ipassmt
( IpAssmt(..)
, IsabelleIpAssmt
, showIpAssmtDiff) where


import qualified Network.IPTables.Generated as Isabelle
import           Network.IPTables.IsabelleToString (Word32)


data IpAssmt a = IpAssmt [(Isabelle.Iface, Isabelle.Negation_type [Isabelle.Ipt_iprange a])]

deriving instance Show (Isabelle.Ipt_iprange a) => Show (IpAssmt a)

type IsabelleIpAssmt a = [(Isabelle.Iface, [(Isabelle.Word a, Isabelle.Nat)])]

showIpAssmtDiff assmt rtbl = unlines tbl 
    where
        diff = Isabelle.ipassmt_diff assmt (Isabelle.routing_ipassmt rtbl)
        show_cidr = show . uncurry Isabelle.PrefixMatch
        pfxlen = foldr max 5 . map (length . show_cidr) . concat . uncurry (++) . unzip . map snd $ diff
        iftitle = "Interface"
        iflen = foldr max (length iftitle) . map (length . show . fst) $ diff
        nrep n = take n . repeat
        nminu = flip nrep '-'
        nspc = flip nrep ' '
        brd = " | "
        hline = nminu (iflen + 1) ++ "+" ++ nminu (pfxlen + 2) ++ "+" ++ nminu (pfxlen + 1)
        tline a b c = a ++ brd ++ b ++ brd ++ c
        alil n s = s ++ nspc (n - length s)
        alir n s = nspc (n - length s) ++ s
        aliif = alil iflen
        alipfx = alir pfxlen
        headl = aliif iftitle ++ brd ++ alil pfxlen "a - b" ++ brd ++ alil pfxlen "b - a"
        eldiff (a,(b,c)) =
            let l = max (length b) (length c); s = (++ repeat (nspc pfxlen)) . map (alipfx . show_cidr)
            in (,) l (aliif (show a) : repeat (nspc iflen), s b, s c)
        sdiff a = take (max a 1) . uncurry3 (zipWith3 tline)
        tbl = ([headl, hline] ++) . concat . map (uncurry sdiff . eldiff) $ diff

uncurry3 f (a,b,c) = f a b c
