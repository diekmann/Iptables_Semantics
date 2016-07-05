{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Data_Bits where {

import qualified Data.Bits;

{-
  The ...Bounded functions assume that the Integer argument for the shift 
  or bit index fits into an Int, is non-negative and (for types of fixed bit width)
  less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitUnbounded x b
  | b <= toInteger (Prelude.maxBound :: Int) = Data.Bits.testBit x (fromInteger b)
  | otherwise = error ("Bit index too large: " ++ show b)
;

testBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitBounded x b = Data.Bits.testBit x (fromInteger b);

setBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitUnbounded x n b
  | n <= toInteger (Prelude.maxBound :: Int) = 
    if b then Data.Bits.setBit x (fromInteger n) else Data.Bits.clearBit x (fromInteger n)
  | otherwise = error ("Bit index too large: " ++ show n)
;

setBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x (fromInteger n);
setBitBounded x n False = Data.Bits.clearBit x (fromInteger n);

shiftlUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftL x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftlBounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlBounded x n = Data.Bits.shiftL x (fromInteger n);

shiftrUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftrUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftR x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Integer -> a;
shiftrBounded x n = Data.Bits.shiftR x (fromInteger n);

}
