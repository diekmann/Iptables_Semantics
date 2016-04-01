module Common.Util
( isParseErrorWindowsNewline
) where

import qualified Data.List as L
import qualified Text.Parsec.Error --Windows line ending debug

isParseErrorWindowsNewline :: Text.Parsec.Error.ParseError -> Bool
isParseErrorWindowsNewline err =
    case L.reverse (Text.Parsec.Error.errorMessages err) of
        (Text.Parsec.Error.Expect "\"\\n\"" : Text.Parsec.Error.SysUnExpect "\"\\r\"" : _) -> True
        _ -> False

