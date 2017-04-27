{-# LANGUAGE MagicHash #-}

module Integer where

import GHC.Exts

makeInteger :: Integer
makeInteger = 42

makeIntHash :: () -> Int#
makeIntHash _ = 42#
