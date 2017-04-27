{-# LANGUAGE MultiParamTypeClasses #-}

module Fibonacci where

class Blahable where
    f :: Int

fib :: Blahable => Int -> Int
fib 1 = 1
fib 2 = 1
fib n = (fib (n - 1)) + (fib (n - 2))
