module Coercion where

f :: Monad a => (a () -> a ()) -> (a () -> a ())
f = fmap id

g :: Functor m => m () -> m ()
g x = x

h :: Monad m => m () -> m ()
h x = g x
