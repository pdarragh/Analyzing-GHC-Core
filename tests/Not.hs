module Not where

foo :: Bool
foo = let x = not x in x

bar :: Int
bar = if foo
    then 3
    else 9
