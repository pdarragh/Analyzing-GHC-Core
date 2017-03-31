module FFITest where

foreign import ccall "exp" c_exp :: Double -> Double

test :: (Int -> Int) -> (Int -> Int) -> Int -> Int
test f g x = f (g x)


main :: IO ()
main = return ()

-- rm -f FFITest.o && stack ghc FFITest.hs -- -ddump-simpl -dshow-passes -dppr-debug -dsuppress-module-prefixes
