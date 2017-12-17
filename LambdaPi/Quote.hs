module LambdaPi.Quote where

import Common
import LambdaPi.AST

instance Show Value where
  show = show . quote0

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t)
  =     Lam (quote (ii + 1) (t (vfree (Quote ii))))

quote ii VStar = Inf Star
quote ii (VPi v f)
    =  Inf (Pi (quote ii v) (quote (ii + 1) (f (vfree (Quote ii)))))
quote ii (VNeutral n)
  =     Inf (neutralQuote ii n)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v)
   =  boundfree ii v
neutralQuote ii (NApp n v)
   =  App (neutralQuote ii n) (quote ii v)

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k)     =  Bound ((ii - k - 1) `max` 0)
boundfree ii x             =  Free x
