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
quote ii VNat       =  Inf Nat
quote ii VZero      =  Zero
quote ii (VSucc n)  =  Succ (quote ii n)
quote ii (VVec a n)         =  Inf (Vec (quote ii a) (quote ii n))
quote ii (VNil a)           =  Nil (quote ii a)
quote ii (VCons a n x xs)   =  Cons  (quote ii a) (quote ii n)
                                        (quote ii x) (quote ii xs)
quote ii (VEq a x y)  =  Inf (Eq (quote ii a) (quote ii x) (quote ii y))
quote ii (VRefl a x)  =  Refl (quote ii a) (quote ii x)
quote ii (VFin n)           =  Inf (Fin (quote ii n))
quote ii (VFZero n)         =  FZero (quote ii n)
quote ii (VFSucc n f)       =  FSucc  (quote ii n) (quote ii f)
neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v)
   =  boundfree ii v
neutralQuote ii (NApp n v)
   =  App (neutralQuote ii n) (quote ii v)
neutralQuote ii (NNatElim m z s n)
   =  NatElim (quote ii m) (quote ii z) (quote ii s) (Inf (neutralQuote ii n))
neutralQuote ii (NVecElim a m mn mc n xs)
   =  VecElim (quote ii a) (quote ii m)
               (quote ii mn) (quote ii mc)
               (quote ii n) (Inf (neutralQuote ii xs))
neutralQuote ii (NEqElim a m mr x y eq)
   =  EqElim  (quote ii a) (quote ii m) (quote ii mr)
               (quote ii x) (quote ii y)
               (Inf (neutralQuote ii eq))
neutralQuote ii (NFinElim m mz ms n f)
   =  FinElim (quote ii m)
               (quote ii mz) (quote ii ms)
               (quote ii n) (Inf (neutralQuote ii f))

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k)     =  Bound ((ii - k - 1) `max` 0)
boundfree ii x             =  Free x
