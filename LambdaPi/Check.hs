module LambdaPi.Check where

import Control.Monad.Except

import Text.PrettyPrint.HughesPJ hiding (parens)

import Common
import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Quote
import LambdaPi.Printer

iType0 :: (NameEnv Value,Context) -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> (NameEnv Value,Context) -> ITerm -> Result Type
iType ii g (Ann e tyt )
  =     do  cType  ii g tyt VStar
            let ty = cEval tyt (fst g, [])
            cType ii g e ty
            return ty
iType ii g Star
   =  return VStar
iType ii g (Pi tyt tyt')
   =  do  cType ii g tyt VStar
          let ty = cEval tyt (fst g, [])
          cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                    (cSubst 0 (Free (Local ii)) tyt') VStar
          return VStar
iType ii g (Free x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint 0 0 (Free x)))
iType ii g (e1 :$: e2)
  =     do  si <- iType ii g e1
            case si of
              VPi  ty ty1  ->  do  cType ii g e2 ty
                                    return ( ty1 (cEval e2 (fst g, [])))
              _                  ->  throwError "illegal application"
iType ii g Nat                  =  return VStar
iType ii g (NatElim m mz ms n)  =
  do  cType ii g m (VPi VNat (const VStar))
      let mVal  = cEval m (fst g, [])
      cType ii g mz (mVal `vapp` VZero)
      cType ii g ms (VPi VNat (\ k -> VPi (mVal `vapp` k) (\ _ -> mVal `vapp` VSucc k)))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      return (mVal `vapp` nVal)
iType ii g (Vec a n) =
  do  cType ii g a  VStar
      cType ii g n  VNat
      return VStar
iType ii g (VecElim a m mn mc n vs) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      cType ii g m
        (  VPi VNat (\n -> VPi (VVec aVal n) (\ _ -> VStar)))
      let mVal = cEval m (fst g, [])
      cType ii g mn (foldl vapp mVal [VZero, VNil aVal])
      cType ii g mc
        (  VPi VNat (\ n ->
           VPi aVal (\ y ->
           VPi (VVec aVal n) (\ ys ->
           VPi (foldl vapp mVal [n, ys]) (\ _ ->
           (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      cType ii g vs (VVec aVal nVal)
      let vsVal = cEval vs (fst g, [])
      return (foldl vapp mVal [nVal, vsVal])
iType i g (Eq a x y) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g x aVal
      cType i g y aVal
      return VStar
iType i g (EqElim a m mr x y eq) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g m
        (VPi aVal (\ x ->
         VPi aVal (\ y ->
         VPi (VEq aVal x y) (\ _ -> VStar))))
      let mVal = cEval m (fst g, [])
      cType i g mr
        (VPi aVal (\ x ->
         foldl vapp mVal [x, x]))
      cType i g x aVal
      let xVal = cEval x (fst g, [])
      cType i g y aVal
      let yVal = cEval y (fst g, [])
      cType i g eq (VEq aVal xVal yVal)
      let eqVal = cEval eq (fst g, [])
      return (foldl vapp mVal [xVal, yVal])

cType :: Int -> (NameEnv Value,Context) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v
  =     do  v' <- iType ii g e
            unless ( quote0 v == quote0 v') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint 0 0 (quote0 v')) ++ "\n" ++ "type expected:  " ++ render (cPrint 0 0 (quote0 v)) ++ "\n" ++ "for expression: " ++ render (iPrint 0 0 e)))
cType ii g (Lam e) ( VPi ty ty')
  =     cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty ) : g))) g)
                (cSubst 0 (Free (Local ii)) e) ( ty' (vfree (Local ii)))
cType ii g Zero      VNat  =  return ()
cType ii g (Succ k)  VNat  =  cType ii g k VNat
cType ii g (Nil a) (VVec bVal VZero) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
cType ii g (Cons a n x xs) (VVec bVal (VSucc k)) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      unless  (quote0 nVal == quote0 k)
              (throwError "number mismatch")
      cType ii g x aVal
      cType ii g xs (VVec bVal k)
cType ii g (Refl a z) (VEq bVal xVal yVal) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g z aVal
      let zVal = cEval z (fst g, [])
      unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
              (throwError "type mismatch")
cType ii g _ _
  =     throwError "type mismatch"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i'   (Ann c c')     =  Ann (cSubst ii i' c) (cSubst ii i' c')

iSubst ii r  Star           =  Star
iSubst ii r  (Pi ty ty')    =  Pi  (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j)      =  if ii == j then i' else Bound j
iSubst ii i' (Free y)       =  Free y
iSubst ii i' (i :$: c)       =  (iSubst ii i' i) :$: (cSubst ii i' c)
iSubst ii r  Nat            =  Nat
iSubst ii r  (NatElim m mz ms n)
                              =  NatElim (cSubst ii r m)
                                          (cSubst ii r mz) (cSubst ii r ms)
                                          (cSubst ii r ms)
iSubst ii r  (Vec a n)      =  Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r  (VecElim a m mn mc n xs)
                              =  VecElim (cSubst ii r a) (cSubst ii r m)
                                          (cSubst ii r mn) (cSubst ii r mc)
                                          (cSubst ii r n) (cSubst ii r xs)
iSubst ii r  (Eq a x y)     =  Eq (cSubst ii r a)
                                     (cSubst ii r x) (cSubst ii r y)
iSubst ii r  (EqElim a m mr x y eq)
                              =  VecElim (cSubst ii r a) (cSubst ii r m)
                                          (cSubst ii r mr) (cSubst ii r x)
                                          (cSubst ii r y) (cSubst ii r eq)
iSubst ii r  (Fin n)        =  Fin (cSubst ii r n)
iSubst ii r  (FinElim m mz ms n f)
                              =  FinElim (cSubst ii r m)
                                          (cSubst ii r mz) (cSubst ii r ms)
                                          (cSubst ii r n) (cSubst ii r f)
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)      =  Inf (iSubst ii i' i)
cSubst ii i' (Lam c)      =  Lam (cSubst (ii + 1) i' c)
cSubst ii r  Zero         =  Zero
cSubst ii r  (Succ n)     =  Succ (cSubst ii r n)
cSubst ii r  (Nil a)      =  Nil (cSubst ii r a)
cSubst ii r  (Cons a n x xs)
                            =  Cons (cSubst ii r a) (cSubst ii r x)
                                     (cSubst ii r x) (cSubst ii r xs)
cSubst ii r  (Refl a x)   =  Refl (cSubst ii r a) (cSubst ii r x)
cSubst ii r  (FZero n)    =  FZero (cSubst ii r n)
cSubst ii r  (FSucc n k)  =  FSucc (cSubst ii r n) (cSubst ii r k)
