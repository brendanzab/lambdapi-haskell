module LambdaPi.AST where

import Common

data CTerm
   =  Inf  ITerm
   |  Lam  CTerm
   |  Zero
   |  Succ CTerm
   |  Nil CTerm
   |  Cons CTerm CTerm CTerm CTerm
   |  Refl CTerm CTerm
   |  FZero CTerm
   |  FSucc CTerm CTerm
  deriving (Show, Eq)
data ITerm
   =  Ann CTerm CTerm
   |  Star
   |  Pi CTerm CTerm
   |  Bound  Int
   |  Free  Name
   |  App ITerm CTerm
   |  Nat
   |  NatElim CTerm CTerm CTerm CTerm
   |  Vec CTerm CTerm
   |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Eq CTerm CTerm CTerm
   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Fin CTerm
   |  FinElim CTerm CTerm CTerm CTerm CTerm
  deriving (Show, Eq)

data Value
   =  VLam  (Value -> Value)
   |  VStar
   |  VPi Value (Value -> Value)
   |  VNeutral Neutral
   |  VNat
   |  VZero
   |  VSucc Value
   |  VNil Value
   |  VCons Value Value Value Value
   |  VVec Value Value
   |  VEq Value Value Value
   |  VRefl Value Value
   |  VFZero Value
   |  VFSucc Value Value
   |  VFin Value
data Neutral
   =  NFree  Name
   |  NApp  Neutral Value
   |  NNatElim Value Value Value Neutral
   |  NVecElim Value Value Value Value Value Neutral
   |  NEqElim Value Value Value Value Value Neutral
   |  NFinElim Value Value Value Value Neutral
type Env = [Value]
type Type     =  Value
type Context    =  [(Name, Type)]


vapp :: Value -> Value -> Value
vapp (VLam f)      v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)
