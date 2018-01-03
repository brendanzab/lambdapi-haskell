module LambdaPi.AST where

import Common

data CTerm
  = Inf ITerm
  | Lam CTerm
  deriving (Show, Eq)

data ITerm
  = Ann CTerm CTerm
  | Star
  | Pi CTerm CTerm
  | Bound Int
  | Free Name
  | App ITerm CTerm
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

type Env = [Value]
type Type = Value
type Context = [(Name, Type)]

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)
