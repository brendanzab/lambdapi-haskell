module LambdaPi.Eval where

import Common
import LambdaPi.AST

cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval (Inf ii) d =
  iEval ii d
cEval (Lam c) d =
  VLam (\x -> cEval c (((\(e, d) -> (e, (x : d))) d)))

iEval :: ITerm -> (NameEnv Value,Env) -> Value
iEval (Ann c _) d =
  cEval c d
iEval Star d =
  VStar
iEval (Pi ty ty1) d =
  VPi (cEval ty d) (\x -> cEval ty1 (((\(e, d) -> (e, (x : d))) d)))
iEval (Free x) d =
  case lookup x (fst d) of
    Just v -> v
    Nothing -> (vfree x)
iEval (Bound ii) d =
  (snd d) !! ii
iEval (App i c) d =
  vapp (iEval i d) (cEval c d)
