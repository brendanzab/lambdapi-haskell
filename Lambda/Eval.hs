module Lambda.Eval where

import Common
import Lambda.AST

iEval :: ITerm -> (NameEnv Value, Env) -> Value
iEval (Ann  e _)    d  =  cEval e d
iEval (Free  x)     d  =  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
iEval (Bound  ii)   d  =  (snd d) !! ii
iEval (App e1 e2)   d  =  vapp (iEval e1 d) (cEval e2 d)

cEval (Inf  ii)   d  =  iEval ii d
cEval (Lam  e)    d  =  VLam (\ x -> cEval e (((\(e, d) -> (e,  (x : d))) d)))
