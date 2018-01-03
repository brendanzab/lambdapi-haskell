module LambdaPi.Check where

import Control.Monad.Except

import Text.PrettyPrint.HughesPJ hiding (parens)

import Common
import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Quote
import LambdaPi.Printer

iType0 :: (NameEnv Value,Context) -> ITerm -> Result Type
iType0 =
  iType 0

iType :: Int -> (NameEnv Value,Context) -> ITerm -> Result Type
iType ii g (Ann e tyt ) =
  do  cType ii g tyt VStar
      let ty = cEval tyt (fst g, [])
      cType ii g e ty
      return ty
iType ii g Star =
  return VStar
iType ii g (Pi tyt tyt') =
  do  cType ii g tyt VStar
      let ty = cEval tyt (fst g, [])
      cType (ii + 1)
            ((\(d, g) -> (d, ((Local ii, ty) : g))) g)
            (cSubst 0 (Free (Local ii)) tyt')
            VStar
      return VStar
iType ii g (Free x) =
  case lookup x (snd g) of
    Just ty ->
      return ty
    Nothing ->
      throwError ("unknown identifier: " ++ render (iPrint 0 0 (Free x)))
iType ii g (App e1 e2) =
  do  si <- iType ii g e1
      case si of
        VPi ty ty1 ->
          do  cType ii g e2 ty
              return (ty1 (cEval e2 (fst g, [])))
        _ ->
          throwError "illegal application"

cType :: Int -> (NameEnv Value, Context) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v =
  do  v' <- iType ii g e
      unless (quote0 v == quote0 v')
             (throwError ("type mismatch:\n" ++
                          "type inferred:  " ++ render (cPrint 0 0 (quote0 v')) ++ "\n" ++
                          "type expected:  " ++ render (cPrint 0 0 (quote0 v)) ++ "\n" ++
                          "for expression: " ++ render (iPrint 0 0 e)))
cType ii g (Lam e) (VPi ty ty') =
  cType (ii + 1)
        ((\(d, g) -> (d, ((Local ii, ty ) : g))) g)
        (cSubst 0 (Free (Local ii)) e) (ty' (vfree (Local ii)))
cType ii g _ _ =
  throwError "type mismatch"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') =
  Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii r  Star =
  Star
iSubst ii r (Pi ty ty') =
  Pi  (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j) =
  if ii == j then i' else Bound j
iSubst ii i' (Free y) =
  Free y
iSubst ii i' (App i c) =
  App (iSubst ii i' i) (cSubst ii i' c)

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i) =
  Inf (iSubst ii i' i)
cSubst ii i' (Lam c) =
  Lam (cSubst (ii + 1) i' c)
