module LambdaPi.Printer where

import Text.PrettyPrint.HughesPJ hiding (parens)

import Common
import LambdaPi.AST

iPrint :: Int -> Int -> ITerm -> Doc
iPrint p ii (Ann c ty) =
  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> cPrint 0 ii ty)
iPrint p ii Star =
  text "*"
iPrint p ii (Pi d (Inf (Pi d' r))) =
  parensIf (p > 0) (nestedForall (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint p ii (Pi d r) =
  let param =
        text (vars !! ii) <>
        text " :: " <>
        cPrint 0 ii d
  in
    parensIf (p > 0) (sep [ text "forall " <> param <> text " .", cPrint 0 (ii + 1) r ])
iPrint p ii (Bound k) =
  text (vars !! (ii - k - 1))
iPrint p ii (Free (Global s)) =
  text s
iPrint p ii (App i c) =
  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii x =
  text ("[" ++ show x ++ "]")

cPrint :: Int -> Int -> CTerm -> Doc
cPrint p ii (Inf i) =
  iPrint p ii i
cPrint p ii (Lam c) =
  parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)

nestedForall :: Int -> [(Int, CTerm)] -> CTerm -> Doc
nestedForall ii ds (Inf (Pi d r)) =
  nestedForall (ii + 1) ((ii, d) : ds) r
nestedForall ii ds x =
  let params =
        sep [ parensIf True (text (vars !! n) <> text " :: " <> cPrint 0 n d)
            | (n, d) <- reverse ds
            ]
  in
    sep [ text "forall " <> params <> text " .", cPrint 0 ii x ]
