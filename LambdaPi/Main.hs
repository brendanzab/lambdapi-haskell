module LambdaPi.Main where

import Common
import REPL

import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Check
import LambdaPi.Quote
import LambdaPi.Parser
import LambdaPi.Printer

lpte :: Ctx Value
lpte = []

lpve :: Ctx Value
lpve = []

lpassume state@(inter, out, ve, te) x t =
  -- x: String, t: CTerm
  check lp state x (Ann t (Inf Star))
        (\(y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint 0 0 (quote0 v))))
        (\(y, v) -> (inter, out, ve, (Global x, v) : te))

lp :: Interpreter ITerm CTerm Value Value CTerm Value
lp = I { iname = "lambda-Pi"
       , iprompt = "LP> "
       , iitype = \v c -> iType 0 (v, c)
       , iquote = quote0
       , ieval = \e x -> iEval x (e, [])
       , ihastype = id
       , icprint = cPrint 0 0
       , itprint = cPrint 0 0 . quote0
       , iiparse = parseITerm 0 []
       , isparse = parseStmt []
       , iassume = \s (x, t) -> lpassume s x t
       }

repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)

main :: IO ()
main = repLP True
