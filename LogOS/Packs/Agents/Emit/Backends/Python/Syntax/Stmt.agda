{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Stmt where

open import LogOS.Prelude.List using (List; []; _∷_; _++_)
open import LogOS.Prelude.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.String using (String; _++s_; intercalateS)

open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Expr using (PyExpr; renderExpr)

data PyTarget : Set where
  targetName : String → PyTarget
  targetTuple : List String → PyTarget

data PyStmt : Set where
  blank : PyStmt
  comment : String → PyStmt
  importAs : String → String → PyStmt
  assign : String → PyExpr → PyStmt
  assignExpr : PyExpr → PyExpr → PyStmt
  exprStmt : PyExpr → PyStmt
  return : PyExpr → PyStmt
  def : String → List String → List PyStmt → PyStmt
  forIn : PyTarget → PyExpr → List PyStmt → PyStmt
  withAs : PyExpr → String → List PyStmt → PyStmt
  ifStmt : PyExpr → List PyStmt → List PyStmt → PyStmt

indentUnit : String
indentUnit = "    "

repeatS : ℕ → String → String
repeatS zero _ = ""
repeatS (suc n) s = s ++s repeatS n s

indent : ℕ → String → String
indent n s = repeatS n indentUnit ++s s

renderTarget : PyTarget → String
renderTarget (targetName name) = name
renderTarget (targetTuple []) = "()"
renderTarget (targetTuple (x ∷ [])) = "(" ++s x ++s ",)"
renderTarget (targetTuple (x ∷ y ∷ xs)) =
  "(" ++s intercalateS ", " (x ∷ y ∷ xs) ++s ")"

mutual
  renderStmtsLines : ℕ → List PyStmt → List String
  renderStmtsLines _ [] = []
  renderStmtsLines n (s ∷ ss) = renderStmtLines n s ++ renderStmtsLines n ss

  renderStmtLines : ℕ → PyStmt → List String
  renderStmtLines _ blank = "" ∷ []
  renderStmtLines n (comment s) = indent n ("# " ++s s) ∷ []
  renderStmtLines n (importAs mod alias) =
    indent n ("import " ++s mod ++s " as " ++s alias) ∷ []
  renderStmtLines n (assign name expr) =
    indent n (name ++s " = " ++s renderExpr expr) ∷ []
  renderStmtLines n (assignExpr target expr) =
    indent n (renderExpr target ++s " = " ++s renderExpr expr) ∷ []
  renderStmtLines n (exprStmt expr) = indent n (renderExpr expr) ∷ []
  renderStmtLines n (return expr) = indent n ("return " ++s renderExpr expr) ∷ []
  renderStmtLines n (def name params body) =
    indent n ("def " ++s name ++s "(" ++s intercalateS ", " params ++s "):")
      ∷ renderStmtsLines (suc n) body
  renderStmtLines n (forIn target iter body) =
    indent n ("for " ++s renderTarget target ++s " in " ++s renderExpr iter ++s ":")
      ∷ renderStmtsLines (suc n) body
  renderStmtLines n (withAs expr name body) =
    indent n ("with " ++s renderExpr expr ++s " as " ++s name ++s ":")
      ∷ renderStmtsLines (suc n) body
  renderStmtLines n (ifStmt cond thenBody elseBody) =
    indent n ("if " ++s renderExpr cond ++s ":")
      ∷ renderStmtsLines (suc n) thenBody
        ++ renderElse n elseBody
    where
      renderElse : ℕ → List PyStmt → List String
      renderElse _ [] = []
      renderElse k (b ∷ bs) =
        indent k "else:" ∷ renderStmtsLines (suc k) (b ∷ bs)
