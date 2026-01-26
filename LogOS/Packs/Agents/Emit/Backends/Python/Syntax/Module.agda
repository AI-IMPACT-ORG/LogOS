{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Module where

open import LogOS.Prelude.List using (List)
open import LogOS.Prelude.String using (String; intercalateS)

open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Stmt using (PyStmt; renderStmtsLines)

record PyModule : Set where
  constructor pyModule
  field
    stmts : List PyStmt

renderModule : PyModule → String
renderModule m =
  intercalateS "\n" (renderStmtsLines 0 (PyModule.stmts m))
