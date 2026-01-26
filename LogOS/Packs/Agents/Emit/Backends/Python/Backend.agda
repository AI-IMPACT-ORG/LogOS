{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.Backends.Python.Backend where

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)
open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax as Py

pythonBackend : Backend
pythonBackend =
  record
    { Expr = Py.PyExpr
    ; Arg = Py.PyArg
    ; Slice = Py.PySlice
    ; Target = Py.PyTarget
    ; Stmt = Py.PyStmt
    ; Module = Py.PyModule
    ; raw = Py.pyRaw
    ; var = Py.pyVar
    ; stringLit = Py.pyString
    ; attr = Py.pyAttr
    ; call = Py.pyCall
    ; binOp = Py.pyBinOp
    ; index = Py.pyIndex
    ; tuple = Py.pyTuple
    ; subscript = Py.pySubscript
    ; argPos = Py.pyPos
    ; argKw = Py.pyKw
    ; slice = Py.pySlice
    ; sliceIndex = Py.pySliceIndex
    ; targetName = Py.targetName
    ; targetTuple = Py.targetTuple
    ; blank = Py.pyBlank
    ; comment = Py.pyComment
    ; importAs = Py.pyImportAs
    ; assign = Py.pyAssign
    ; assignExpr = Py.pyAssignExpr
    ; exprStmt = Py.pyExprStmt
    ; return = Py.pyReturn
    ; def = Py.pyDef
    ; forIn = Py.pyForIn
    ; withAs = Py.pyWithAs
    ; ifStmt = Py.pyIfElse
    ; mkModule = Py.pyModule
    ; renderModule = Py.renderModule
    }
