{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Builder where

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.Maybe using (Maybe; nothing; just)
open import LogOS.Prelude.String using (String)

open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Expr
  using (PyExpr; PyArg; PySlice; raw; var; stringLit; attr; call; binOp; index; tuple; subscript; pos; kw; slice; sliceIndex)
open import LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Stmt
  using (PyStmt; PyTarget; blank; comment; importAs; assign; assignExpr; exprStmt; return; def; forIn; withAs; ifStmt)

pyRaw : String → PyExpr
pyRaw = raw

pyVar : String → PyExpr
pyVar = var

pyString : String → PyExpr
pyString = stringLit

pyTrue : PyExpr
pyTrue = raw "True"

pyFalse : PyExpr
pyFalse = raw "False"

pyBool : Bool → PyExpr
pyBool true = pyTrue
pyBool false = pyFalse

pyAttr : PyExpr → String → PyExpr
pyAttr = attr

pyCall : PyExpr → List PyArg → PyExpr
pyCall = call

pyBinOp : String → PyExpr → PyExpr → PyExpr
pyBinOp = binOp

pyIndex : PyExpr → PyExpr → PyExpr
pyIndex = index

pyTuple : List PyExpr → PyExpr
pyTuple = tuple

pySubscript : PyExpr → List PySlice → PyExpr
pySubscript = subscript

pySlice : Maybe PyExpr → Maybe PyExpr → PySlice
pySlice = slice

pySliceIndex : PyExpr → PySlice
pySliceIndex = sliceIndex

pySliceFull : PySlice
pySliceFull = slice nothing nothing

pySliceFrom : PyExpr → PySlice
pySliceFrom start = slice (just start) nothing

pySliceTo : PyExpr → PySlice
pySliceTo end = slice nothing (just end)

pySliceRange : PyExpr → PyExpr → PySlice
pySliceRange start end = slice (just start) (just end)

pyPos : PyExpr → PyArg
pyPos = pos

pyKw : String → PyExpr → PyArg
pyKw = kw

pyCall0 : PyExpr → PyExpr
pyCall0 f = call f []

pyCall1 : PyExpr → PyExpr → PyExpr
pyCall1 f a = call f (pos a ∷ [])

pyCall2 : PyExpr → PyExpr → PyExpr → PyExpr
pyCall2 f a b = call f (pos a ∷ pos b ∷ [])

pyCall3 : PyExpr → PyExpr → PyExpr → PyExpr → PyExpr
pyCall3 f a b c = call f (pos a ∷ pos b ∷ pos c ∷ [])

pyBlank : PyStmt
pyBlank = blank

pyComment : String → PyStmt
pyComment = comment

pyImportAs : String → String → PyStmt
pyImportAs = importAs

pyAssign : String → PyExpr → PyStmt
pyAssign = assign

pyAssignExpr : PyExpr → PyExpr → PyStmt
pyAssignExpr = assignExpr

pyExprStmt : PyExpr → PyStmt
pyExprStmt = exprStmt

pyReturn : PyExpr → PyStmt
pyReturn = return

pyDef : String → List String → List PyStmt → PyStmt
pyDef = def

pyForIn : PyTarget → PyExpr → List PyStmt → PyStmt
pyForIn = forIn

pyWithAs : PyExpr → String → List PyStmt → PyStmt
pyWithAs = withAs

pyIf : PyExpr → List PyStmt → PyStmt
pyIf cond thenBody = ifStmt cond thenBody []

pyIfElse : PyExpr → List PyStmt → List PyStmt → PyStmt
pyIfElse = ifStmt

pyPrint1 : PyExpr → PyStmt
pyPrint1 value = exprStmt (call (var "print") (pos value ∷ []))

pyPrint2 : PyExpr → PyExpr → PyStmt
pyPrint2 label value = exprStmt (call (var "print") (pos label ∷ pos value ∷ []))

licenseHeader : List PyStmt
licenseHeader =
  pyComment "LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning"
  ∷ pyComment "Copyright (C) 2026 AI.IMPACT GmbH"
  ∷ pyComment "SPDX-License-Identifier: GPL-3.0-only"
  ∷ pyBlank
  ∷ []
