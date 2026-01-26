{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Emit.Backends.Python.Syntax.Expr where

open import LogOS.Prelude.List using (List; []; _∷_; _++_)
open import LogOS.Prelude.Maybe using (Maybe; nothing; just)
open import LogOS.Prelude.String using (String; _++s_; intercalateS; showString)

mutual
  data PyExpr : Set where
    raw : String → PyExpr
    var : String → PyExpr
    stringLit : String → PyExpr
    attr : PyExpr → String → PyExpr
    call : PyExpr → List PyArg → PyExpr
    binOp : String → PyExpr → PyExpr → PyExpr
    index : PyExpr → PyExpr → PyExpr
    tuple : List PyExpr → PyExpr
    subscript : PyExpr → List PySlice → PyExpr

  data PyArg : Set where
    pos : PyExpr → PyArg
    kw : String → PyExpr → PyArg

  data PySlice : Set where
    slice : Maybe PyExpr → Maybe PyExpr → PySlice
    sliceIndex : PyExpr → PySlice

mutual
  renderExpr : PyExpr → String
  renderExpr (raw s) = s
  renderExpr (var s) = s
  renderExpr (stringLit s) = showString s
  renderExpr (attr e name) = renderExpr e ++s "." ++s name
  renderExpr (call f args) =
    renderExpr f ++s "(" ++s renderArgs args ++s ")"
    where
      renderArg : PyArg → String
      renderArg (pos e) = renderExpr e
      renderArg (kw name e) = name ++s "=" ++s renderExpr e

      renderArgList : List PyArg → List String
      renderArgList [] = []
      renderArgList (x ∷ xs) = renderArg x ∷ renderArgList xs

      renderArgs : List PyArg → String
      renderArgs xs = intercalateS ", " (renderArgList xs)
  renderExpr (binOp op a b) =
    renderExpr a ++s " " ++s op ++s " " ++s renderExpr b
  renderExpr (index e i) = renderExpr e ++s "[" ++s renderExpr i ++s "]"
  renderExpr (tuple es) = tupleString es
  renderExpr (subscript e slices) =
    renderExpr e ++s "[" ++s renderSlices slices ++s "]"
    where
      renderMaybe : Maybe PyExpr → String
      renderMaybe nothing = ""
      renderMaybe (just expr) = renderExpr expr

      renderSlice : PySlice → String
      renderSlice (slice start end) =
        renderMaybe start ++s ":" ++s renderMaybe end
      renderSlice (sliceIndex expr) = renderExpr expr

      renderSliceList : List PySlice → List String
      renderSliceList [] = []
      renderSliceList (s ∷ ss) = renderSlice s ∷ renderSliceList ss

      renderSlices : List PySlice → String
      renderSlices [] = ""
      renderSlices (s ∷ ss) =
        intercalateS ", " (renderSlice s ∷ renderSliceList ss)

  renderExprList : List PyExpr → List String
  renderExprList [] = []
  renderExprList (x ∷ xs) = renderExpr x ∷ renderExprList xs

  tupleString : List PyExpr → String
  tupleString [] = "()"
  tupleString (x ∷ []) = "(" ++s renderExpr x ++s ",)"
  tupleString (x ∷ y ∷ xs) =
    "(" ++s intercalateS ", " (renderExprList (x ∷ y ∷ xs)) ++s ")"
