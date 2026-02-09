{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.String where

-- Bridge to Agda built-in strings to avoid duplicate BUILTIN bindings.

open import Agda.Builtin.String public using
  (String; primStringAppend; primShowString; primShowNat)
open import LogOS.Host.List using (List; []; _∷_)
open import LogOS.Host.Nat using (ℕ)

infixr 5 _++s_
_++s_ : String → String → String
_++s_ = primStringAppend

concatS : List String → String
concatS [] = ""
concatS (x ∷ xs) = x ++s concatS xs

intercalateS : String → List String → String
intercalateS _ [] = ""
intercalateS sep (x ∷ xs) = x ++s go xs
  where
    go : List String → String
    go [] = ""
    go (y ∷ ys) = sep ++s y ++s go ys

showString : String → String
showString = primShowString

showNat : ℕ → String
showNat = primShowNat

