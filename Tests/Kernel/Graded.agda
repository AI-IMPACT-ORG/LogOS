{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.Kernel.Graded where

open import LogOS.Prelude
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth

open GuardedCore {ℓ = lzero}

-- Tiny sanity check: build a trivial graded closure and forget the grading.

CP : ConPreorder lzero
CP =
  record
    { Con   = ⊤
    ; _⊑_   = λ _ _ → ⊤
    ; refl  = λ {c} → tt
    ; trans = λ _ _ → tt
    }

Q : QAdapter lzero
Q = trivialQAdapter

G : GradedClosure Q CP
G =
  record
    { Flow       = λ _ c → c
    ; mono       = λ {g} {c} {c'} le → le
    ; mono-grade = λ _ _ → tt
    ; comp-lax   = λ _ _ _ → tt
    ; sat        = tt
    ; sat-top    = λ _ → tt
    ; infl-sat   = λ _ → tt
    ; idemp-sat  = λ _ → tt
    ; Th*        = tt
    ; Th*-fixed  = tt , tt
    }

U : GuardedClosure CP
U = forgetGradedClosure G
