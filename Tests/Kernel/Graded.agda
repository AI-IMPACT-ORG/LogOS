{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
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

CP : ConPoset lzero
CP =
  record
    { Con   = ⊤
    ; _⊑_   = λ _ _ → ⊤
    ; refl  = λ {c} → tt
    ; trans = λ _ _ → tt
    }

Q : QAdapter lzero
Q =
  record
    { Scale = ⊤
    ; _≤s_  = λ _ _ → ⊤
    ; _·_   = λ _ _ → tt
    ; e     = tt
    ; _≤p_  = λ _ _ → ⊤
    ; Time  = ⊤
    ; _+_   = λ _ _ → tt
    ; zero  = tt
    ; τ     = λ _ → tt
    }

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
