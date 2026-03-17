{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.Context where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)

open import LogOS.Apps.ZFC.Stack.Boundary using (SetBoundary)
import LogOS.Apps.ZFC.SetTheory.MembershipLaws as MemLaws

record SetContext {ℓ : Level} : Set (lsuc ℓ) where
  infix 4 _∈_
  field
    SetU : Set ℓ
    _∈_  : SetU → SetU → Set ℓ

  -- Shared boundary: sets-as-predicates with refinement by entailment.
  SetBnd : ConPreorder ℓ ℓ
  SetBnd = SetBoundary SetU _∈_

  -- Subset-by-membership (a derived, symmetric-friendly relation).
  open MemLaws.Laws {ℓ} {SetU} _∈_ using
    (_⊆_; _≈_; refl≈; sym≈; trans≈; mem-ext; ≡→≈)
    public
