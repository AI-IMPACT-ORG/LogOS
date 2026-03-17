{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ExtensionalityLadder where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_)
open import LogOS.LT.FunPreorder using (DFunPreorder; pointwise≡→≈)
open import LogOS.Ports.Globalise using (DependentGlobalise; globaliseᵈ)

extensionality-ladder
  : ∀ {ℓI ℓOCon ℓORel : Level}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
  → (G : DependentGlobalise I (λ i → Con (O i)))
  → {F H : (i : I) → Con (O i)}
  → (eq : ∀ i → F i ≡ H i)
  → _≈_ (DFunPreorder I O) F H × F ≡ H
extensionality-ladder {O = O} G eq =
  pointwise≡→≈ {O = O} eq
  , globaliseᵈ G eq
