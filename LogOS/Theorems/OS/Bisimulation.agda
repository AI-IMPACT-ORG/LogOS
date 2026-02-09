{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.Bisimulation where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Kernel.Eq using (module ForKernel)
open import LogOS.Theorems.Boundary.Reflection as BR

-- “Full bisimulation” in the most LogOS-native OS sense:
-- bisimulation is *boundary observational equality*.
--
-- This avoids inventing an internal small-step relation: LogOS is an open system,
-- so the only behaviour that matters is what the explicit boundary can observe.
--
-- This module also exposes the basic implication:
-- propositional equality of decoded constraints implies bisimilarity.
--
-- Stronger “full abstraction” statements (upgrading observational equality to
-- propositional equality, or relating it to preorder antisymmetry) require
-- additional extensionality/completeness hypotheses and are stated elsewhere.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) where
  open Kernel K
  open ForKernel K using (_≃K_)

  -- Bisimulation on codes (by definition, boundary observational equality).
  Bisim : Code → Code → Set ℓ
  Bisim = BR._≈∂_ K

  bisim-refl : ∀ γ → Bisim γ γ
  bisim-refl γ = BR.≃K→≈∂ K refl

  bisim-sym : ∀ {γ δ} → Bisim γ δ → Bisim δ γ
  bisim-sym (gd , dg) = (dg , gd)

  bisim-trans : ∀ {γ δ ε} → Bisim γ δ → Bisim δ ε → Bisim γ ε
  bisim-trans (gd , dg) (de , ed) =
    ( (λ p satγ → de p (gd p satγ))
    , (λ p satε → dg p (ed p satε))
    )

  ≃K→bisim : ∀ {γ δ} → γ ≃K δ → Bisim γ δ
  ≃K→bisim = BR.≃K→≈∂ K

  -- Kernel reflection respects bisimulation immediately (reify is observation-inert).
  reify-bisim : ∀ γ → Bisim (reify γ) γ
  reify-bisim = BR.reify≈∂ K
