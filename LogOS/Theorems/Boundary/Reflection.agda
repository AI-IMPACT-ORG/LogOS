{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Reflection where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.View using (≃→≈[V])
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.Tiers as KTiers
open import LogOS.Kernel.Eq using (module ForKernel)

-- Kernel self-reflection “up to the explicit boundary”: codes are observed only
-- via the boundary view `Sat_H_bnd ∘ decode`.
--
-- This module packages the core congruences that follow *purely* from the Kernel
-- fields (no extra axioms): reify does not change boundary meaning, and the
-- canonical fixed point code `γ*` agrees with the guarded boundary point `Th⋆`.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) where
  open Kernel K using (Sat_H_bnd; encode; decode; decode∘encode; reify; reify-decode; γ*; decode-γ*)
  open ForKernel K

  module KT = KTiers.For K

  -- Boundary observational equality on codes: two codes agree when they
  -- induce the same boundary observations across all boundary contexts.

  infix 4 _≈∂_
  _≈∂_ : Kernel.Code K → Kernel.Code K → Set ℓ
  _≈∂_ = KT._≈obs_

  -- Strict decoded equality implies boundary equivalence.

  ≃K→≈∂ : ∀ {γ δ} → γ ≃K δ → γ ≈∂ δ
  ≃K→≈∂ eq = ≃→≈[V] {V = KT.decodeObsView} eq

  -- Reify is observationally inert at the boundary.

  reify≈∂ : ∀ γ → reify γ ≈∂ γ
  reify≈∂ γ = ≃K→≈∂ (reify-decode γ)

  -- Reify is a decode-level idempotent retraction.

  reify-idem-decode
    : ∀ γ → decode (reify (reify γ)) ≡ decode γ
  reify-idem-decode γ =
    trans (reify-decode (reify γ)) (reify-decode γ)

  reify-idempotent-decode = reify-idem-decode

  reify-encode-decode
    : ∀ c → decode (reify (encode c)) ≡ c
  reify-encode-decode c =
    trans (reify-decode (encode c)) (decode∘encode c)

  reify-retraction-decode = reify-encode-decode

  -- Canonical fixed point code reflects the guarded boundary fixed point.
  -- This is the most concrete “self-reflection” fact available from the core:
  -- code-level `γ*` denotes the boundary point `Th⋆` via `decode`.

  γ*≈∂Th⋆
    : ∀ p → Sat_H_bnd p (decode γ*) ↔ Sat_H_bnd p (Th⋆K K)
  γ*≈∂Th⋆ p =
    record
      { to   = λ s → subst (Sat_H_bnd p) (decode-γ*) s
      ; from = λ s → subst (Sat_H_bnd p) (sym (decode-γ*)) s
      }
