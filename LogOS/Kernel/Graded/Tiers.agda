{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Tiers where

-- Derived S/H/G/R tier interface for a `GradedKernel`.
--
-- This is the graded analogue of `LogOS.Kernel.Tiers`, focusing on the shared
-- H/R structure (decode-views and boundary-observational comparisons).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.RelPreorder
open import LogOS.Minimal.View
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel.Graded

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  open LogOSSignature Sig

  -- Base H-target preorder (order-theoretic).
  CPᴴ : ConPreorder ℓ
  CPᴴ = BulkBoundary.bnd (GradedKernel.BB K)

  -- Same target as a two-level preorder.
  RPᴴ : RelPreorder ℓ ℓ
  RPᴴ = ConPreorder→RelPreorder CPᴴ

  -- Observational H-target preorder induced by boundary satisfaction.
  CPᴴᵒ : RelPreorder ℓ ℓ
  CPᴴᵒ = ObsPreorder (GradedKernel.Sat_H_bnd K)

  -- Canonical views into the H-target preorder.
  decodeView : View (GradedKernel.Code K) RPᴴ
  decodeView = record { μ = GradedKernel.decode K }

  transHView : View (GradedKernel.Fml K) RPᴴ
  transHView = record { μ = GradedKernel.TransH K }

  -- Canonical view for code-level observational comparisons.
  decodeObsView : View (GradedKernel.Code K) CPᴴᵒ
  decodeObsView = record { μ = GradedKernel.decode K }

  -- View-named relations (recommended for downstream naming discipline).

  infix 4 _⊑decode_ _≈decode_ _≃decode_

  _⊑decode_ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  γ ⊑decode δ = γ ⊑[ decodeView ] δ

  _≈decode_ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  γ ≈decode δ = γ ≈[ decodeView ] δ

  _≃decode_ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  γ ≃decode δ = γ ≃[ decodeView ] δ

  infix 4 _⊑TransH_ _≈TransH_ _≃TransH_

  _⊑TransH_ : GradedKernel.Fml K → GradedKernel.Fml K → Set ℓ
  φ ⊑TransH ψ = φ ⊑[ transHView ] ψ

  _≈TransH_ : GradedKernel.Fml K → GradedKernel.Fml K → Set ℓ
  φ ≈TransH ψ = φ ≈[ transHView ] ψ

  _≃TransH_ : GradedKernel.Fml K → GradedKernel.Fml K → Set ℓ
  φ ≃TransH ψ = φ ≃[ transHView ] ψ

  -- Observational comparisons on code via `decode` (boundary satisfaction).

  infix 4 _⊑obs_ _≈obs_

  _⊑obs_ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  γ ⊑obs δ = γ ⊑[ decodeObsView ] δ

  _≈obs_ : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  γ ≈obs δ = γ ≈[ decodeObsView ] δ

  -- Non-glyph alias (useful at call sites that prefer a prefix name).
  Obs≈obs : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  Obs≈obs = _≈obs_

  -- Presentation aliases for observational comparisons on code via `decode`.

  Sat_obs : ∂Cosp → GradedKernel.Code K → Set ℓ
  Sat_obs p γ = GradedKernel.Sat_H_bnd K p (GradedKernel.decode K γ)

  ObsLeobs : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  ObsLeobs = Prop.ObsLeOn Sat_obs

  ObsEqobs : GradedKernel.Code K → GradedKernel.Code K → Set ℓ
  ObsEqobs = Prop.ObsEqOn Sat_obs

  ObsEqobs↔≈obs : ∀ {γ δ} → Prop._↔_ (ObsEqobs γ δ) (γ ≈obs δ)
  ObsEqobs↔≈obs {γ} {δ} =
    ObsEqOn↔Obs≈ Sat_obs {x = γ} {y = δ}

  ObsEqobs↔Obs≈obs : ∀ {γ δ} → Prop._↔_ (ObsEqobs γ δ) (Obs≈obs γ δ)
  ObsEqobs↔Obs≈obs = ObsEqobs↔≈obs
