{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Completeness where

-- Boundary-level completeness for the code preorder, relative to a small
-- adequacy assumption (order reflection on the image of `to∂`).

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; ObsLeOn)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  private
    CP = BulkBoundary.bnd (Kernel.BB K)

  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)

  -- Boundary entailment restricted to the image of `to∂`.
  Entails∂ : Kernel.Code K → Kernel.Code K → Set ℓ
  Entails∂ γ δ =
    ∀ (w : LogOSSignature.Cosp Sig)
    → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K γ)
    → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K δ)

  -- Soundness: refinement implies boundary entailment.
  sound∂ : ∀ {γ δ} → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ) → Entails∂ γ δ
  sound∂ {γ} {δ} le w satB =
    let
      cohγ = Kernel.sat-coh K w (Kernel.decode K γ)
      cohδ = Kernel.sat-coh K w (Kernel.decode K δ)
      satH  = Prop._↔_.from cohγ satB
      satH' = HT.HLayer.mono-Con (Kernel.HTruth K) le satH
    in Prop._↔_.to cohδ satH'

  -- Adequacy: boundary entailment reflects back to the preorder.
  record BoundaryAdequacy : Set (lsuc ℓ) where
    field
      reflect
        : ∀ {c d}
        → (∀ (w : LogOSSignature.Cosp Sig)
            → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
            → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) d)
        → ConPoset._⊑_ CP c d

  open BoundaryAdequacy public

  -- Completeness is conditional on BoundaryAdequacy.
  complete∂
    : BoundaryAdequacy
    → ∀ {γ δ}
    → Entails∂ γ δ
    → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ)
  complete∂ BA ent = BoundaryAdequacy.reflect BA (λ w satB → ent w satB)

  complete∂-under = complete∂

  sound-complete∂
    : BoundaryAdequacy → ∀ {γ δ}
    → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ) ↔ Entails∂ γ δ
  sound-complete∂ BA =
    Prop.intro (sound∂) (complete∂ BA)

  sound-complete∂-under = sound-complete∂

  -- Budgeted boundary entailment: restrict to a predicate on observations.
  Budget : Set (lsuc ℓ)
  Budget = LogOSSignature.Cosp Sig → Set ℓ

  Entails∂-budget
    : (B : Budget)
    → Kernel.Code K → Kernel.Code K → Set ℓ
  Entails∂-budget B γ δ =
    ∀ (w : LogOSSignature.Cosp Sig)
    → B w
    → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K γ)
    → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K δ)

  -- Budgeted adequacy: the budgeted observations still reflect the preorder.
  record BudgetedAdequacy (B : Budget) : Set (lsuc ℓ) where
    field
      reflect
        : ∀ {c d}
        → (∀ (w : LogOSSignature.Cosp Sig)
            → B w
            → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
            → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) d)
        → ConPoset._⊑_ CP c d

  sound∂-budget
    : ∀ {B γ δ}
    → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ)
    → Entails∂-budget B γ δ
  sound∂-budget le w _ satB = sound∂ le w satB

  complete∂-budget
    : ∀ {B} → BudgetedAdequacy B
    → ∀ {γ δ} → Entails∂-budget B γ δ
    → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ)
  complete∂-budget BA ent = BudgetedAdequacy.reflect BA (λ w bw satB → ent w bw satB)

  complete∂-budget-under = complete∂-budget

  sound-complete∂-budget
    : ∀ {B} → BudgetedAdequacy B
    → ∀ {γ δ}
    → ConPoset._⊑_ CP (Kernel.decode K γ) (Kernel.decode K δ) ↔ Entails∂-budget B γ δ
  sound-complete∂-budget BA =
    Prop.intro (sound∂-budget) (complete∂-budget BA)

  sound-complete∂-budget-under = sound-complete∂-budget

  -- Observational adequacy on the full boundary index (stronger).
  --
  -- This reflects entailment across *all* boundary observations, not just those
  -- in the image of `to∂`.

  ObsAdequacy : Set ℓ
  ObsAdequacy =
    ∀ {c d}
    → ObsLeOn (Kernel.Sat_H_bnd K) c d
    → ConPoset._⊑_ CP c d

  -- Boundary-observational adequacy restricted to `to∂` (same content as boundary
  -- adequacy, but phrased with ObsLeOn to expose the observer reading).

  BoundaryObsAdequacy : Set ℓ
  BoundaryObsAdequacy =
    ∀ {c d}
    → ObsLeOn (λ w c' → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c') c d
    → ConPoset._⊑_ CP c d

  boundary→obs : BoundaryAdequacy → BoundaryObsAdequacy
  boundary→obs BA ent = BoundaryAdequacy.reflect BA ent

  obs→boundary : BoundaryObsAdequacy → BoundaryAdequacy
  obs→boundary OA = record { reflect = OA }
