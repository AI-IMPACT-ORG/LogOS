{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.SyntaxCompleteness where

-- Relative completeness for the strict syntax layer, via boundary adequacy.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
import LogOS.Theorems.Meta.TruthLemma as TruthLemma
import LogOS.Theorems.Meta.CHL.Completeness as CHLC

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  private
    CP = BulkBoundary.bnd (Kernel.BB K)

  module ST = Truth.StrictTruth Sig
  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
  module TL = TruthLemma.KernelTruthLemma {Sig = Sig} {Q = Q} K
  module C = CHLC.For K
  open C using (BoundaryAdequacy; BoundaryObsAdequacy; obs→boundary; Budget; BudgetedAdequacy)

  -- Proof calculus on strict formulas: refinement of translated constraints.
  infix 4 _⊢S_
  _⊢S_ : Kernel.Fml K → Kernel.Fml K → Set ℓ
  φ ⊢S ψ = ConPoset._⊑_ CP (Kernel.TransH K φ) (Kernel.TransH K ψ)

  -- Semantic entailment on the strict layer (all worlds).
  EntailsS : Kernel.Fml K → Kernel.Fml K → Set ℓ
  EntailsS φ ψ =
    ∀ (w : LogOSSignature.Cosp Sig)
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w φ
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w ψ

  -- Budgeted strict entailment: only observations satisfying B.
  EntailsS-budget
    : (B : Budget)
    → Kernel.Fml K → Kernel.Fml K → Set ℓ
  EntailsS-budget B φ ψ =
    ∀ (w : LogOSSignature.Cosp Sig)
    → B w
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w φ
    → ST.StrictLayer.Sat_S (Kernel.Strict K) w ψ

  idS : ∀ {φ} → φ ⊢S φ
  idS = ConPoset.refl CP

  cutS : ∀ {φ ψ χ} → φ ⊢S ψ → ψ ⊢S χ → φ ⊢S χ
  cutS = ConPoset.trans CP

  -- Soundness: derivability implies semantic entailment.
  soundS : ∀ {φ ψ} → φ ⊢S ψ → EntailsS φ ψ
  soundS {φ} {ψ} le w satS =
    let
      satH  = Prop._↔_.to (Kernel.coh-LH K w φ) satS
      satH' = HT.HLayer.mono-Con (Kernel.HTruth K) le satH
    in Prop._↔_.from (Kernel.coh-LH K w ψ) satH'

  soundS-budget : ∀ {B φ ψ} → φ ⊢S ψ → EntailsS-budget B φ ψ
  soundS-budget le w _ satS = soundS le w satS

  -- Relative completeness: semantic entailment implies derivability.
  completeS : BoundaryAdequacy → ∀ {φ ψ} → EntailsS φ ψ → φ ⊢S ψ
  completeS BA {φ} {ψ} ent =
    BoundaryAdequacy.reflect BA (λ w satB →
      let
        satS  = Prop._↔_.from (TL.S↔∂ w φ) satB
        satS' = ent w satS
      in Prop._↔_.to (TL.S↔∂ w ψ) satS')

  completeS-budget
    : ∀ {B} → BudgetedAdequacy B
    → ∀ {φ ψ} → EntailsS-budget B φ ψ → φ ⊢S ψ
  completeS-budget BA {φ} {ψ} ent =
    BudgetedAdequacy.reflect BA (λ w bw satB →
      let
        satS  = Prop._↔_.from (TL.S↔∂ w φ) satB
        satS' = ent w bw satS
      in Prop._↔_.to (TL.S↔∂ w ψ) satS')

  -- Soundness + completeness packaged as an equivalence.
  sound-completeS : BoundaryAdequacy → ∀ {φ ψ} → (φ ⊢S ψ) ↔ EntailsS φ ψ
  sound-completeS BA =
    Prop.intro (soundS) (completeS BA)

  sound-completeS-obs : BoundaryObsAdequacy → ∀ {φ ψ} → (φ ⊢S ψ) ↔ EntailsS φ ψ
  sound-completeS-obs OA = sound-completeS (obs→boundary OA)

  sound-completeS-budget
    : ∀ {B} → BudgetedAdequacy B
    → ∀ {φ ψ} → (φ ⊢S ψ) ↔ EntailsS-budget B φ ψ
  sound-completeS-budget BA =
    Prop.intro (soundS-budget) (completeS-budget BA)
