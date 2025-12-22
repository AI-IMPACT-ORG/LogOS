{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.SemanticCut where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Syntax.Prop as Prop

-- Semantic S-layer entailment and cut (admissibility by composition).
-- Proofs live entirely in this module; upstream dependencies are the Kernel
-- records from `LogOS/Kernel.agda` and H-layer monotonicity from `LogOS/Minimal/Truth.agda`.

Ent_S
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    → Kernel.Fml K → Kernel.Fml K → Set ℓ
Ent_S Sig Q K φ ψ =
  ∀ (w : LogOSSignature.Cosp Sig)
  → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w φ
  → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w ψ

-- Reflexivity and transitivity (cut)

reflS
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (φ : Kernel.Fml K)
  → Ent_S Sig Q K φ φ
reflS Sig Q K φ w p = p

cutS
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    {φ ψ χ : Kernel.Fml K}
  → Ent_S Sig Q K φ ψ
  → Ent_S Sig Q K ψ χ
  → Ent_S Sig Q K φ χ
cutS Sig Q K e₁ e₂ w p = e₂ w (e₁ w p)

-- Soundness: boundary inequality implies S-layer entailment via S↔H coherence.

ineq→Ent_S
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (φ ψ : Kernel.Fml K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Kernel.TransH K φ) (Kernel.TransH K ψ)
  → Ent_S Sig Q K φ ψ
ineq→Ent_S Sig Q K φ ψ le w p =
  let
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    open HT
    -- S↔H coherence
    cL = Kernel.coh-LH K w φ
    cR = Kernel.coh-LH K w ψ
    -- transport to H, apply monotonicity, and transport back
    pH : HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K φ)
    pH = Prop._↔_.to cL p
    qH : HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K ψ)
    qH = HLayer.mono-Con (Kernel.HTruth K) le pH
  in Prop._↔_.from cR qH

-- Completeness direction (Ent_S → boundary inequality) is, in general, not derivable
-- from the minimal core; it would require additional assumptions (e.g., completeness
-- or definability conditions). We refrain from stating it here to keep the module
-- honest and axioms-explicit.
