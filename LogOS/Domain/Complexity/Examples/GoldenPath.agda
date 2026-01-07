{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Examples.GoldenPath where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.PolyGrade as PG
import LogOS.Domain.Complexity.PvsNPFromInfo_Grade_Only as PFI
import LogOS.Domain.Complexity.PhysToTruthRouteBridge as Bridge
import LogOS.Domain.Complexity.ClassicalPvsNP as CP
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TR

-- Golden path skeleton:
-- grade-native core (info-hardness) → grade-hom bridge → classical alignment at the end.

module Core
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (PGG : PG.PolyPredG (QAdapter.Scale Q))
  where

  module Route = PFI.For K Input Size DetRun VerRun VerRunWith PGG
  open Route public

module BridgeFromNat
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q₁ Q₂ : QAdapter ℓ}
  (K₁ : GradedKernel Sig Q₁)
  (K₂ : GradedKernel Sig Q₂)
  (h  : GradedKernelHomWithGrade K₁ K₂)
  (hf : GradedKernelHomFlowWithGrade K₁ K₂ h)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun₁ : Input → GradedKernel.Code K₁)
  (VerRun₁ : Input → GradedKernel.Code K₁)
  (VerRunWith₁ : Input → GradedKernel.Code K₁ → GradedKernel.Code K₁)
  (DetRun₂ : Input → GradedKernel.Code K₂)
  (VerRun₂ : Input → GradedKernel.Code K₂)
  (VerRunWith₂ : Input → GradedKernel.Code K₂ → GradedKernel.Code K₂)
  (Pℕ : PolyPred)
  (gradeBound₁ : ℕ → QAdapter.Scale Q₁)
  (gradeBound₂ : ℕ → QAdapter.Scale Q₂)
  (grade-coh : ∀ n →
     gradeBound₂ n ≡
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (gradeBound₁ n)))
  (det-map : ∀ x → GradedKernelHomWithGrade.mapCode h (DetRun₁ x) ≡ DetRun₂ x)
  (ver-map : ∀ x → GradedKernelHomWithGrade.mapCode h (VerRun₁ x) ≡ VerRun₂ x)
  (verw-map : ∀ x w → GradedKernelHomWithGrade.mapCode h (VerRunWith₁ x w)
                     ≡ VerRunWith₂ x (GradedKernelHomWithGrade.mapCode h w))
  where

  module Base =
    Bridge.ForGFromNat
      K₁ K₂ h hf Input Size
      DetRun₁ VerRun₁ VerRunWith₁
      DetRun₂ VerRun₂ VerRunWith₂
      Pℕ gradeBound₁ gradeBound₂ grade-coh
      det-map ver-map verw-map

  module WithBack
    (back : QAdapter.Scale Q₂ → QAdapter.Scale Q₁)
    (map-back : ∀ g₂ →
       (let module GH = Truth.GuardedCore.GradeHom (GradedKernelHomWithGrade.grade-hom h) in
        GH.map (back g₂)) ≡ g₂)
    (poly-back
      : ∀ g₂ →
        PG.PolyPredG.isPolyG Base.PG₂.polyPredG g₂ →
        PG.PolyPredG.isPolyG Base.PG₁.polyPredG (λ n → back (g₂ n)))
    where

    open Base.WithBack back map-back poly-back public

module ClassicalAlignment
  {ℓ ℓI : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (Input : Set ℓI)
  (Size  : Input → ℕ)
  (DetRun : Input → GradedKernel.Code K)
  (VerRun : Input → GradedKernel.Code K)
  (VerRunWith : Input → GradedKernel.Code K → GradedKernel.Code K)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (WSize : GradedKernel.Code K → ℕ)
  (Pℕ : PolyPred)
  where

  IsPoly : (ℕ → ℕ) → Set
  IsPoly = PolyPred.isPoly Pℕ

  module Rℕ = TR.ForNat K Input Size DetRun VerRun VerRunWith IsPoly gradeBound
  module Wℕ = Rℕ.WithWitnessSize WSize

  module CS =
    CP.FromTruthRoute
      K Input Size DetRun VerRun VerRunWith
      IsPoly gradeBound WSize Pℕ (λ {p} pp → pp)

  module ForLanguage {ℓL : Level} (L : Rℕ.Language ℓL) where
    module L₀ = CS.ForLanguage {ℓL = ℓL} L

    toClassicalInP : Rℕ.InP {ℓL = ℓL} L → L₀.C.InP L
    toClassicalInP = L₀.fromInP

    toClassicalInNP : Wℕ.InNP {ℓL = ℓL} L → L₀.C.InNP L
    toClassicalInNP = L₀.fromInNP
