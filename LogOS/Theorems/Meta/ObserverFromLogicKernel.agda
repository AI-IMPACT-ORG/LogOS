{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ObserverFromLogicKernel where

-- Canonical “observer semantics” adaptor for the CHL-facing `LogicKernel` interface.
--
-- This is deliberately lightweight:
-- - it does not add axioms or strengthen the kernel,
-- - it only packages the already-existing primitives into the generic
--   `ObserverCore` interface,
-- - and it exposes the key alignment lemma: refinement (2-cells) implies
--   truth preservation for boundary satisfaction (observer semantics).

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; _≈CP_)
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Kernel.LogicKernel as LK
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2
import LogOS.Kernel.Core as KCore

import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.RefinementSoundness as RefSound

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  where

  Code : Set ℓ
  Code = LK.LogicKernel.Code K

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (LK.LogicKernel.BB K)

  Dec : Set ℓ
  Dec = ConPreorder.Con CP

  decode : Code → Dec
  decode = LK.LogicKernel.decode K

  private
    stepGrade : LK.GTier.Step (LK.LogicKernel.G K)
    stepGrade = LK.GTier.step (LK.LogicKernel.G K)

  -- Canonical observer step:
  -- “run one computational body step, then stabilise at the step grade”.
  step : Code → Code
  step γ =
    LK.BoxAt K stepGrade (LK.LogicKernel.Body K γ)

  -- Legacy/raw operational step (same decoded boundary evolution, different code presentation):
  -- `FlowCode = Guard ∘ Body`.
  stepFlowCode : Code → Code
  stepFlowCode = LK.FlowCode K

  decode-stepFlowCode≡decode-step
    : ∀ γ → decode (stepFlowCode γ) ≡ decode (step γ)
  decode-stepFlowCode≡decode-step = LK.decode-FlowCode≡decode-BoxAt-step-body K

  decode-stepFlowCode≈decode-step
    : ∀ γ → _≈CP_ CP (decode (stepFlowCode γ)) (decode (step γ))
  decode-stepFlowCode≈decode-step γ
    rewrite decode-stepFlowCode≡decode-step γ
    = (ConPreorder.refl CP , ConPreorder.refl CP)

  decode-step≈decode-stepFlowCode
    : ∀ γ → _≈CP_ CP (decode (step γ)) (decode (stepFlowCode γ))
  decode-step≈decode-stepFlowCode γ =
    let (xy , yx) = decode-stepFlowCode≈decode-step γ in (yx , xy)

  TruthK-stepFlowCode↔TruthK-step
    : ∀ {ℓT : Level}
      (TruthK : Code → Set ℓT)
    → ObsCore.DecodeExtensional decode TruthK
    → ∀ γ → TruthK (stepFlowCode γ) ↔ TruthK (step γ)
  TruthK-stepFlowCode↔TruthK-step TruthK extTruth γ =
    ObsCore.DecodeExtensional-cong extTruth (decode-stepFlowCode≡decode-step γ)

  -- One-line canonical ObserverCore instantiation:
  Observable⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Observable⋆ {ℓO = ℓO} TruthK = ObsCore.Pred⋆≈ {ℓP = ℓO} CP decode step TruthK

  -- Same observer semantics, but presented via the legacy/raw `FlowCode` step.
  Observable⋆-FlowCode
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Observable⋆-FlowCode {ℓO = ℓO} TruthK =
    ObsCore.Pred⋆≈ {ℓP = ℓO} CP decode stepFlowCode TruthK

  Observable⋆↔Observable⋆-FlowCode
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → ∀ {γ}
    → Observable⋆ {ℓO = ℓO} TruthK γ
      ↔
      Observable⋆-FlowCode {ℓO = ℓO} TruthK γ
  Observable⋆↔Observable⋆-FlowCode {ℓO = ℓO} TruthK {γ} =
    let
      module ST =
        ObsCore.StepTransport≈
          CP
          decode
          step
          stepFlowCode
          decode-step≈decode-stepFlowCode
    in
    ST.Pred⋆≈↔ {ℓP = ℓO} TruthK {γ = γ}

  -- Safe reflection (alias): maximal admissible predicate for TruthK.
  Safe⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Safe⋆ {ℓT} {ℓO} TruthK = Observable⋆ {ℓT} {ℓO} TruthK

  -- Concrete truth predicate induced by boundary satisfaction at a chosen world.
  --
  -- This is extensional w.r.t. decoded observational equality (`≈`), using
  -- monotonicity of boundary satisfaction.

  TruthAt
    : LogOSSignature.Cosp Sig → Code → Set ℓ
  TruthAt w γ = LK.LogicKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (decode γ)

  -- Safe reflection of boundary truth at a world.
  SafeTruthAt
    : ∀ {ℓO : Level} (w : LogOSSignature.Cosp Sig)
    → Code → Set (ℓ ⊔ lsuc ℓO)
  SafeTruthAt {ℓO = ℓO} w = Safe⋆ {ℓO = ℓO} (TruthAt w)

  TruthAt-ext : ∀ (w : LogOSSignature.Cosp Sig) → ObsCore.DecodeExtensional≈ CP decode (TruthAt w)
  TruthAt-ext w γ₁ γ₂ eq sat =
    let (c≤c' , _) = eq in
    KCore.Sat_H_bnd-mono (LK.LogicKernel.shape K) c≤c' sat

-- Refinement (2-cells) preserves TruthAt in the target LogicKernel.
-- This is the “2-category picture agrees with observer semantics” lemma.

module RefinementPreservesTruthAt
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {K₁ K₂ : LK.LogicKernel Sig Q}
  {f g : LK2.LogicKernelHom₁ K₁ K₂}
  (fg : LK2._⇒_ f g)
  where

  module RS = RefSound.LogicKernelSoundness {Sig = Sig} {Q = Q}
  module T  = For {Sig = Sig} {Q = Q} K₂

  preserves
    : ∀ (w : LogOSSignature.Cosp Sig) (γ : LK.LogicKernel.Code K₁)
    → T.TruthAt w (LK2.LogicKernelHom₁.mapCode₁ f γ)
    → T.TruthAt w (LK2.LogicKernelHom₁.mapCode₁ g γ)
  preserves w γ sat =
    RS.refine-preserves-Sat_H_bnd {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} fg w γ sat
