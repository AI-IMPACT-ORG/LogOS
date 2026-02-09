{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.ObserverFromKernel where

-- Canonical “observer semantics” adapter for the CHL-facing `Kernel` interface.
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
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)

import LogOS.Kernel as LK
import LogOS.Kernel.Hom2Cat as LK2
import LogOS.Kernel.Shape as KCore

import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.RefinementSoundness as RefSound

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.Kernel Sig Q)
  where

  Code : Set ℓ
  Code = LK.Kernel.Code K

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (LK.Kernel.BB K)

  Dec : Set ℓ
  Dec = ConPreorder.Con CP

  decode : Code → Dec
  decode = LK.Kernel.decode K

  private
    stepGrade : LK.GTier.Step (LK.Kernel.G K)
    stepGrade = LK.GTier.step (LK.Kernel.G K)

  -- Canonical observer step:
  -- “run one computational body step, then stabilise at the step grade”.
  step : Code → Code
  step γ =
    LK.BoxAt K stepGrade (LK.Kernel.Body K γ)

  -- One-line canonical ObserverCore instantiation:
  Observable⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Observable⋆ {ℓO = ℓO} TruthK = ObsCore.Pred⋆≈ {ℓP = ℓO} CP decode step TruthK

  -- Safe reflection (alias): maximal admissible predicate for TruthK.
  Safe⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Safe⋆ {ℓT} {ℓO} TruthK = Observable⋆ {ℓT} {ℓO} TruthK

  -- Concrete truth predicate induced by boundary satisfaction at a chosen world.
  --
  -- This is extensional w.r.t. decoded mutual refinement (`≈`), using
  -- monotonicity of boundary satisfaction.

  TruthAt
    : LogOSSignature.Cosp Sig → Code → Set ℓ
  TruthAt w γ = LK.Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (decode γ)

  -- Safe reflection of boundary truth at a world.
  SafeTruthAt
    : ∀ {ℓO : Level} (w : LogOSSignature.Cosp Sig)
    → Code → Set (ℓ ⊔ lsuc ℓO)
  SafeTruthAt {ℓO = ℓO} w = Safe⋆ {ℓO = ℓO} (TruthAt w)

  TruthAt-ext : ∀ (w : LogOSSignature.Cosp Sig) → ObsCore.DecodeExtensional≈ CP decode (TruthAt w)
  TruthAt-ext w γ₁ γ₂ eq sat =
    let (c≤c' , _) = eq in
    KCore.Sat_H_bnd-mono (LK.Kernel.shape K) c≤c' sat

-- Refinement (2-cells) preserves TruthAt in the target Kernel.
-- This is the “2-category picture agrees with observer semantics” lemma.

module RefinementPreservesTruthAt
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {K₁ K₂ : LK.Kernel Sig Q}
  {f g : LK2.KernelHom₁ K₁ K₂}
  (fg : LK2._⇒_ f g)
  where

  module RS = RefSound.KernelSoundness {Sig = Sig} {Q = Q}
  module T  = For {Sig = Sig} {Q = Q} K₂

  preserves
    : ∀ (w : LogOSSignature.Cosp Sig) (γ : LK.Kernel.Code K₁)
    → T.TruthAt w (LK2.KernelHom₁.mapCode₁ f γ)
    → T.TruthAt w (LK2.KernelHom₁.mapCode₁ g γ)
  preserves w γ sat =
    RS.refine-preserves-Sat_H_bnd {K₁ = K₁} {K₂ = K₂} {f = f} {g = g} fg w γ sat
