{-
LogOS: an Agda research library for foundational logic system architecture.
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
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)

open import LogOS.Kernel.LogicKernel as LK
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2

import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.RefinementSoundness as RefSound

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  where

  Code : Set ℓ
  Code = LK.LogicKernel.Code K

  Dec : Set ℓ
  Dec = ConPoset.Con (BulkBoundary.bnd (LK.LogicKernel.BB K))

  decode : Code → Dec
  decode = LK.LogicKernel.decode K

  stepCode : Code → Code
  stepCode = LK.FlowCode K

  -- One-line canonical ObserverCore instantiation:
  Observable⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Observable⋆ {ℓO = ℓO} TruthK = ObsCore.Pred⋆ {ℓP = ℓO} decode stepCode TruthK

  -- Safe reflection (alias): maximal admissible predicate for TruthK.
  Safe⋆
    : ∀ {ℓT ℓO : Level}
      (TruthK : Code → Set ℓT)
    → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓO)
  Safe⋆ {ℓT} {ℓO} TruthK = Observable⋆ {ℓT} {ℓO} TruthK

  -- Concrete truth predicate induced by boundary satisfaction at a chosen world.
  --
  -- This is decode-extensional by construction, so it is a canonical input to `Observable⋆`.

  TruthAt
    : LogOSSignature.Cosp Sig → Code → Set ℓ
  TruthAt w γ = LK.LogicKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (decode γ)

  -- Safe reflection of boundary truth at a world.
  SafeTruthAt
    : ∀ {ℓO : Level} (w : LogOSSignature.Cosp Sig)
    → Code → Set (ℓ ⊔ lsuc ℓO)
  SafeTruthAt {ℓO = ℓO} w = Safe⋆ {ℓO = ℓO} (TruthAt w)

  TruthAt-ext : ∀ (w : LogOSSignature.Cosp Sig) → ObsCore.DecodeExtensional decode (TruthAt w)
  TruthAt-ext w γ₁ γ₂ eq sat =
    subst (λ c → LK.LogicKernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c) eq sat

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
