{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.GuardedTruthAt where

-- Guarded truth as “stability under resource-constrained interaction”:
-- we define it as the largest observer-admissible fragment of TruthAt and
-- derive the core properties (soundness + step stability).
--
-- Note: in a CHL-facing `Kernel`, the kernel lemma
-- `LK.decode-FlowCode≡decode-BoxAt-step-body` identifies the decoded meaning
-- of `FlowCode` with “stabilise after one body step” (`BoxAt step (Body _)`).

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Kernel as LK
import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.ObserverFromKernel as ObsFrom

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.Kernel Sig Q)
  where

  module O = ObsFrom.For K

  private
    module ForStep
      (step : O.Code → O.Code)
      where

      GuardedTruthAt
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
        → O.Code → Set (ℓ ⊔ lsuc ℓO)
      GuardedTruthAt {ℓO} w =
        ObsCore.Pred⋆≈ {ℓP = ℓO} O.CP O.decode step (O.TruthAt w)

      guarded-sound
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
          {γ : O.Code}
        → GuardedTruthAt {ℓO = ℓO} w γ
        → O.TruthAt w γ
      guarded-sound w =
        ObsCore.Pred⋆≈-sound O.CP O.decode step (O.TruthAt w)

      guarded-stable
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
          (γ : O.Code)
        → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (step γ)
      guarded-stable w =
        ObsCore.Pred⋆≈-stable O.CP O.decode step (O.TruthAt w)

      guarded-ext
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
        → ObsCore.DecodeExtensional≈ O.CP O.decode (GuardedTruthAt {ℓO = ℓO} w)
      guarded-ext w =
        ObsCore.Pred⋆≈-ext O.CP O.decode step (O.TruthAt w)

      guarded-admissible
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
        → ObsCore.Admissible≈ O.Code O.CP O.decode step (O.TruthAt w)
            (GuardedTruthAt {ℓO = ℓO} w)
      guarded-admissible w =
        ObsCore.Pred⋆≈-admissible O.CP O.decode step (O.TruthAt w)

      guarded-largest
        : ∀ {ℓO : Level}
          (w : LogOSSignature.Cosp Sig)
          (P : O.Code → Set ℓO)
        → ObsCore.Admissible≈ O.Code O.CP O.decode step (O.TruthAt w) P
        → ∀ {γ} → P γ → GuardedTruthAt {ℓO = ℓO} w γ
      guarded-largest w P AP p =
        ObsCore.Pred⋆≈-largest O.CP O.decode step (O.TruthAt w) P AP _ p

    module StableStep = ForStep O.step

  -- Guarded truth at a world: maximal “compute then stabilise” predicate
  -- (stable under `BoxAt step (Body _)`), contained in TruthAt.
  GuardedTruthAt
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → O.Code → Set (ℓ ⊔ lsuc ℓO)
  GuardedTruthAt {ℓO} w = StableStep.GuardedTruthAt {ℓO} w

  guarded-sound
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      {γ : O.Code}
    → GuardedTruthAt {ℓO = ℓO} w γ
    → O.TruthAt w γ
  guarded-sound = StableStep.guarded-sound

  guarded-stable
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (O.step γ)
  guarded-stable = StableStep.guarded-stable

  -- Named theorem: guarded truth is observer-stable (resource-constrained interaction).
  guarded-observer-stable
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (O.step γ)
  guarded-observer-stable {ℓO} w γ = guarded-stable {ℓO = ℓO} w γ

  guarded-ext
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.DecodeExtensional≈ O.CP O.decode (GuardedTruthAt {ℓO = ℓO} w)
  guarded-ext = StableStep.guarded-ext

  guarded-admissible
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.step (O.TruthAt w)
        (GuardedTruthAt {ℓO = ℓO} w)
  guarded-admissible = StableStep.guarded-admissible

  -- Named theorem: GuardedTruthAt is the largest observer-admissible fragment.
  guarded-largest
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (P : O.Code → Set ℓO)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.step (O.TruthAt w) P
    → ∀ {γ} → P γ → GuardedTruthAt {ℓO = ℓO} w γ
  guarded-largest = StableStep.guarded-largest
