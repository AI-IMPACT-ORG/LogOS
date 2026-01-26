{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.GuardedTruthAt where

-- Guarded truth as “stability under resource-constrained interaction”:
-- we define it as the largest observer-admissible fragment of TruthAt and
-- derive the core properties (soundness + FlowCode stability).
--
-- In a CHL-facing `LogicKernel`, `FlowCode` is decode-equivalent to
-- “stabilise after one body step” (`BoxAt step (Body _)`), so any claims
-- phrased as “stable under FlowCode” can be read as “stable after compute”.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Kernel.LogicKernel as LK
import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsFrom

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
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
    module FlowCodeStep = ForStep O.stepFlowCode

  -- Guarded truth at a world: maximal “compute then stabilise” predicate
  -- (stable under `BoxAt step (Body _)`), contained in TruthAt.
  GuardedTruthAt
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → O.Code → Set (ℓ ⊔ lsuc ℓO)
  GuardedTruthAt {ℓO} w = StableStep.GuardedTruthAt {ℓO} w

  -- Same notion, but presented via the legacy/raw operational step `FlowCode`.
  GuardedTruthAt-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → O.Code → Set (ℓ ⊔ lsuc ℓO)
  GuardedTruthAt-FlowCode {ℓO} w = FlowCodeStep.GuardedTruthAt {ℓO} w

  GuardedTruthAt↔GuardedTruthAt-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ∀ {γ}
    → GuardedTruthAt {ℓO = ℓO} w γ
      ↔ GuardedTruthAt-FlowCode {ℓO = ℓO} w γ
  GuardedTruthAt↔GuardedTruthAt-FlowCode {ℓO = ℓO} w {γ} =
    let
      module ST =
        ObsCore.StepTransport≈
          O.CP
          O.decode
          O.step
          O.stepFlowCode
          O.decode-step≈decode-stepFlowCode
    in
    ST.Pred⋆≈↔ {ℓP = ℓO} (O.TruthAt w) {γ = γ}

  guarded-sound
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      {γ : O.Code}
    → GuardedTruthAt {ℓO = ℓO} w γ
    → O.TruthAt w γ
  guarded-sound = StableStep.guarded-sound

  guarded-sound-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      {γ : O.Code}
    → GuardedTruthAt-FlowCode {ℓO = ℓO} w γ
    → O.TruthAt w γ
  guarded-sound-FlowCode = FlowCodeStep.guarded-sound

  guarded-stable
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (O.step γ)
  guarded-stable = StableStep.guarded-stable

  guarded-stable-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt-FlowCode {ℓO = ℓO} w γ
      ↔ GuardedTruthAt-FlowCode {ℓO = ℓO} w (O.stepFlowCode γ)
  guarded-stable-FlowCode = FlowCodeStep.guarded-stable

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

  guarded-ext-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.DecodeExtensional≈ O.CP O.decode (GuardedTruthAt-FlowCode {ℓO = ℓO} w)
  guarded-ext-FlowCode = FlowCodeStep.guarded-ext

  guarded-admissible
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.step (O.TruthAt w)
        (GuardedTruthAt {ℓO = ℓO} w)
  guarded-admissible = StableStep.guarded-admissible

  guarded-admissible-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.stepFlowCode (O.TruthAt w)
        (GuardedTruthAt-FlowCode {ℓO = ℓO} w)
  guarded-admissible-FlowCode = FlowCodeStep.guarded-admissible

  -- Named theorem: GuardedTruthAt is the largest observer-admissible fragment.
  guarded-largest
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (P : O.Code → Set ℓO)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.step (O.TruthAt w) P
    → ∀ {γ} → P γ → GuardedTruthAt {ℓO = ℓO} w γ
  guarded-largest = StableStep.guarded-largest

  guarded-largest-FlowCode
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (P : O.Code → Set ℓO)
    → ObsCore.Admissible≈ O.Code O.CP O.decode O.stepFlowCode (O.TruthAt w) P
    → ∀ {γ} → P γ → GuardedTruthAt-FlowCode {ℓO = ℓO} w γ
  guarded-largest-FlowCode = FlowCodeStep.guarded-largest
