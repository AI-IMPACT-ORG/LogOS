{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.GuardedTruthAt where

-- Guarded truth as “stability under resource-constrained interaction”:
-- we define it as the largest observer-admissible fragment of TruthAt and
-- derive the core properties (soundness + FlowCode stability).

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

  -- Guarded truth at a world: maximal FlowCode-stable, decode-extensional
  -- predicate contained in TruthAt.
  GuardedTruthAt
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → O.Code → Set (ℓ ⊔ lsuc ℓO)
  GuardedTruthAt {ℓO} w =
    ObsCore.Pred⋆ {ℓP = ℓO} O.decode O.stepCode (O.TruthAt w)

  guarded-sound
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      {γ : O.Code}
    → GuardedTruthAt {ℓO = ℓO} w γ
    → O.TruthAt w γ
  guarded-sound w =
    ObsCore.Pred⋆-sound O.decode O.stepCode (O.TruthAt w)

  guarded-stable
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (O.stepCode γ)
  guarded-stable w =
    ObsCore.Pred⋆-stable O.decode O.stepCode (O.TruthAt w)

  -- Named theorem: guarded truth is observer-stable (resource-constrained interaction).
  guarded-observer-stable
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (γ : O.Code)
    → GuardedTruthAt {ℓO = ℓO} w γ ↔ GuardedTruthAt {ℓO = ℓO} w (O.stepCode γ)
  guarded-observer-stable = guarded-stable

  guarded-ext
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.DecodeExtensional O.decode (GuardedTruthAt {ℓO = ℓO} w)
  guarded-ext w =
    ObsCore.Pred⋆-ext O.decode O.stepCode (O.TruthAt w)

  guarded-admissible
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
    → ObsCore.Admissible O.Code O.Dec O.decode O.stepCode (O.TruthAt w)
        (GuardedTruthAt {ℓO = ℓO} w)
  guarded-admissible w =
    ObsCore.Pred⋆-admissible O.decode O.stepCode (O.TruthAt w)

  -- Named theorem: GuardedTruthAt is the largest observer-admissible fragment.
  guarded-largest
    : ∀ {ℓO : Level}
      (w : LogOSSignature.Cosp Sig)
      (P : O.Code → Set ℓO)
    → ObsCore.Admissible O.Code O.Dec O.decode O.stepCode (O.TruthAt w) P
    → ∀ {γ} → P γ → GuardedTruthAt {ℓO = ℓO} w γ
  guarded-largest w P AP p =
    ObsCore.Pred⋆-largest O.decode O.stepCode (O.TruthAt w) P AP _ p
