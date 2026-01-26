{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.MathTruth where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.Prelude.Product using (Σ; _,_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.TruthPositivity as TP
import LogOS.Theorems.Meta.LimitPublicisation as LP

-- Observer-facing positivity induced from the canonical communicability projector `Pr`.
-- This is logic-agnostic: `W-pos` can be any predicate on the observer language of codes.

TruthPositivity-fromPr
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K     : Kernel Sig Q)
    (W-pos : Kernel.Code K → Set ℓW)
  → TP.TruthPositivity {ℓ} {ℓW} {ℓ ⊔ ℓW ⊔ lsuc ℓC}
TruthPositivity-fromPr {ℓC = ℓC} K W-pos = record
  { Test       = Kernel.Code K
  ; W-pos      = W-pos
  ; Observable = Comm.Pr {ℓC = ℓC} K W-pos
  ; positivity = λ _ obs → Comm.comm⋆-sound {ℓC = ℓC} K W-pos obs
  }

-- A compact “MathTruth” pack:
-- - a family of finite regulator predicates `Truthᵢ`,
-- - the limit predicate `Truth∞` as their pointwise intersection,
-- - the canonical observable/communicable fragment `Observable = Pr Truth∞`,
-- - a derived limit lemma: if every regulator can communicate γ, then so can the limit.

record MathTruth {ℓ ℓT ℓC : Level}
                 {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                 (K : Kernel Sig Q)
                 : Set (lsuc (ℓ ⊔ ℓT ⊔ lsuc ℓC)) where
  open Kernel K

  field
    Idx     : Set
    Truthᵢ  : Idx → Code → Set ℓT

  -- Limit predicate as intersection (“remove the regulator”).
  Truth∞ : Code → Set ℓT
  Truth∞ γ = ∀ i → Truthᵢ i γ

  -- Canonical communicable/observable truth at the limit.
  Observable : Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
  Observable = Comm.Pr {ℓC = ℓC} K Truth∞

  -- Canonicality (“reflector”): `Observable` is the largest communicable predicate
  -- compatible with FlowCode and sound for the limit truth predicate `Truth∞`.

  observable-admissible
    : Comm.AdmissibleComm
        {ℓ = ℓ} {ℓT = ℓT} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)}
        K Truth∞ Observable
  observable-admissible = Comm.comm⋆-admissible {ℓC = ℓC} K Truth∞

  observable-factor
    : ∀ (CommP : Code → Set ℓC)
      → Comm.AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K Truth∞ CommP
      → ∀ {γ} → CommP γ → Observable γ
  observable-factor CommP A cγ =
    Comm.comm⋆-intro K Truth∞ CommP A cγ

  -- Basic properties: sound, stable under FlowCode, and decode-extensional.
  observable-sound : ∀ {γ} → Observable γ → Truth∞ γ
  observable-sound = Comm.comm⋆-sound {ℓC = ℓC} K Truth∞

  observable-stable : ∀ γ → (Observable γ) ↔ (Observable (FlowCode K γ))
  observable-stable = Comm.comm⋆-stable {ℓC = ℓC} K Truth∞

  observable-ext : Comm.DecodeExtensional′ K Observable
  observable-ext = Comm.comm⋆-ext {ℓC = ℓC} K Truth∞

  -- Regulator-wise communicable predicates.
  Observableᵢ : Idx → Code → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
  Observableᵢ i = Comm.Pr {ℓC = ℓC} K (Truthᵢ i)

  -- Monotonicity: since Truth∞ ⇒ Truthᵢ i, any limit-observable code is also
  -- observable at every finite regulator.

  Observable→Observableᵢ
    : ∀ i {γ} → Observable γ → Observableᵢ i γ
  Observable→Observableᵢ i obs =
    Comm.comm⋆-mono-Truth K Truth∞ (Truthᵢ i) (λ {γ} t∞ → t∞ i) obs

  -- Meet-limit preservation (derived, not assumed): `Pr` preserves intersections.
  allObservableᵢ→Observable∞
    : ∀ {γ} → (∀ i → Observableᵢ i γ) → Observable γ
  allObservableᵢ→Observable∞ all =
    Comm.Pr-Π {ℓC = ℓC} K Truthᵢ all

  Observable↔allObservableᵢ
    : ∀ {γ} → Observable γ ↔ (∀ i → Observableᵢ i γ)
  Observable↔allObservableᵢ {γ} =
    record
      { to   = λ obs i → Observable→Observableᵢ i obs
      ; from = allObservableᵢ→Observable∞
      }

  -- Idempotence of observability (up to the universe bump inherent in `Pr`).
  Observable-idem-to
    : ∀ {γ} → Observable γ
      → Comm.Pr {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K Observable γ
  Observable-idem-to = Comm.Pr-idem-to {ℓC = ℓC} K Truth∞

  Observable-idem-from
    : ∀ {γ} → Comm.Pr {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K Observable γ
      → Observable γ
  Observable-idem-from = Comm.Pr-idem-from {ℓC = ℓC} K Truth∞

  -- Induced observer-facing positivity interface at the limit.
  Positivity : TP.TruthPositivity {ℓ} {ℓT} {ℓ ⊔ ℓT ⊔ lsuc ℓC}
  Positivity = TruthPositivity-fromPr {ℓC = ℓC} K Truth∞

  -- Schedule/gauge invariance: reindexing regulators along a cofinal map does not
  -- change the meet-limit truth predicate (or its publicisation), provided the
  -- family is monotone (decreasing) in the regulator order.

  Truth∞-cofinal
    : ∀ {B : Set}
      (PIdx : LP.Preorder Idx)
      (u    : B → Idx)
      (cof  : LP.Cofinal PIdx u)
      (antiMono : ∀ {i j} → LP.Preorder._≤_ PIdx i j → ∀ {γ} → Truthᵢ j γ → Truthᵢ i γ)
    → ∀ {γ} → Truth∞ γ ↔ (∀ b → Truthᵢ (u b) γ)
  Truth∞-cofinal PIdx u cof antiMono {γ} =
    LP.LimitTruth-cofinal PIdx u cof Truthᵢ antiMono

  Observable-cofinal
    : ∀ {B : Set}
      (PIdx : LP.Preorder Idx)
      (u    : B → Idx)
      (cof  : LP.Cofinal PIdx u)
      (antiMono : ∀ {i j} → LP.Preorder._≤_ PIdx i j → ∀ {γ} → Truthᵢ j γ → Truthᵢ i γ)
    → ∀ {γ} → Observable γ ↔ Comm.Pr {ℓC = ℓC} K (λ γ → ∀ b → Truthᵢ (u b) γ) γ
  Observable-cofinal {B = B} PIdx u cof antiMono {γ} =
    LP.Pr∞-cofinal {ℓC = ℓC} K PIdx u cof Truthᵢ antiMono

  -- Language invariance within a fixed Kernel: any decode-preserving translation
  -- does not change the publicised limit predicate.

  observable-naturality
    : (f : Code → Code)
    → LP.DecodePreserving K f
    → ∀ {γ} → Observable γ ↔ Observable (f γ)
  observable-naturality f pres {γ} =
    LP.Pr-naturality {ℓC = ℓC} K Truth∞ f pres
