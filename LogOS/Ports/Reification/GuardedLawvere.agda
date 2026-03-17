{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Reification.GuardedLawvere where

-- Guarded, refinement-first Lawvere schema packaged as an optional
-- reification theorem layer rather than part of the default LT theorem spine.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; mkStable; elem)
open import LogOS.LT.View using (View; μ)
import LogOS.Ports.Reification.Admissible as Admissible

StableObservation
  : ∀ {ℓX ℓCon ℓRel}
  → (X : Set ℓX)
  → (O : ConPreorder ℓCon ℓRel)
  → (GC : GuardedClosure O)
  → Set (ℓX ⊔ lsuc (ℓCon ⊔ ℓRel))
StableObservation X O GC = X → Stable {CP = O} (Flow GC)

Pointwise≈
  : ∀ {ℓX ℓCon ℓRel}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {GC : GuardedClosure O}
  → StableObservation X O GC
  → StableObservation X O GC
  → Set (ℓX ⊔ ℓRel)
Pointwise≈ {O = O} f g = ∀ x → _≈_ O (elem (f x)) (elem (g x))

record StableEvaluator
  {ℓA ℓX ℓCon ℓRel : Level}
  (A : Set ℓA)
  (X : Set ℓX)
  (O : ConPreorder ℓCon ℓRel)
  (GC : GuardedClosure O)
  : Set (lsuc (ℓA ⊔ ℓX ⊔ ℓCon ⊔ ℓRel)) where
  field
    eval : A → StableObservation X O GC

open StableEvaluator public

record QuotedPointSurjective
  {ℓA ℓX ℓCon ℓRel : Level}
  {A : Set ℓA}
  {X : Set ℓX}
  {O : ConPreorder ℓCon ℓRel}
  {GC : GuardedClosure O}
  (E : StableEvaluator A X O GC)
  : Set (lsuc (ℓA ⊔ ℓX ⊔ ℓCon ⊔ ℓRel)) where
  field
    quotePoint : X → A
    namesEvery
      : (φ : StableObservation X O GC)
      → Σ X (λ x → Pointwise≈ {X = X} {O = O} {GC = GC}
                     (StableEvaluator.eval E (quotePoint x))
                     φ)

open QuotedPointSurjective public

stableObservationFromRestrictedReification
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (R : Admissible.RestrictedReification {ℓR = ℓR} obs)
  → (c : Con O)
  → Admissible.RestrictedReification.Reifiable R c
  → Stable {CP = O} (Flow (Admissible.RestrictedReification.GC R))
stableObservationFromRestrictedReification {O = O} {obs = obs} R c r =
  mkStable
    (μ obs (Admissible.RestrictedReification.reify R c r))
    stableObs
  where
    module Rsn = LogOS.Prelude.RefinementKit.Reasoning O
    open Rsn using (begin⊑_; _⊑⟨_⟩_; _∎⊑)

    GC₀ = Admissible.RestrictedReification.GC R
    law = Admissible.RestrictedReification.decode-reify≈Flow R c r

    stableObs
      : _⊑_ O
          (Flow GC₀ (μ obs (Admissible.RestrictedReification.reify R c r)))
          (μ obs (Admissible.RestrictedReification.reify R c r))
    stableObs =
      begin⊑
        Flow GC₀ (μ obs (Admissible.RestrictedReification.reify R c r))
          ⊑⟨ GuardedClosure.mono GC₀ (fst law) ⟩
        Flow GC₀ (Flow GC₀ c)
          ⊑⟨ GuardedClosure.idemp-lax GC₀ c ⟩
        Flow GC₀ c
          ⊑⟨ snd law ⟩
        μ obs (Admissible.RestrictedReification.reify R c r) ∎⊑

stableObservationFromRestrictedReification≈Flow
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (R : Admissible.RestrictedReification {ℓR = ℓR} obs)
  → (c : Con O)
  → (r : Admissible.RestrictedReification.Reifiable R c)
  → _≈_ O
      (elem (stableObservationFromRestrictedReification R c r))
      (Flow (Admissible.RestrictedReification.GC R) c)
stableObservationFromRestrictedReification≈Flow R c r =
  Admissible.RestrictedReification.decode-reify≈Flow R c r

stableObservationFromRestrictedReification≈stable
  : ∀ {ℓX ℓCon ℓRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (R : Admissible.RestrictedReification {ℓR = ℓR} obs)
  → (c : Con O)
  → (r : Admissible.RestrictedReification.Reifiable R c)
  → _⊑_ O (Flow (Admissible.RestrictedReification.GC R) c) c
  → _≈_ O
      (elem (stableObservationFromRestrictedReification R c r))
      c
stableObservationFromRestrictedReification≈stable R c r =
  Admissible.decode-reify-stable≈ R c r

lawvereStableFixedPoint
  : ∀ {ℓA ℓX ℓCon ℓRel}
    {A : Set ℓA}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {GC : GuardedClosure O}
    {E : StableEvaluator A X O GC}
  → (Q : QuotedPointSurjective E)
  → (α : Stable {CP = O} (Flow GC) → Stable {CP = O} (Flow GC))
  → Σ (Stable {CP = O} (Flow GC))
      (λ p → _≈_ O (elem p) (elem (α p)))
lawvereStableFixedPoint {X = X} {O = O} {GC = GC} {E = E} Q α =
  let
    φ : StableObservation X O GC
    φ x = α (StableEvaluator.eval E (QuotedPointSurjective.quotePoint Q x) x)

    named = QuotedPointSurjective.namesEvery Q φ
    x = proj₁ named
    named≈ = proj₂ named

    p : Stable {CP = O} (Flow GC)
    p = StableEvaluator.eval E (QuotedPointSurjective.quotePoint Q x) x
  in
  p , named≈ x

noStableFixedPoint-obstructsQuotedPointSurjective
  : ∀ {ℓA ℓX ℓCon ℓRel}
    {A : Set ℓA}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {GC : GuardedClosure O}
    {E : StableEvaluator A X O GC}
  → Σ
      (Stable {CP = O} (Flow GC) → Stable {CP = O} (Flow GC))
      (λ α → ∀ p → ¬ _≈_ O (elem p) (elem (α p)))
  → ¬ QuotedPointSurjective E
noStableFixedPoint-obstructsQuotedPointSurjective (α , noFixed) Q =
  noFixed p p≈αp
  where
    fixed = lawvereStableFixedPoint Q α
    p = proj₁ fixed
    p≈αp = proj₂ fixed
