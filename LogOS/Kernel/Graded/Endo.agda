{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFrom
open import LogOS.Kernel.EndoCore as EndoCore

-- Boundary endomaps and fixed-point helpers for a graded kernel,
-- instantiated at the saturation grade.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : EndoCore.Ops Sig Q
    ops =
      record
        { Obj           = GradedKernel Sig Q
        ; asLogicKernel = LKFrom.asLogicKernel
        }

  open EndoCore.WithOps {Sig = Sig} {Q = Q} ops public

-- Flow at an arbitrary grade as an endomap.

Flow-EndoAt : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : GradedKernel Sig Q) → QAdapter.Scale Q → Endo K
Flow-EndoAt {Sig = Sig} {Q = Q} K g .Endo.fn =
  GradedClosure.Flow (GradedKernel.GTruth K) g
Flow-EndoAt {Sig = Sig} {Q = Q} K g .Endo.mono =
  GradedClosure.mono (GradedKernel.GTruth K) {g = g}

-- Grade monotonicity and composition for Flow endomaps (lax monoid action).

Flow-EndoAt-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    {g g' : QAdapter.Scale Q}
  → QAdapter._≤s_ Q g g'
  → _≤₂_ K (Flow-EndoAt K g) (Flow-EndoAt K g')
Flow-EndoAt-mono {Sig = Sig} {Q = Q} K g≤g' = λ c →
  let open GradedKernel K in
  GradedClosure.mono-grade GTruth g≤g' c

Flow-EndoAt-comp≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g g' : QAdapter.Scale Q)
  → _≤₂_ K ((Flow-EndoAt K g') ∘E (Flow-EndoAt K g))
          (Flow-EndoAt K (QAdapter._·_ Q g g'))
Flow-EndoAt-comp≤ {Sig = Sig} {Q = Q} K g g' = λ c →
  let open GradedKernel K in
  GradedClosure.comp-lax GTruth g g' c

Flow-EndoAt≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (Flow-EndoAt K g) (Flow-Endo K)
Flow-EndoAt≤Flow {Sig = Sig} {Q = Q} K g =
  Flow-EndoAt-mono K (GradedClosure.sat-top (GradedKernel.GTruth K) g)

Step-Endo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
            (K : GradedKernel Sig Q) → Endo K
Step-Endo K = Flow-EndoAt K (GradedKernel.step-grade K)

stepFlow≤satFlow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → _≤₂_ K (Step-Endo K) (Flow-Endo K)
stepFlow≤satFlow {Sig = Sig} {Q = Q} K =
  Flow-EndoAt-mono K (step≤sat K)

-- Grade-indexed closure steps: composition multiplies grades.

record ClosureStepAt {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K   : GradedKernel Sig Q)
                     (g   : QAdapter.Scale Q)
                     : Set (lsuc ℓ) where
  field
    endo : Endo K
    infl : _≤₂_ K (idEndo K) endo
    leFlow : _≤₂_ K endo (Flow-EndoAt K g)

mkClosureStepAt
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q} {g : QAdapter.Scale Q}
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K f (Flow-EndoAt K g)
  → ClosureStepAt K g
mkClosureStepAt f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

-- Categorical (right-to-left) composition.
infixr 9 _∘StepAt_
_∘StepAt_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q}
    {g₁ g₂ : QAdapter.Scale Q}
  → ClosureStepAt K g₂ → ClosureStepAt K g₁ → ClosureStepAt K (QAdapter._·_ Q g₁ g₂)
_∘StepAt_ {Sig = Sig} {Q = Q} {K = K} {g₁} {g₂} s₂ s₁ =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      f = ClosureStepAt.endo s₁
      g = ClosureStepAt.endo s₂
      inflf = ClosureStepAt.infl s₁
      inflg = ClosureStepAt.infl s₂
      f≤Flow  = ClosureStepAt.leFlow s₁
      g≤Flow  = ClosureStepAt.leFlow s₂
      inflComp : _≤₂_ K (idEndo K) (g ∘E f)
      inflComp = λ c → ConPoset.trans CP (inflf c) (inflg (Endo.fn f c))
      leTFComp : _≤₂_ K (g ∘E f) (Flow-EndoAt K (QAdapter._·_ Q g₁ g₂))
      leTFComp = λ c →
        let step₁ = Endo.mono g (f≤Flow c)          -- g(f c) ≤ g(Flow g₁ c)
            step₂ = g≤Flow (GradedClosure.Flow GTruth g₁ c)
            step₃ = GradedClosure.comp-lax GTruth g₁ g₂ c
        in ConPoset.trans CP step₁ (ConPoset.trans CP step₂ step₃)
  in mkClosureStepAt (g ∘E f) inflComp leTFComp

-- Flow-closing at a chosen grade (grade squares to g · g).

Flow-closeEndoAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → Endo K → Endo K
Flow-closeEndoAt K g f = (Flow-EndoAt K g) ∘E f

id≤Flow-closeAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndoAt K g f)
id≤Flow-closeAt {Sig = Sig} {Q = Q} K g id≤FlowAt f id≤f = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPoset.trans CP (id≤f c) (id≤FlowAt (Endo.fn f c))

Flow-close≤FlowAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-EndoAt K g)
  → _≤₂_ K (Flow-closeEndoAt K g f) (Flow-EndoAt K (QAdapter._·_ Q g g))
Flow-close≤FlowAt {Sig = Sig} {Q = Q} K g f f≤Flow = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      monoFlow = GradedClosure.mono GTruth {g = g}
      step₁ = monoFlow (f≤Flow c)          -- Flow g (f c) ≤ Flow g (Flow g c)
      step₂ = GradedClosure.comp-lax GTruth g g c
  in ConPoset.trans CP step₁ step₂

FlowStepAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → ClosureStepAt K g
FlowStepAt K g id≤FlowAt =
  mkClosureStepAt (Flow-EndoAt K g) id≤FlowAt (refl₂ K (Flow-EndoAt K g))

Flow-closeStepAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → ClosureStepAt K g
  → ClosureStepAt K (QAdapter._·_ Q g g)
Flow-closeStepAt K g id≤FlowAt s =
  mkClosureStepAt
    (Flow-closeEndoAt K g (ClosureStepAt.endo s))
    (id≤Flow-closeAt K g id≤FlowAt (ClosureStepAt.endo s) (ClosureStepAt.infl s))
    (Flow-close≤FlowAt K g (ClosureStepAt.endo s) (ClosureStepAt.leFlow s))

-- Left-to-right composition (grade order matches operand order).
infixl 9 _thenStepAt_
_thenStepAt_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q}
    {g₁ g₂ : QAdapter.Scale Q}
  → ClosureStepAt K g₁ → ClosureStepAt K g₂ → ClosureStepAt K (QAdapter._·_ Q g₁ g₂)
_thenStepAt_ s₁ s₂ = s₂ ∘StepAt s₁

promoteStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q} {g g' : QAdapter.Scale Q}
  → QAdapter._≤s_ Q g g'
  → ClosureStepAt K g → ClosureStepAt K g'
promoteStep {Sig = Sig} {Q = Q} {K = K} {g} {g'} le s =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      leFlow' : _≤₂_ K (ClosureStepAt.endo s) (Flow-EndoAt K g')
      leFlow' = λ c →
        ConPoset.trans CP (ClosureStepAt.leFlow s c)
          (GradedClosure.mono-grade GTruth le c)
  in mkClosureStepAt (ClosureStepAt.endo s) (ClosureStepAt.infl s) leFlow'

toSatStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q} {g : QAdapter.Scale Q}
  → ClosureStepAt K g → ClosureStep K
toSatStep {Sig = Sig} {Q = Q} {K = K} {g} s =
  let open GradedKernel K
      le = GradedClosure.sat-top GTruth g
  in mkClosureStep
       (ClosureStepAt.endo s)
       (ClosureStepAt.infl s)
       (ClosureStepAt.leFlow (promoteStep le s))

fromSatStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ClosureStep K → ClosureStepAt K (GradedClosure.sat (GradedKernel.GTruth K))
fromSatStep K s =
  mkClosureStepAt (ClosureStep.endo s) (ClosureStep.infl s) (ClosureStep.leFlow s)

FlowStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → ClosureStep K
FlowStep K = mkClosureStep (Flow-Endo K) (id≤Flow K) (refl₂ K (Flow-Endo K))
