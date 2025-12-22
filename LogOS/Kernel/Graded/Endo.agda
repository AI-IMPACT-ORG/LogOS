{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
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

-- Boundary endomaps and fixed-point helpers for a graded kernel,
-- instantiated at the saturation grade.

infix 4 _≤₂_
infixr 9 _∘E_

record Endo {ℓ : Level}
            {Sig : LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            (K   : GradedKernel Sig Q)
            : Set (lsuc ℓ) where
  open GradedKernel K
  private
    Con∂ = ConPoset.Con (BulkBoundary.bnd BB)
    _≤_  = ConPoset._⊑_ (BulkBoundary.bnd BB)
  field
    fn   : Con∂ → Con∂
    mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

open Endo public

-- Pointwise refinement between endomaps.
_≤₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : GradedKernel Sig Q) → Endo K → Endo K → Set ℓ
_≤₂_ {ℓ} {Sig} {Q} K f g = ∀ c →
  let open GradedKernel K in
  ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) (Endo.fn g c)

-- Identity and composition on endomaps (categorical structure).

idEndo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : GradedKernel Sig Q) → Endo K
idEndo K .Endo.fn   = λ c → c
idEndo K .Endo.mono = λ p → p

_∘E_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : GradedKernel Sig Q} → Endo K → Endo K → Endo K
_∘E_ {K = K} f g .Endo.fn   = λ c → Endo.fn f (Endo.fn g c)
_∘E_ {K = K} f g .Endo.mono = λ p → Endo.mono f (Endo.mono g p)

-- Refinement basics.

refl₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        (K : GradedKernel Sig Q) (f : Endo K) → _≤₂_ K f f
refl₂ K f = λ _ →
  let open GradedKernel K in
  ConPoset.refl (BulkBoundary.bnd BB)

trans₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : GradedKernel Sig Q)
         {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
trans₂ K fg gh = λ c →
  let open GradedKernel K in
  ConPoset.trans (BulkBoundary.bnd BB) (fg c) (gh c)

-- Whiskering: composition preserves refinement on either side.

whisker-left : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
               (K : GradedKernel Sig Q)
               {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (h ∘E f) (h ∘E g)
whisker-left K {f} {g} {h} fg = λ c → Endo.mono h (fg c)

whisker-right : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                (K : GradedKernel Sig Q)
                {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (f ∘E h) (g ∘E h)
whisker-right K {f} {g} {h} fg = λ c → fg (Endo.fn h c)

-- Flow at an arbitrary grade as an endomap.

Flow-EndoAt : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : GradedKernel Sig Q) → QAdapter.Scale Q → Endo K
Flow-EndoAt {Sig = Sig} {Q = Q} K g .Endo.fn =
  GradedClosure.Flow (GradedKernel.GTruth K) g
Flow-EndoAt {Sig = Sig} {Q = Q} K g .Endo.mono =
  GradedClosure.mono (GradedKernel.GTruth K) {g = g}

-- Flow at saturation grade as an endomap.

Flow-Endo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
            (K : GradedKernel Sig Q) → Endo K
Flow-Endo {Sig = Sig} {Q = Q} K =
  Flow-EndoAt K (GradedClosure.sat (GradedKernel.GTruth K))

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

-- Flow-closure of an endomap: “apply f, then take Flow-shadow”.
--
-- Once you have `id ≤ f ≤ Flow`, Flow-closing preserves those bounds and makes
-- Flow-boundedness stable under composition by whiskering.

Flow-closeEndo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) → Endo K → Endo K
Flow-closeEndo K f = (Flow-Endo K) ∘E f

id≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
id≤Flow-close {Sig = Sig} {Q = Q} K f id≤f = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      inflFlow = GradedClosure.infl-sat GTruth (Endo.fn f c)
  in ConPoset.trans CP (id≤f c) inflFlow

Flow-close≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
Flow-close≤Flow {Sig = Sig} {Q = Q} K f f≤Flow = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      monoFlow = GradedClosure.mono GTruth {g = GradedClosure.sat GTruth}
      idemFlow = GradedClosure.idemp-sat GTruth
      step₁ = monoFlow (f≤Flow c)              -- Flow(f c) ≤ Flow(Flow c)
      step₂ = idemFlow c                       -- Flow(Flow c) ≤ Flow c
  in ConPoset.trans CP step₁ step₂

Flow≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
Flow≤Flow-close {Sig = Sig} {Q = Q} K f id≤f = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      monoFlow = GradedClosure.mono GTruth {g = GradedClosure.sat GTruth}
  in monoFlow (id≤f c)

-- Canonical “closure step” API ----------------------------------------------
-- For domain authors: a closure step is any endomap sandwiched by `id ≤ _ ≤ Flow`.
-- These are compositional, and Flow-closing is the canonical way to build them.

record ClosureStep {ℓ : Level}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : GradedKernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    endo : Endo K
    infl : _≤₂_ K (idEndo K) endo
    leFlow : _≤₂_ K endo (Flow-Endo K)

mkClosureStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q}
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K f (Flow-Endo K)
  → ClosureStep K
mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

Flow-closeStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ClosureStep K → ClosureStep K
Flow-closeStep K s =
  mkClosureStep
    (Flow-closeEndo K (ClosureStep.endo s))
    (id≤Flow-close K (ClosureStep.endo s) (ClosureStep.infl s))
    (Flow-close≤Flow K (ClosureStep.endo s) (ClosureStep.leFlow s))

infixr 9 _∘Step_
infixl 9 _thenStep_
_∘Step_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_∘Step_ {Sig = Sig} {Q = Q} {K = K} s₂ s₁ =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      monoFlow = Endo.mono (Flow-Endo K)
      idemFlow = GradedClosure.idemp-sat GTruth
      f = ClosureStep.endo s₁
      g = ClosureStep.endo s₂
      inflf = ClosureStep.infl s₁
      inflg = ClosureStep.infl s₂
      f≤Flow  = ClosureStep.leFlow s₁
      g≤Flow  = ClosureStep.leFlow s₂
      inflComp : _≤₂_ K (idEndo K) (g ∘E f)
      inflComp = λ c → ConPoset.trans CP (inflf c) (inflg (Endo.fn f c))
      leTFComp : _≤₂_ K (g ∘E f) (Flow-Endo K)
      leTFComp = λ c →
        let step₁ = g≤Flow (Endo.fn f c)            -- g(f c) ≤ Flow(f c)
            step₂ = monoFlow (f≤Flow c)             -- Flow(f c) ≤ Flow(Flow c)
            step₃ = idemFlow c                      -- Flow(Flow c) ≤ Flow c
        in ConPoset.trans CP step₁ (ConPoset.trans CP step₂ step₃)
  in mkClosureStep (g ∘E f) inflComp leTFComp

-- Left-to-right composition (operand order matches execution order).
_thenStep_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_thenStep_ s₁ s₂ = s₂ ∘Step s₁

id≤Flow : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          (K : GradedKernel Sig Q) → _≤₂_ K (idEndo K) (Flow-Endo K)
id≤Flow {Sig = Sig} {Q = Q} K = λ c →
  GradedClosure.infl-sat (GradedKernel.GTruth K) c

Flow∘Flow≤Flow : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                 (K : GradedKernel Sig Q) → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
Flow∘Flow≤Flow {Sig = Sig} {Q = Q} K = λ c →
  GradedClosure.idemp-sat (GradedKernel.GTruth K) c

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

-- Canonical guarded fixed-point helpers (saturation grade).

Th⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : GradedKernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K))
Th⋆K K = GradedClosure.Th* (GradedKernel.GTruth K)

FlowTh⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           (K : GradedKernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K))
FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

Th⋆≤FlowTh⋆ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : GradedKernel Sig Q)
            → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
Th⋆≤FlowTh⋆ K = fst (GradedClosure.Th*-fixed (GradedKernel.GTruth K))

FlowTh⋆≤Th⋆ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : GradedKernel Sig Q)
            → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
FlowTh⋆≤Th⋆ K = snd (GradedClosure.Th*-fixed (GradedKernel.GTruth K))

FlowTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (po : BulkBoundaryPO (GradedKernel.BB K))
  → FlowTh⋆K K ≡ Th⋆K K
FlowTh⋆≡Th⋆ K po =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K)

-- Textbook alias: antisymmetry upgrades the fixed-point inequalities to an equation.

fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆

Flow≤f→Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
  ConPoset.trans (BulkBoundary.bnd (GradedKernel.BB K)) (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

f≤Flow→fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
  ConPoset.trans (BulkBoundary.bnd (GradedKernel.BB K)) (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

Flow≃f→fTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (po : BulkBoundaryPO (GradedKernel.BB K))
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → _≤₂_ K f (Flow-Endo K)
  → Endo.fn f (Th⋆K K) ≡ Th⋆K K
Flow≃f→fTh⋆≡Th⋆ K po f tf≤f f≤tf =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f)
