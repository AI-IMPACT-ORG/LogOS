{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

-- Boundary endomaps and fixed-point helpers for a graded kernel.
--
-- This is the graded analogue of:
-- - `LogOS.Kernel.EndoCore` + `LogOS.Kernel.Endo` (CHL-facing `Kernel`), and
-- - `LogOS.Kernel.UngradedKernel.EndoCore` + `LogOS.Kernel.UngradedKernel.Endo`.
--
-- The main extra structure here is the grade-indexed Flow (`Flow-EndoAt`) and
-- grade-indexed closure steps (`ClosureStepAt`), together with a saturation
-- view (`ClosureStep`) instantiated at `sat`.

infix 4 _≤₂_
infix 4 _≈₂_
infixr 9 _∘E_

record Endo {ℓ : Level}
            {Sig : LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            (K   : GradedKernel Sig Q)
            : Set (lsuc ℓ) where
  open GradedKernel K
  private
    Con∂ = ConPreorder.Con (BulkBoundary.bnd BB)
    _≤_  = ConPreorder._⊑_ (BulkBoundary.bnd BB)
  field
    fn   : Con∂ → Con∂
    mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

open Endo public

_≤₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : GradedKernel Sig Q) → Endo K → Endo K → Set ℓ
_≤₂_ {ℓ} {Sig} {Q} K f g = ∀ c →
  let open GradedKernel K in
  ConPreorder._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) (Endo.fn g c)

-- Mutual refinement between endomaps (pointwise, in the boundary preorder).
_≈₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : GradedKernel Sig Q) → Endo K → Endo K → Set ℓ
_≈₂_ K f g = (_≤₂_ K f g) × (_≤₂_ K g f)

idEndo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : GradedKernel Sig Q) → Endo K
idEndo K .Endo.fn   = λ c → c
idEndo K .Endo.mono = λ p → p

_∘E_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : GradedKernel Sig Q} → Endo K → Endo K → Endo K
_∘E_ {K = K} f g .Endo.fn   = λ c → Endo.fn f (Endo.fn g c)
_∘E_ {K = K} f g .Endo.mono = λ p → Endo.mono f (Endo.mono g p)

refl₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        (K : GradedKernel Sig Q) (f : Endo K) → _≤₂_ K f f
refl₂ K f = λ _ →
  let open GradedKernel K in
  ConPreorder.refl (BulkBoundary.bnd BB)

trans₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : GradedKernel Sig Q)
         {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
trans₂ K fg gh = λ c →
  let open GradedKernel K in
  ConPreorder.trans (BulkBoundary.bnd BB) (fg c) (gh c)

≈₂-refl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q) (f : Endo K) → _≈₂_ K f f
≈₂-refl K f = (refl₂ K f , refl₂ K f)

≈₂-sym
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q} {f g : Endo K}
  → _≈₂_ K f g → _≈₂_ K g f
≈₂-sym (fg , gf) = (gf , fg)

≈₂-trans
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    {f g h : Endo K}
  → _≈₂_ K f g → _≈₂_ K g h → _≈₂_ K f h
≈₂-trans K {f} {g} {h} (fg , gf) (gh , hg) =
  ( trans₂ K {f = f} {g = g} {h = h} fg gh
  , trans₂ K {f = h} {g = g} {h = f} hg gf
  )

-- Flow at an arbitrary grade as an endomap.

Flow-EndoAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → QAdapter.Scale Q
  → Endo K
Flow-EndoAt {Q = Q} K g .Endo.fn =
  GradedClosure.Flow (GradedKernel.GTruth K) g
Flow-EndoAt {Q = Q} K g .Endo.mono =
  GradedClosure.mono (GradedKernel.GTruth K) {g = g}

-- Flow at saturation (cost → ∞).

Flow-Endo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Endo K
Flow-Endo K = Flow-EndoAt K (GradedClosure.sat (GradedKernel.GTruth K))

id≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → _≤₂_ K (idEndo K) (Flow-Endo K)
id≤Flow K =
  let open GradedKernel K in
  GradedClosure.infl-sat GTruth

Flow∘Flow≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
Flow∘Flow≤Flow K =
  let open GradedKernel K in
  GradedClosure.idemp-sat GTruth

-- Grade monotonicity and composition for Flow endomaps (lax monoid action).

Flow-EndoAt-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    {g g' : QAdapter.Scale Q}
  → QAdapter._≤s_ Q g g'
  → _≤₂_ K (Flow-EndoAt K g) (Flow-EndoAt K g')
Flow-EndoAt-mono {Q = Q} K g≤g' = λ c →
  let open GradedKernel K in
  GradedClosure.mono-grade GTruth g≤g' c

Flow-EndoAt-comp≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g g' : QAdapter.Scale Q)
  → _≤₂_ K ((Flow-EndoAt K g') ∘E (Flow-EndoAt K g))
           (Flow-EndoAt K (QAdapter._·_ Q g g'))
Flow-EndoAt-comp≤ {Q = Q} K g g' = λ c →
  let open GradedKernel K in
  GradedClosure.comp-lax GTruth g g' c

Flow-EndoAt≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (Flow-EndoAt K g) (Flow-Endo K)
Flow-EndoAt≤Flow {Q = Q} K g =
  Flow-EndoAt-mono K (GradedClosure.sat-top (GradedKernel.GTruth K) g)

Step-Endo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Endo K
Step-Endo K = Flow-EndoAt K (GradedKernel.step-grade K)

stepFlow≤satFlow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → _≤₂_ K (Step-Endo K) (Flow-Endo K)
stepFlow≤satFlow K = Flow-EndoAt≤Flow K (GradedKernel.step-grade K)

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
_∘StepAt_ {Q = Q} {K = K} {g₁} {g₂} s₂ s₁ =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      f = ClosureStepAt.endo s₁
      g = ClosureStepAt.endo s₂
      inflf = ClosureStepAt.infl s₁
      inflg = ClosureStepAt.infl s₂
      f≤Flow  = ClosureStepAt.leFlow s₁
      g≤Flow  = ClosureStepAt.leFlow s₂
      inflComp : _≤₂_ K (idEndo K) (g ∘E f)
      inflComp = λ c → ConPreorder.trans CP (inflf c) (inflg (Endo.fn f c))
      leTFComp : _≤₂_ K (g ∘E f) (Flow-EndoAt K (QAdapter._·_ Q g₁ g₂))
      leTFComp = λ c →
        let step₁ = Endo.mono g (f≤Flow c)          -- g(f c) ≤ g(Flow g₁ c)
            step₂ = g≤Flow (GradedClosure.Flow GTruth g₁ c)
            step₃ = GradedClosure.comp-lax GTruth g₁ g₂ c
        in ConPreorder.trans CP step₁ (ConPreorder.trans CP step₂ step₃)
  in mkClosureStepAt (g ∘E f) inflComp leTFComp

-- Flow-closing at a chosen grade (grade squares to g · g).

Flow-closeEndoAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → Endo K → Endo K
Flow-closeEndoAt K g f = (Flow-EndoAt K g) ∘E f

-- Specialisation: close at saturation.

Flow-closeEndo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Endo K → Endo K
Flow-closeEndo K = Flow-closeEndoAt K (GradedClosure.sat (GradedKernel.GTruth K))

id≤Flow-closeAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndoAt K g f)
id≤Flow-closeAt K g id≤FlowAt' f id≤f = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (id≤f c) (id≤FlowAt' (Endo.fn f c))

Flow-close≤FlowAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-EndoAt K g)
  → _≤₂_ K (Flow-closeEndoAt K g f) (Flow-EndoAt K (QAdapter._·_ Q g g))
Flow-close≤FlowAt {Q = Q} K g f f≤Flow = λ c →
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      monoFlow = GradedClosure.mono GTruth {g = g}
      step₁ = monoFlow (f≤Flow c)          -- Flow g (f c) ≤ Flow g (Flow g c)
      step₂ = GradedClosure.comp-lax GTruth g g c
  in ConPreorder.trans CP step₁ step₂

FlowStepAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → ClosureStepAt K g
FlowStepAt K g id≤FlowAt' =
  mkClosureStepAt (Flow-EndoAt K g) id≤FlowAt' (refl₂ K (Flow-EndoAt K g))

Flow-closeStepAt
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (g : QAdapter.Scale Q)
  → _≤₂_ K (idEndo K) (Flow-EndoAt K g)
  → ClosureStepAt K g
  → ClosureStepAt K (QAdapter._·_ Q g g)
Flow-closeStepAt K g id≤FlowAt' s =
  mkClosureStepAt
    (Flow-closeEndoAt K g (ClosureStepAt.endo s))
    (id≤Flow-closeAt K g id≤FlowAt' (ClosureStepAt.endo s) (ClosureStepAt.infl s))
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
promoteStep {K = K} {g = g} {g' = g'} le s =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
      leFlow' : _≤₂_ K (ClosureStepAt.endo s) (Flow-EndoAt K g')
      leFlow' = λ c →
        ConPreorder.trans CP (ClosureStepAt.leFlow s c)
          (GradedClosure.mono-grade GTruth le c)
  in mkClosureStepAt (ClosureStepAt.endo s) (ClosureStepAt.infl s) leFlow'

-- Saturation-view closure steps (`sat` grade).

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

toSatStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : GradedKernel Sig Q} {g : QAdapter.Scale Q}
  → ClosureStepAt K g → ClosureStep K
toSatStep {K = K} {g} s =
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

-- Canonical guarded fixed-point helpers exposed via the endomap DSL.

Th⋆K
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))
Th⋆K K = GradedClosure.Th* (GradedKernel.GTruth K)

FlowTh⋆K
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K))
FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

Th⋆≤FlowTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
Th⋆≤FlowTh⋆ K = GradedClosure.Th*-fixed⇒ (GradedKernel.GTruth K)

FlowTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
FlowTh⋆≤Th⋆ K = GradedClosure.Th*-fixed⇐ (GradedKernel.GTruth K)

FlowTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (po : BulkBoundaryPO (GradedKernel.BB K))
  → FlowTh⋆K K ≡ Th⋆K K
FlowTh⋆≡Th⋆ K po =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K)

fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆

Flow≤f→Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

f≤Flow→fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
  let open GradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

Flow≈₂f→fTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (po : BulkBoundaryPO (GradedKernel.BB K))
    (f : Endo K)
  → _≈₂_ K (Flow-Endo K) f
  → Endo.fn f (Th⋆K K) ≡ Th⋆K K
Flow≈₂f→fTh⋆≡Th⋆ K po f (tf≤f , f≤tf) =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f)
