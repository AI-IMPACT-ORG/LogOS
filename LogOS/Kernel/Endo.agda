{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel

-- Boundary endomaps and pointwise refinements for a given kernel K.
-- This is the canonical DSL: endomaps, refinement `_≤₂_`, composition `_∘E_`,
-- and the distinguished Flow endomap with its fixed-point helpers.

infix 4 _≤₂_
infixr 9 _∘E_
infixr 9 _∘Step_
infixl 9 _thenStep_

record Endo {ℓ : Level}
            {Sig : LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            (K   : Kernel Sig Q)
            : Set (lsuc ℓ) where
  open Kernel K
  private
    Con∂ = ConPoset.Con (BulkBoundary.bnd BB)
    _≤_  = ConPoset._⊑_ (BulkBoundary.bnd BB)
  field
    fn   : Con∂ → Con∂
    mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

open Endo public

-- Pointwise refinement between endomaps.
_≤₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : Kernel Sig Q) → Endo K → Endo K → Set ℓ
_≤₂_ {ℓ} {Sig} {Q} K f g = ∀ c →
  let open Kernel K in
  ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) (Endo.fn g c)

-- Identity and composition on endomaps.

idEndo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) → Endo K
idEndo K .Endo.fn   = λ c → c
idEndo K .Endo.mono = λ p → p

_∘E_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : Kernel Sig Q} → Endo K → Endo K → Endo K
_∘E_ {K = K} f g .Endo.fn   = λ c → Endo.fn f (Endo.fn g c)
_∘E_ {K = K} f g .Endo.mono = λ p → Endo.mono f (Endo.mono g p)

-- Refinement basics.

refl₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        (K : Kernel Sig Q) (f : Endo K) → _≤₂_ K f f
refl₂ K f = λ _ →
  let open Kernel K in
  ConPoset.refl (BulkBoundary.bnd BB)

trans₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q)
         {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
trans₂ K fg gh = λ c →
  let open Kernel K in
  ConPoset.trans (BulkBoundary.bnd BB) (fg c) (gh c)

-- Whiskering: composition preserves refinement on either side.

whisker-left : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
               (K : Kernel Sig Q)
               {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (h ∘E f) (h ∘E g)
whisker-left K {f} {g} {h} fg = λ c → Endo.mono h (fg c)

whisker-right : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                (K : Kernel Sig Q)
                {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K (f ∘E h) (g ∘E h)
whisker-right K {f} {g} {h} fg = λ c → fg (Endo.fn h c)

-- Flow as an endomap and canonical refinements.

Flow-Endo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
            (K : Kernel Sig Q) → Endo K
Flow-Endo {Sig = Sig} {Q = Q} K .Endo.fn =
  let module GT0 = Truth.GuardedTruth Sig Q in
  GT0.GuardedClosure.Flow (Kernel.GTruth K)
Flow-Endo {Sig = Sig} {Q = Q} K .Endo.mono =
  let module GT0 = Truth.GuardedTruth Sig Q in
  GT0.GuardedClosure.mono (Kernel.GTruth K)

-- Flow-closure of an endomap: “apply f, then take Flow-shadow”.
--
-- Once you have `id ≤ f ≤ Flow`, Flow-closing preserves those bounds and makes
-- Flow-boundedness stable under composition by whiskering.

Flow-closeEndo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Endo K → Endo K
Flow-closeEndo K f = (Flow-Endo K) ∘E f

id≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
id≤Flow-close {Sig = Sig} {Q = Q} K f id≤f = λ c →
  let open Kernel K
      CP = BulkBoundary.bnd BB
      inflFlow =
        (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.infl (Kernel.GTruth K))
          (Endo.fn f c)
  in ConPoset.trans CP (id≤f c) inflFlow

Flow-close≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
Flow-close≤Flow {Sig = Sig} {Q = Q} K f f≤Flow = λ c →
  let open Kernel K
      CP = BulkBoundary.bnd BB
      monoFlow = (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.mono) (Kernel.GTruth K)
      idemFlow = (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.idemp-lax) (Kernel.GTruth K)
      step₁ = monoFlow (f≤Flow c)              -- Flow(f c) ≤ Flow(Flow c)
      step₂ = idemFlow c                       -- Flow(Flow c) ≤ Flow c
  in ConPoset.trans CP step₁ step₂

Flow≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
Flow≤Flow-close {Sig = Sig} {Q = Q} K f id≤f = λ c →
  let open Kernel K
      CP = BulkBoundary.bnd BB
      monoFlow = (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.mono) (Kernel.GTruth K)
  in monoFlow (id≤f c)

-- Canonical “closure step” API ------------------------------------------------
-- For domain authors: a closure step is any endomap sandwiched by `id ≤ _ ≤ Flow`.
-- These are compositional, and Flow-closing is the canonical way to build them.

record ClosureStep {ℓ : Level}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    endo : Endo K
    infl : _≤₂_ K (idEndo K) endo
    leFlow : _≤₂_ K endo (Flow-Endo K)

mkClosureStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K f (Flow-Endo K)
  → ClosureStep K
mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

Flow-closeStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ClosureStep K → ClosureStep K
Flow-closeStep K s =
  mkClosureStep
    (Flow-closeEndo K (ClosureStep.endo s))
    (id≤Flow-close K (ClosureStep.endo s) (ClosureStep.infl s))
    (Flow-close≤Flow K (ClosureStep.endo s) (ClosureStep.leFlow s))

_∘Step_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_∘Step_ {Sig = Sig} {Q = Q} {K = K} s₂ s₁ =
  let open Kernel K
      CP = BulkBoundary.bnd BB
      monoFlow = Endo.mono (Flow-Endo K)
      idemFlow = (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.idemp-lax) (Kernel.GTruth K)
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
_thenStep_ : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
             {K : Kernel Sig Q}
           → ClosureStep K → ClosureStep K → ClosureStep K
_thenStep_ s₁ s₂ = s₂ ∘Step s₁

id≤Flow : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          (K : Kernel Sig Q) → _≤₂_ K (idEndo K) (Flow-Endo K)
id≤Flow {Sig = Sig} {Q = Q} K = λ c →
  (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.infl (Kernel.GTruth K)) c

Flow∘Flow≤Flow : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                 (K : Kernel Sig Q) → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
Flow∘Flow≤Flow {Sig = Sig} {Q = Q} K = λ c →
  (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.idemp-lax (Kernel.GTruth K)) c

-- Canonical guarded fixed-point helpers exposed via the endomap DSL.

Th⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : Kernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
Th⋆K {Sig = Sig} {Q = Q} K =
  let module GT0 = Truth.GuardedTruth Sig Q in
  GT0.GuardedClosure.Th* (Kernel.GTruth K)

FlowTh⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           (K : Kernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

Th⋆≤FlowTh⋆ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : Kernel Sig Q)
            → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
Th⋆≤FlowTh⋆ {Sig = Sig} {Q = Q} K =
  fst (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.Th*-fixed (Kernel.GTruth K))

FlowTh⋆≤Th⋆ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : Kernel Sig Q)
            → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
FlowTh⋆≤Th⋆ {Sig = Sig} {Q = Q} K =
  snd (let module GT0 = Truth.GuardedTruth Sig Q in GT0.GuardedClosure.Th*-fixed (Kernel.GTruth K))

FlowTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (po : BulkBoundaryPO (Kernel.BB K))
  → FlowTh⋆K K ≡ Th⋆K K
FlowTh⋆≡Th⋆ K po =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K)

-- Textbook alias: antisymmetry upgrades the fixed-point inequalities to an equation.

fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆

Flow≤f→Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
  let open Kernel K
  in ConPoset.trans (BulkBoundary.bnd BB) (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

f≤Flow→fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
  let open Kernel K
  in ConPoset.trans (BulkBoundary.bnd BB) (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

Flow≃f→fTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (po : BulkBoundaryPO (Kernel.BB K))
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → _≤₂_ K f (Flow-Endo K)
  → Endo.fn f (Th⋆K K) ≡ Th⋆K K
Flow≃f→fTh⋆≡Th⋆ K po f tf≤f f≤tf =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f)

-- ASCII aliases for the Th⋆ helpers (to avoid mixed star symbols).

ThStarK : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          (K : Kernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
ThStarK = Th⋆K

FlowThStarK : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
              (K : Kernel Sig Q) → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K))
FlowThStarK = FlowTh⋆K

ThStar≤FlowThStar : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                    (K : Kernel Sig Q)
                  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (ThStarK K) (FlowThStarK K)
ThStar≤FlowThStar = Th⋆≤FlowTh⋆

FlowThStar≤ThStar : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                    (K : Kernel Sig Q)
                  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (FlowThStarK K) (ThStarK K)
FlowThStar≤ThStar = FlowTh⋆≤Th⋆

FlowThStar≡ThStar
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (po : BulkBoundaryPO (Kernel.BB K))
  → FlowThStarK K ≡ ThStarK K
FlowThStar≡ThStar = FlowTh⋆≡Th⋆

Flow≤f→ThStar≤fThStar
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (ThStarK K) (Endo.fn f (ThStarK K))
Flow≤f→ThStar≤fThStar = Flow≤f→Th⋆≤fTh⋆

f≤Flow→fThStar≤ThStar
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Endo.fn f (ThStarK K)) (ThStarK K)
f≤Flow→fThStar≤ThStar = f≤Flow→fTh⋆≤Th⋆

Flow≃f→fThStar≡ThStar
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (po : BulkBoundaryPO (Kernel.BB K))
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → _≤₂_ K f (Flow-Endo K)
  → Endo.fn f (ThStarK K) ≡ ThStarK K
Flow≃f→fThStar≡ThStar = Flow≃f→fTh⋆≡Th⋆
