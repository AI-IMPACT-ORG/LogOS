{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.UngradedKernel.EndoCore public
import LogOS.Kernel.UngradedKernel.EndoRelative as EndoRel

-- Boundary endomaps and pointwise refinements for a given `UngradedKernel` K.
--
-- This is the ungraded analogue of `LogOS.Kernel.Endo` (the CHL-facing `Kernel`
-- interface), using the `GTruth` closure directly.

infixr 9 _∘Step_
infixl 9 _thenStep_

-- Flow as a closure op on boundary constraints.

FlowClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ClosureOp (BulkBoundary.bnd (UngradedKernel.BB K))
FlowClosure K =
  record
    { cl        = Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K)
    ; mono      = Truth.GuardedCore.GuardedClosure.mono (UngradedKernel.GTruth K)
    ; infl      = Truth.GuardedCore.GuardedClosure.infl (UngradedKernel.GTruth K)
    ; idemp-lax = Truth.GuardedCore.GuardedClosure.idemp-lax (UngradedKernel.GTruth K)
    }

Flow-Endo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Endo K
Flow-Endo K .Endo.fn = cl (FlowClosure K)
Flow-Endo K .Endo.mono = mono-cl (FlowClosure K)

id≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → _≤₂_ K (idEndo K) (Flow-Endo K)
id≤Flow K = infl (FlowClosure K)

Flow∘Flow≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
Flow∘Flow≤Flow K = idemp-lax (FlowClosure K)

-- Flow-closure of an endomap: “apply f, then take Flow-shadow”.

Flow-closeEndo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → Endo K → Endo K
Flow-closeEndo K = Rel.J-closeEndo
  where
    module Rel = EndoRel.With K (FlowClosure K)

id≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
id≤Flow-close K = Rel.id≤J-close
  where
    module Rel = EndoRel.With K (FlowClosure K)

Flow-close≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
Flow-close≤Flow K = Rel.J-close≤J
  where
    module Rel = EndoRel.With K (FlowClosure K)

Flow≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
Flow≤Flow-close K = Rel.J≤J-close
  where
    module Rel = EndoRel.With K (FlowClosure K)

-- Closure steps: endomaps with `id ≤ f ≤ Flow`, closed under composition.

record ClosureStep {ℓ : Level}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : UngradedKernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    endo : Endo K
    infl : _≤₂_ K (idEndo K) endo
    leFlow : _≤₂_ K endo (Flow-Endo K)

mkClosureStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : UngradedKernel Sig Q}
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K f (Flow-Endo K)
  → ClosureStep K
mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

Flow-closeStep
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : UngradedKernel Sig Q}
  → ClosureStep K → ClosureStep K
Flow-closeStep {K = K} s =
  let
    module Rel = EndoRel.With K (FlowClosure K)

    toRel : ClosureStep K → Rel.ClosureStep
    toRel t = Rel.mkClosureStep (ClosureStep.endo t) (ClosureStep.infl t) (ClosureStep.leFlow t)

    fromRel : Rel.ClosureStep → ClosureStep K
    fromRel t = mkClosureStep (Rel.endo t) (Rel.infl t) (Rel.leJ t)
  in
  fromRel (Rel.J-closeStep (toRel s))

_∘Step_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : UngradedKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_∘Step_ {K = K} s₂ s₁ =
  let
    module Rel = EndoRel.With K (FlowClosure K)

    toRel : ClosureStep K → Rel.ClosureStep
    toRel t = Rel.mkClosureStep (ClosureStep.endo t) (ClosureStep.infl t) (ClosureStep.leFlow t)

    fromRel : Rel.ClosureStep → ClosureStep K
    fromRel t = mkClosureStep (Rel.endo t) (Rel.infl t) (Rel.leJ t)
  in
  fromRel (Rel._∘Step_ (toRel s₂) (toRel s₁))

-- Left-to-right composition (operand order matches execution order).
_thenStep_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : UngradedKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_thenStep_ s₁ s₂ = s₂ ∘Step s₁

-- Canonical guarded fixed-point helpers exposed via the endomap DSL.

Th⋆K
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (UngradedKernel.BB K))
Th⋆K K = Truth.GuardedCore.GuardedClosure.Th* (UngradedKernel.GTruth K)

FlowTh⋆K
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ConPreorder.Con (BulkBoundary.bnd (UngradedKernel.BB K))
FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

Th⋆≤FlowTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
Th⋆≤FlowTh⋆ K = Truth.GuardedCore.GuardedClosure.Th*-fixed⇒ (UngradedKernel.GTruth K)

FlowTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
FlowTh⋆≤Th⋆ K = Truth.GuardedCore.GuardedClosure.Th*-fixed⇐ (UngradedKernel.GTruth K)

FlowTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (po : BulkBoundaryPO (UngradedKernel.BB K))
  → FlowTh⋆K K ≡ Th⋆K K
FlowTh⋆≡Th⋆ K po =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K)

-- Textbook alias: antisymmetry upgrades the fixed-point inequalities to an equation.

fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆

Flow≤f→Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
  let open UngradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

f≤Flow→fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
  let open UngradedKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

Flow≈₂f→fTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UngradedKernel Sig Q)
    (po : BulkBoundaryPO (UngradedKernel.BB K))
    (f : Endo K)
  → _≈₂_ K (Flow-Endo K) f
  → Endo.fn f (Th⋆K K) ≡ Th⋆K K
Flow≈₂f→fTh⋆≡Th⋆ K po f (tf≤f , f≤tf) =
  let open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
  in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f)
