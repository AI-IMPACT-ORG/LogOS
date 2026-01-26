{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.EndoCore public
import LogOS.Kernel.LogicKernel.EndoRelative as EndoRel

-- Boundary endomaps and pointwise refinements for a given `LogicKernel` K.
-- This is the common DSL behind both ungraded and graded kernels, instantiated
-- at the saturation step.

infixr 9 _∘Step_
infixl 9 _thenStep_

-- Flow at saturation as an endomap.

FlowClosure
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ClosureOp (BulkBoundary.bnd (LogicKernel.BB K))
FlowClosure K =
  let open LogicKernel K in
  record
    { cl        = GTier.Flow G (GTier.sat G)
    ; mono      = GTier.mono G
    ; infl      = GTier.infl-sat G
    ; idemp-lax = GTier.idemp-sat G
    }

Flow-Endo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
            (K : LogicKernel Sig Q) → Endo K
Flow-Endo K .Endo.fn = cl (FlowClosure K)
Flow-Endo K .Endo.mono = mono-cl (FlowClosure K)

id≤Flow : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
          (K : LogicKernel Sig Q) → _≤₂_ K (idEndo K) (Flow-Endo K)
id≤Flow K = infl (FlowClosure K)

Flow∘Flow≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q) → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
Flow∘Flow≤Flow K = idemp-lax (FlowClosure K)

-- Flow-closure of an endomap: “apply f, then take Flow-shadow”.

Flow-closeEndo
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q) → Endo K → Endo K
Flow-closeEndo K = Rel.J-closeEndo
  where
    module Rel = EndoRel.With K (FlowClosure K)

id≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
id≤Flow-close K = Rel.id≤J-close
  where
    module Rel = EndoRel.With K (FlowClosure K)

Flow-close≤Flow
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q) (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
Flow-close≤Flow K = Rel.J-close≤J
  where
    module Rel = EndoRel.With K (FlowClosure K)

Flow≤Flow-close
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q) (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
Flow≤Flow-close K = Rel.J≤J-close
  where
    module Rel = EndoRel.With K (FlowClosure K)

-- Closure steps: endomaps with `id ≤ f ≤ Flow`, closed under composition.

record ClosureStep {ℓ : Level}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : LogicKernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    endo : Endo K
    infl : _≤₂_ K (idEndo K) endo
    leFlow : _≤₂_ K endo (Flow-Endo K)

mkClosureStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : LogicKernel Sig Q}
  → (f : Endo K)
  → _≤₂_ K (idEndo K) f
  → _≤₂_ K f (Flow-Endo K)
  → ClosureStep K
mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

Flow-closeStep
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ClosureStep K → ClosureStep K
Flow-closeStep K s =
  let
    module Rel = EndoRel.With K (FlowClosure K)

    toRel : ClosureStep K → Rel.ClosureStep
    toRel s = Rel.mkClosureStep (ClosureStep.endo s) (ClosureStep.infl s) (ClosureStep.leFlow s)

    fromRel : Rel.ClosureStep → ClosureStep K
    fromRel s = mkClosureStep (Rel.endo s) (Rel.infl s) (Rel.leJ s)
  in
  fromRel (Rel.J-closeStep (toRel s))

_∘Step_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : LogicKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_∘Step_ {K = K} s₂ s₁ =
  let
    module Rel = EndoRel.With K (FlowClosure K)

    toRel : ClosureStep K → Rel.ClosureStep
    toRel s = Rel.mkClosureStep (ClosureStep.endo s) (ClosureStep.infl s) (ClosureStep.leFlow s)

    fromRel : Rel.ClosureStep → ClosureStep K
    fromRel s = mkClosureStep (Rel.endo s) (Rel.infl s) (Rel.leJ s)
  in
  fromRel (Rel._∘Step_ (toRel s₂) (toRel s₁))

-- Left-to-right composition (operand order matches execution order).
_thenStep_
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : LogicKernel Sig Q}
  → ClosureStep K → ClosureStep K → ClosureStep K
_thenStep_ s₁ s₂ = s₂ ∘Step s₁

-- Canonical guarded fixed-point helpers exposed via the endomap DSL.

Th⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : LogicKernel Sig Q) → ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K))
Th⋆K K = GTier.Th* (LogicKernel.G K)

FlowTh⋆K : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
           (K : LogicKernel Sig Q) → ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K))
FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

Th⋆≤FlowTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
Th⋆≤FlowTh⋆ K = fst (GTier.Th*-fixed (LogicKernel.G K))

FlowTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
FlowTh⋆≤Th⋆ K = snd (GTier.Th*-fixed (LogicKernel.G K))

FlowTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (po : BulkBoundaryPO (LogicKernel.BB K)) -- ANTISYM-OK
  → FlowTh⋆K K ≡ Th⋆K K
FlowTh⋆≡Th⋆ K po =
  let open BulkBoundaryPO po using (po-bnd) -- ANTISYM-OK
      open PartialOrder po-bnd using (antisym) -- ANTISYM-OK
  in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K) -- ANTISYM-OK

-- Textbook alias: antisymmetry upgrades the fixed-point inequalities to an equation.

fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆ -- ANTISYM-OK

Flow≤f→Th⋆≤fTh⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K))
      (Th⋆K K) (Endo.fn f (Th⋆K K))
Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
  let open LogicKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

f≤Flow→fTh⋆≤Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (f : Endo K)
  → _≤₂_ K f (Flow-Endo K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (LogicKernel.BB K))
      (Endo.fn f (Th⋆K K)) (Th⋆K K)
f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
  let open LogicKernel K
      CP = BulkBoundary.bnd BB
  in ConPreorder.trans CP (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

Flow≃f→fTh⋆≡Th⋆
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
    (po : BulkBoundaryPO (LogicKernel.BB K)) -- ANTISYM-OK
    (f : Endo K)
  → _≤₂_ K (Flow-Endo K) f
  → _≤₂_ K f (Flow-Endo K)
  → Endo.fn f (Th⋆K K) ≡ Th⋆K K
Flow≃f→fTh⋆≡Th⋆ K po f tf≤f f≤tf =
  let open BulkBoundaryPO po using (po-bnd) -- ANTISYM-OK
      open PartialOrder po-bnd using (antisym) -- ANTISYM-OK
  in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f) -- ANTISYM-OK
