{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoFlowShared where

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)

import LogOS.Kernel.EndoCoreShared as CoreShared
import LogOS.Kernel.EndoRelativeShared as RelShared

module With
  {ℓObj ℓ : Level}
  (Obj : Set ℓObj)
  (BBOf : Obj → BulkBoundary ℓ)
  (FlowClosure : (K : Obj) → ClosureOp (BulkBoundary.bnd (BBOf K)))
  (Th*Of : (K : Obj) → ConPreorder.Con (BulkBoundary.bnd (BBOf K)))
  (Th*fixed⇒ : (K : Obj) →
               ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K))
                 (Th*Of K)
                 (cl (FlowClosure K) (Th*Of K)))
  (Th*fixed⇐ : (K : Obj) →
               ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K))
                 (cl (FlowClosure K) (Th*Of K))
                 (Th*Of K))
  where

  module Core = CoreShared.With Obj BBOf
  module RelCore = RelShared.With Obj BBOf

  open Core public
    using
      ( Endo; _≤₂_; _≈₂_; idEndo; _∘E_
      ; refl₂; trans₂
      ; EndoPreorder; EndoThin2Cat
      ; EndoRelPreorder; EndoRelThin2Cat
      ; module Endo2Cat
      )
  open Endo public

  infixr 9 _∘Step_
  infixl 9 _thenStep_

  Flow-Endo : (K : Obj) → Endo K
  Flow-Endo K .Endo.fn = cl (FlowClosure K)
  Flow-Endo K .Endo.mono = mono-cl (FlowClosure K)

  id≤Flow : (K : Obj) → _≤₂_ K (idEndo K) (Flow-Endo K)
  id≤Flow K = infl (FlowClosure K)

  Flow∘Flow≤Flow : (K : Obj) → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
  Flow∘Flow≤Flow K = idemp-lax (FlowClosure K)

  Flow-closeEndo : (K : Obj) → Endo K → Endo K
  Flow-closeEndo K = Rel.J-closeEndo
    where
      module Rel = RelCore.For K (FlowClosure K)

  id≤Flow-close
    : (K : Obj) (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
  id≤Flow-close K = Rel.id≤J-close
    where
      module Rel = RelCore.For K (FlowClosure K)

  Flow-close≤Flow
    : (K : Obj) (f : Endo K)
    → _≤₂_ K f (Flow-Endo K)
    → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
  Flow-close≤Flow K = Rel.J-close≤J
    where
      module Rel = RelCore.For K (FlowClosure K)

  Flow≤Flow-close
    : (K : Obj) (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
  Flow≤Flow-close K = Rel.J≤J-close
    where
      module Rel = RelCore.For K (FlowClosure K)

  record ClosureStep (K : Obj) : Set (lsuc ℓ) where
    field
      endo : Endo K
      infl : _≤₂_ K (idEndo K) endo
      leFlow : _≤₂_ K endo (Flow-Endo K)

  mkClosureStep
    : ∀ {K : Obj}
    → (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → ClosureStep K
  mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

  Flow-closeStep
    : (K : Obj)
    → ClosureStep K → ClosureStep K
  Flow-closeStep K s =
    let
      module Rel = RelCore.For K (FlowClosure K)

      toRel : ClosureStep K → Rel.ClosureStep
      toRel t = Rel.mkClosureStep (ClosureStep.endo t) (ClosureStep.infl t) (ClosureStep.leFlow t)

      fromRel : Rel.ClosureStep → ClosureStep K
      fromRel t = mkClosureStep (Rel.endo t) (Rel.infl t) (Rel.leJ t)
    in
    fromRel (Rel.J-closeStep (toRel s))

  _∘Step_ : ∀ {K : Obj} → ClosureStep K → ClosureStep K → ClosureStep K
  _∘Step_ {K = K} s₂ s₁ =
    let
      module Rel = RelCore.For K (FlowClosure K)

      toRel : ClosureStep K → Rel.ClosureStep
      toRel t = Rel.mkClosureStep (ClosureStep.endo t) (ClosureStep.infl t) (ClosureStep.leFlow t)

      fromRel : Rel.ClosureStep → ClosureStep K
      fromRel t = mkClosureStep (Rel.endo t) (Rel.infl t) (Rel.leJ t)
    in
    fromRel (Rel._∘Step_ (toRel s₂) (toRel s₁))

  _thenStep_ : ∀ {K : Obj} → ClosureStep K → ClosureStep K → ClosureStep K
  _thenStep_ s₁ s₂ = s₂ ∘Step s₁

  Th⋆K : (K : Obj) → ConPreorder.Con (BulkBoundary.bnd (BBOf K))
  Th⋆K = Th*Of

  FlowTh⋆K : (K : Obj) → ConPreorder.Con (BulkBoundary.bnd (BBOf K))
  FlowTh⋆K K = Endo.fn (Flow-Endo K) (Th⋆K K)

  Th⋆≤FlowTh⋆
    : (K : Obj)
    → ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K)) (Th⋆K K) (FlowTh⋆K K)
  Th⋆≤FlowTh⋆ = Th*fixed⇒

  FlowTh⋆≤Th⋆
    : (K : Obj)
    → ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K)) (FlowTh⋆K K) (Th⋆K K)
  FlowTh⋆≤Th⋆ = Th*fixed⇐

  FlowTh⋆≡Th⋆
    : (K : Obj)
      (po : BulkBoundaryPO (BBOf K))
    → FlowTh⋆K K ≡ Th⋆K K
  FlowTh⋆≡Th⋆ K po =
    let open BulkBoundaryPO po using (po-bnd)
        open PartialOrder po-bnd using (antisym)
    in antisym (FlowTh⋆≤Th⋆ K) (Th⋆≤FlowTh⋆ K)

  fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆

  Flow≤f→Th⋆≤fTh⋆
    : (K : Obj)
      (f : Endo K)
    → _≤₂_ K (Flow-Endo K) f
    → ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K))
        (Th⋆K K) (Endo.fn f (Th⋆K K))
  Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
    let
      CP = BulkBoundary.bnd (BBOf K)
    in ConPreorder.trans CP (Th⋆≤FlowTh⋆ K) (tf≤f (Th⋆K K))

  f≤Flow→fTh⋆≤Th⋆
    : (K : Obj)
      (f : Endo K)
    → _≤₂_ K f (Flow-Endo K)
    → ConPreorder._⊑_ (BulkBoundary.bnd (BBOf K))
        (Endo.fn f (Th⋆K K)) (Th⋆K K)
  f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
    let
      CP = BulkBoundary.bnd (BBOf K)
    in ConPreorder.trans CP (f≤tf (Th⋆K K)) (FlowTh⋆≤Th⋆ K)

  Flow≈₂f→fTh⋆≡Th⋆
    : (K : Obj)
      (po : BulkBoundaryPO (BBOf K))
      (f : Endo K)
    → _≈₂_ K (Flow-Endo K) f
    → Endo.fn f (Th⋆K K) ≡ Th⋆K K
  Flow≈₂f→fTh⋆≡Th⋆ K po f (tf≤f , f≤tf) =
    let
      open BulkBoundaryPO po using (po-bnd)
      open PartialOrder po-bnd using (antisym)
    in antisym (f≤Flow→fTh⋆≤Th⋆ K f f≤tf) (Flow≤f→Th⋆≤fTh⋆ K f tf≤f)
