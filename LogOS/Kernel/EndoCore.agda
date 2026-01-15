{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoCore where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Thin2Cat as Thin2Cat
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.EndoStepBridge as StepBridge
import LogOS.Kernel.LogicKernel.Endo as LKEndo

-- Shared saturation-level endomap DSL core (delegating to `LogicKernel.Endo`).
--
-- This factors out the common part of:
-- - `LogOS.Kernel.Endo` (unguarded kernel)
-- - `LogOS.Kernel.Graded.Endo` (graded kernel, at saturation grade)
--
-- without committing to a specific kernel-like record.

record Ops {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    Obj : Set (lsuc (lsuc ℓ))
    asLogicKernel : Obj → LogicKernel Sig Q

module WithOps {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (ops : Ops Sig Q) where
  open Ops ops

  infix 4 _≤₂_
  infixr 9 _∘E_

  record Endo (K : Obj) : Set (lsuc ℓ) where
    open LogicKernel (asLogicKernel K)
    private
      Con∂ = ConPoset.Con (BulkBoundary.bnd BB)
      _≤_  = ConPoset._⊑_ (BulkBoundary.bnd BB)
    field
      fn   : Con∂ → Con∂
      mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

  open Endo public

  toLKEndo : ∀ {K : Obj} → Endo K → LKEndo.Endo (asLogicKernel K)
  toLKEndo f = record { fn = Endo.fn f ; mono = Endo.mono f }

  fromLKEndo : ∀ {K : Obj} → LKEndo.Endo (asLogicKernel K) → Endo K
  fromLKEndo f = record { fn = LKEndo.Endo.fn f ; mono = LKEndo.Endo.mono f }

  toLK∘fromLK-fn
    : ∀ {K : Obj}
      (e : LKEndo.Endo (asLogicKernel K))
      (c : ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))))
    → LKEndo.Endo.fn (toLKEndo (fromLKEndo e)) c ≡ LKEndo.Endo.fn e c
  toLK∘fromLK-fn _ _ = refl

  _≤₂_ : (K : Obj) → Endo K → Endo K → Set ℓ
  _≤₂_ K f g = LKEndo._≤₂_ (asLogicKernel K) (toLKEndo f) (toLKEndo g)

  idEndo : (K : Obj) → Endo K
  idEndo K = fromLKEndo (LKEndo.idEndo (asLogicKernel K))

  _∘E_ : ∀ {K : Obj} → Endo K → Endo K → Endo K
  _∘E_ {K = K} f g =
    fromLKEndo (LKEndo._∘E_ {K = asLogicKernel K} (toLKEndo f) (toLKEndo g))

  refl₂ : ∀ (K : Obj) (f : Endo K) → _≤₂_ K f f
  refl₂ K f = LKEndo.refl₂ (asLogicKernel K) (toLKEndo f)

  trans₂
    : ∀ (K : Obj) {f g h : Endo K}
    → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
  trans₂ K fg gh = λ c →
    let open LogicKernel (asLogicKernel K) in
    ConPoset.trans (BulkBoundary.bnd BB) (fg c) (gh c)

  -- Endomaps form a one-object thin 2-category; whiskering is inherited.

  EndoPoset : (K : Obj) → ConPoset (lsuc ℓ)
  EndoPoset K =
    record
      { Con = Endo K
      ; _⊑_ = λ f g → Lift (lsuc ℓ) (_≤₂_ K f g)
      ; refl = λ {f} → lift (refl₂ K f)
      ; trans = λ {f} {g} {h} fg gh →
          lift (trans₂ K {f = f} {g = g} {h = h} (Lift.lower fg) (Lift.lower gh))
      }

  EndoThin2Cat : (K : Obj) → Thin2Cat.Thin2Cat ℓ (lsuc ℓ)
  EndoThin2Cat K =
    record
      { Obj = ⊤
      ; Hom = λ _ _ → EndoPoset K
      ; id  = λ {A} → idEndo K
      ; _∘_ = _∘E_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} fg →
          lift (λ c → Lift.lower fg (Endo.fn g c))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} gg' →
          lift (λ c → Endo.mono f (Lift.lower gg' c))
      }

  module Endo2Cat (K : Obj) where
    private
      C = EndoThin2Cat K

    whisker-left
      : {f g h : Endo K}
      → _≤₂_ K f g → _≤₂_ K (h ∘E f) (h ∘E g)
    whisker-left {f} {g} {h} fg =
      Lift.lower
        (Thin2Cat.whisker-right
          {C = C} {A = tt} {B = tt} {C' = tt}
          {f = h} {g = f} {g' = g}
          (lift fg))

    whisker-right
      : {f g h : Endo K}
      → _≤₂_ K f g → _≤₂_ K (f ∘E h) (g ∘E h)
    whisker-right {f} {g} {h} fg =
      Lift.lower
        (Thin2Cat.whisker-left
          {C = C} {A = tt} {B = tt} {C' = tt}
          {f = f} {f' = g} {g = h}
          (lift fg))

  -- Fixedness at a point in the boundary preorder, expressed in the LogOS style
  -- as mutual refinement (not definitional equality).

  FixedAt
    : ∀ {K : Obj}
      (f : Endo K)
      (c : ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))))
    → Set ℓ
  FixedAt {K = K} f c =
    let open LogicKernel (asLogicKernel K) in
    ConPoset._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) c
      × ConPoset._⊑_ (BulkBoundary.bnd BB) c (Endo.fn f c)

  fixedAt-transport
    : ∀ (K : Obj) {f g : Endo K}
    → _≤₂_ K f g
    → _≤₂_ K g f
    → ∀ c → FixedAt {K = K} f c → FixedAt {K = K} g c
  fixedAt-transport K fg gf c (fc≤c , c≤fc) =
    let open LogicKernel (asLogicKernel K)
        CP = BulkBoundary.bnd BB
        gc≤fc = gf c
        fc≤gc = fg c
    in
    ( ConPoset.trans CP gc≤fc fc≤c
    , ConPoset.trans CP c≤fc fc≤gc
    )

  Flow-Endo : (K : Obj) → Endo K
  Flow-Endo K = fromLKEndo (LKEndo.Flow-Endo (asLogicKernel K))

  Flow-closeEndo : (K : Obj) → Endo K → Endo K
  Flow-closeEndo K f = fromLKEndo (LKEndo.Flow-closeEndo (asLogicKernel K) (toLKEndo f))

  id≤Flow-close
    : (K : Obj) (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K (idEndo K) (Flow-closeEndo K f)
  id≤Flow-close K f = LKEndo.id≤Flow-close (asLogicKernel K) (toLKEndo f)

  Flow-close≤Flow
    : (K : Obj) (f : Endo K)
    → _≤₂_ K f (Flow-Endo K)
    → _≤₂_ K (Flow-closeEndo K f) (Flow-Endo K)
  Flow-close≤Flow K f = LKEndo.Flow-close≤Flow (asLogicKernel K) (toLKEndo f)

  Flow≤Flow-close
    : (K : Obj) (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K (Flow-Endo K) (Flow-closeEndo K f)
  Flow≤Flow-close K f = LKEndo.Flow≤Flow-close (asLogicKernel K) (toLKEndo f)

  -- Closure steps (id ≤ f ≤ Flow) via the shared bridge.

  module Steps =
    StepBridge.With
      {ℓ = ℓ} {Sig = Sig} {Q = Q}
      Obj
      asLogicKernel
      Endo
      _≤₂_
      idEndo
      Flow-Endo
      toLKEndo
      fromLKEndo
      (λ p → p)
      (λ p → p)
      (λ {K} c → toLK∘fromLK-fn (LKEndo.idEndo (asLogicKernel K)) c)
      (λ {K} c → toLK∘fromLK-fn (LKEndo.Flow-Endo (asLogicKernel K)) c)
      toLK∘fromLK-fn

  open Steps public

  -- A few commonly used fixed-point helpers re-exported at the kernel-like level.

  id≤Flow : (K : Obj) → _≤₂_ K (idEndo K) (Flow-Endo K)
  id≤Flow K = LKEndo.id≤Flow (asLogicKernel K)

  Flow∘Flow≤Flow : (K : Obj) → _≤₂_ K ((Flow-Endo K) ∘E (Flow-Endo K)) (Flow-Endo K)
  Flow∘Flow≤Flow K = LKEndo.Flow∘Flow≤Flow (asLogicKernel K)

  Th⋆K : (K : Obj) → ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K)))
  Th⋆K K = LKEndo.Th⋆K (asLogicKernel K)

  FlowTh⋆K : (K : Obj) → ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K)))
  FlowTh⋆K K = LKEndo.FlowTh⋆K (asLogicKernel K)

  Th⋆≤FlowTh⋆
    : (K : Obj)
    → ConPoset._⊑_ (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))) (Th⋆K K) (FlowTh⋆K K)
  Th⋆≤FlowTh⋆ K = LKEndo.Th⋆≤FlowTh⋆ (asLogicKernel K)

  FlowTh⋆≤Th⋆
    : (K : Obj)
    → ConPoset._⊑_ (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))) (FlowTh⋆K K) (Th⋆K K)
  FlowTh⋆≤Th⋆ K = LKEndo.FlowTh⋆≤Th⋆ (asLogicKernel K)

  FlowTh⋆≡Th⋆
    : (K : Obj)
      (po : BulkBoundaryPO (LogicKernel.BB (asLogicKernel K))) -- ANTISYM-OK
    → FlowTh⋆K K ≡ Th⋆K K
  FlowTh⋆≡Th⋆ K po = LKEndo.FlowTh⋆≡Th⋆ (asLogicKernel K) po

  fixedpoint-eq-under-antisym = FlowTh⋆≡Th⋆ -- ANTISYM-OK

  Flow≤f→Th⋆≤fTh⋆
    : (K : Obj)
      (f : Endo K)
    → _≤₂_ K (Flow-Endo K) f
    → ConPoset._⊑_ (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K)))
        (Th⋆K K) (Endo.fn f (Th⋆K K))
  Flow≤f→Th⋆≤fTh⋆ K f tf≤f =
    LKEndo.Flow≤f→Th⋆≤fTh⋆ (asLogicKernel K) (toLKEndo f) tf≤f

  f≤Flow→fTh⋆≤Th⋆
    : (K : Obj)
      (f : Endo K)
    → _≤₂_ K f (Flow-Endo K)
    → ConPoset._⊑_ (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K)))
        (Endo.fn f (Th⋆K K)) (Th⋆K K)
  f≤Flow→fTh⋆≤Th⋆ K f f≤tf =
    LKEndo.f≤Flow→fTh⋆≤Th⋆ (asLogicKernel K) (toLKEndo f) f≤tf

  Flow≃f→fTh⋆≡Th⋆
    : (K : Obj)
      (po : BulkBoundaryPO (LogicKernel.BB (asLogicKernel K))) -- ANTISYM-OK
      (f : Endo K)
    → _≤₂_ K (Flow-Endo K) f
    → _≤₂_ K f (Flow-Endo K)
    → Endo.fn f (Th⋆K K) ≡ Th⋆K K
  Flow≃f→fTh⋆≡Th⋆ K po f tf≤f f≤tf =
    LKEndo.Flow≃f→fTh⋆≡Th⋆ (asLogicKernel K) po (toLKEndo f) tf≤f f≤tf

  -- ASCII aliases for the Th⋆ helpers (to avoid mixed star symbols).

  ThStarK = Th⋆K
  FlowThStarK = FlowTh⋆K
  ThStar≤FlowThStar = Th⋆≤FlowTh⋆
  FlowThStar≤ThStar = FlowTh⋆≤Th⋆
  FlowThStar≡ThStar = FlowTh⋆≡Th⋆
  Flow≤f→ThStar≤fThStar = Flow≤f→Th⋆≤fTh⋆
  f≤Flow→fThStar≤ThStar = f≤Flow→fTh⋆≤Th⋆
  Flow≃f→fThStar≡ThStar = Flow≃f→fTh⋆≡Th⋆
