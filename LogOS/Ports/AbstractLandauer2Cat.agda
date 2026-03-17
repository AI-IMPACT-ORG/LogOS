{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauer2Cat where

-- Landauer-style cost bounds as a displayed law port over a thin 2-category.
--
-- This is a refinement-first “localisation” of `LandauerAssumptions`:
-- each morphism is decorated with an *explicit* scale element that upper-bounds
-- its Landauer cost, and composition combines bounds multiplicatively.
--
-- Note: the observable refinement on decorated morphisms is inherited from the
-- base thin 2-category only (as in all `DisplayedThin2Cat` decorations).
-- Quantitative comparison between chosen bounds themselves is available below
-- as an explicit fibre preorder (`CostBoundPreorder`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (base; baseHom; dispHom)

open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)

import LogOS.Ports.LawSlice2Cat as LawSlice

-- η-unit payload for the Landauer law-port (avoids Topℓ/⊤ footguns).
record LandauerOb : Set where
  constructor ttLandauer

-- A morphism-local cost bound: a chosen scale element `c` together with a proof
-- that `cost f ⊑ c`.
record CostBound
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (L : LandauerAssumptions C Scale JP)
  {A B : Thin2Cat.Obj C}
  (f : Con (Thin2Cat.Hom C A B))
  : Set (ℓScaleCon ⊔ ℓScaleRel) where
  constructor mkCostBound
  field
    bound : Con Scale
    boundProof : _⊑_ Scale (LandauerAssumptions.cost L f) bound

boundOf
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {L : LandauerAssumptions C Scale JP}
    {A B}
    {f : Con (Thin2Cat.Hom C A B)}
  → CostBound L f
  → Con Scale
boundOf = CostBound.bound

boundProof
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {L : LandauerAssumptions C Scale JP}
    {A B}
    {f : Con (Thin2Cat.Hom C A B)}
  → (cb : CostBound L f)
  → _⊑_ Scale (LandauerAssumptions.cost L f) (boundOf cb)
boundProof = CostBound.boundProof

CostBoundRefines
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {L : LandauerAssumptions C Scale JP}
    {A B}
    {f : Con (Thin2Cat.Hom C A B)}
  → CostBound L f → CostBound L f → Set ℓScaleRel
CostBoundRefines {Scale = Scale} c d =
  ConPreorder._⊑_ Scale (boundOf c) (boundOf d)

CostBoundRefines-trans
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {L : LandauerAssumptions C Scale JP}
    {A B}
    {f : Con (Thin2Cat.Hom C A B)}
  → (c d e : CostBound L f)
  → CostBoundRefines c d
  → CostBoundRefines d e
  → CostBoundRefines c e
CostBoundRefines-trans {Scale = Scale} c d e c≤d d≤e =
  let
    module R = ≤-Reasoning Scale
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    boundOf c
      ⊑⟨ c≤d ⟩
    boundOf d
      ⊑⟨ d≤e ⟩
    boundOf e ∎⊑

CostBoundPreorder
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {L : LandauerAssumptions C Scale JP}
    {A B}
    (f : Con (Thin2Cat.Hom C A B))
  → ConPreorder (ℓScaleCon ⊔ ℓScaleRel) ℓScaleRel
CostBoundPreorder {Scale = Scale} {L = L} f =
  record
    { Con = CostBound L f
    ; _⊑_ = λ c d → CostBoundRefines {Scale = Scale} {L = L} {f = f} c d
    ; refl = ConPreorder.refl Scale
    ; trans = λ {a} {b} {c} a≤b b≤c →
        CostBoundRefines-trans {Scale = Scale} {L = L} {f = f} a b c a≤b b≤c
    }

idCostBound
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  → (L : LandauerAssumptions C Scale JP)
  → ∀ {A}
  → CostBound L (Thin2Cat.id C {A})
idCostBound {Scale = Scale} {JP = JP} L {A} =
  let open JoinPrequantale JP in
  mkCostBound
    e
    (fst (LandauerAssumptions.cost-id≈ L {A = A}))

composeCostBound
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  → (L : LandauerAssumptions C Scale JP)
  → ∀ {A B D}
    {f : Con (Thin2Cat.Hom C A B)}
    {g : Con (Thin2Cat.Hom C B D)}
  → CostBound L f
  → CostBound L g
  → CostBound L (Thin2Cat._∘_ C g f)
composeCostBound {C = C} {Scale = Scale} {JP = JP} L {f = f} {g = g} cf cg =
  let
    open JoinPrequantale JP
    module R = ≤-Reasoning Scale
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  mkCostBound
    (boundOf cf · boundOf cg)
    ( begin⊑
        LandauerAssumptions.cost L (Thin2Cat._∘_ C g f)
          ⊑⟨ LandauerAssumptions.cost-comp⊑ L f g ⟩
        (LandauerAssumptions.cost L f · LandauerAssumptions.cost L g)
          ⊑⟨ ·-mono (boundProof cf) (boundProof cg) ⟩
        (boundOf cf · boundOf cg) ∎⊑
    )
 

-- --------------------------------------------------------------------------
-- PortStack packaging: tag + signature + singleton stack.

data LandauerTag : Set where
  landauerTag : LandauerTag

landauerTagId : ℕ
landauerTagId = 14

module Port
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (L : LandauerAssumptions C Scale JP)
  = LawSlice.Exports
      {C = C}
      {Tag = LandauerTag}
      landauerTagId
      LandauerOb
      (CostBound L)
      (idCostBound L)
      (composeCostBound L)

port2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  → (L : LandauerAssumptions C Scale JP)
  → LawSlice.Singleton2Cat C landauerTagId LandauerTag
port2Cat {C = C} L =
  Port.port2Cat {C = C} L

open Port public using
  ( singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  )

totalCostBound
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
    {A B : Thin2Cat.Obj (WithPort {C = C} L)}
  → (h : Con (Thin2Cat.Hom (WithPort {C = C} L) A B))
  → CostBound L (baseHom {D = Displayed {C = C} L} {X = A} {Y = B} h)
totalCostBound {C = C} {Scale = Scale} {JP = JP} L {A} {B} h =
  dispHom {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} {X = A} {Y = B} h

TotalCostBoundRefines
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
    {A B : Thin2Cat.Obj (WithPort {C = C} L)}
  → Con (Thin2Cat.Hom (WithPort {C = C} L) A B)
  → Con (Thin2Cat.Hom (WithPort {C = C} L) A B)
  → Set (ℓHomRel ⊔ ℓScaleRel)
TotalCostBoundRefines {C = C} {Scale = Scale} {JP = JP} L {A} {B} h k =
  ConPreorder._⊑_
    (Thin2Cat.Hom C
      (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} A)
      (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} B))
    (baseHom {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} {X = A} {Y = B} h)
    (baseHom {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} {X = A} {Y = B} k)
  ×
  ConPreorder._⊑_ Scale
    (CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L h))
    (CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L k))

TotalCostBoundRefines-trans
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
    {A B : Thin2Cat.Obj (WithPort {C = C} L)}
    (h k m : Con (Thin2Cat.Hom (WithPort {C = C} L) A B))
  → TotalCostBoundRefines L h k
  → TotalCostBoundRefines L k m
  → TotalCostBoundRefines L h m
TotalCostBoundRefines-trans {C = C} {Scale = Scale} {JP = JP} L {A} {B} h k m (h≤k , ch≤ck) (k≤m , ck≤cm) =
  ( baseTrans
  , costTrans
  )
  where
    BaseHom =
      Thin2Cat.Hom C
        (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} A)
        (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} B)

    module RBase = ≤-Reasoning BaseHom
    module RScale = ≤-Reasoning Scale

    baseTrans : _⊑_ BaseHom (baseHom h) (baseHom m)
    baseTrans =
      let open RBase using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        baseHom h
          ⊑⟨ h≤k ⟩
        baseHom k
          ⊑⟨ k≤m ⟩
        baseHom m ∎⊑

    costTrans
      : _⊑_ Scale
          (CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L h))
          (CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L m))
    costTrans =
      let open RScale using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L h)
          ⊑⟨ ch≤ck ⟩
        CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L k)
          ⊑⟨ ck≤cm ⟩
        CostBound.bound (totalCostBound {C = C} {Scale = Scale} {JP = JP} L m) ∎⊑

TotalCostBoundPreorder
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
    {A B : Thin2Cat.Obj (WithPort {C = C} L)}
  → ConPreorder
      (ℓHomCon ⊔ ℓScaleCon ⊔ ℓScaleRel)
      (ℓHomRel ⊔ ℓScaleRel)
TotalCostBoundPreorder {C = C} {Scale = Scale} {JP = JP} L {A} {B} =
  record
    { Con = Con (Thin2Cat.Hom (WithPort {C = C} {Scale = Scale} {JP = JP} L) A B)
    ; _⊑_ = TotalCostBoundRefines {C = C} {Scale = Scale} {JP = JP} L
    ; refl =
        ( ConPreorder.refl
            (Thin2Cat.Hom C
              (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} A)
              (base {D = Displayed {C = C} {Scale = Scale} {JP = JP} L} B))
        , ConPreorder.refl Scale
        )
    ; trans = λ {h} {k} {m} h≤k k≤m →
        TotalCostBoundRefines-trans {C = C} {Scale = Scale} {JP = JP} L h k m h≤k k≤m
    }
