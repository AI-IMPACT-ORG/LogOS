{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.Totalisation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Σ-totalisation (Grothendieck-style; refinement inherited from the base):
-- Σ-objects and Σ-morphisms, with 2-cells inherited from the base thin 2-category.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; ≈-refl)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Core using (DisplayedThin2Cat; Ob; HomD; idD; compD)

-- Record-canonical total objects. Conversion helpers remain for older call
-- sites, but the public totalisation surface is no longer Σ-first.
record TotalObjR
  {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (D : DisplayedThin2Cat C ℓDObj ℓDHom)
  : Set (ℓObj ⊔ ℓDObj) where
  constructor mkTotalObjR
  field
    baseObj : Thin2Cat.Obj C
    dispObj : Ob D baseObj

TotalObj
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → DisplayedThin2Cat C ℓDObj ℓDHom
  → Set (ℓObj ⊔ ℓDObj)
TotalObj D = TotalObjR D

toTotalObjR
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
  → TotalObj D → TotalObjR D
toTotalObjR X = X

fromTotalObjR
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
  → TotalObjR D → TotalObj D
fromTotalObjR X = X

base
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
  → TotalObj D → Thin2Cat.Obj C
base = TotalObjR.baseObj

disp
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
  → (X : TotalObj D) → Ob D (base {D = D} X)
disp = TotalObjR.dispObj

-- Record-canonical total morphisms. Refinement still only sees the base part.
record TotalHomR
  {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (D : DisplayedThin2Cat C ℓDObj ℓDHom)
  (X Y : TotalObj D)
  : Set (ℓHomCon ⊔ ℓDHom) where
  constructor mkTotalHomR
  field
    hom : Con (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
    compat : HomD D hom (disp {D = D} X) (disp {D = D} Y)

TotalHom
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
  → TotalObj D → TotalObj D → Set (ℓHomCon ⊔ ℓDHom)
TotalHom D X Y = TotalHomR D X Y

toTotalHomR
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
  → TotalHom D X Y → TotalHomR D X Y
toTotalHomR f = f

fromTotalHomR
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
  → TotalHomR D X Y → TotalHom D X Y
fromTotalHomR f = f

baseHom
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
  → TotalHom D X Y → Con (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
baseHom = TotalHomR.hom

dispHom
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
  → (f : TotalHom D X Y)
  → HomD D (baseHom {D = D} f) (disp {D = D} X) (disp {D = D} Y)
dispHom = TotalHomR.compat

TotalHomPreorder
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
  → TotalObj D → TotalObj D → ConPreorder (ℓHomCon ⊔ ℓDHom) ℓHomRel
TotalHomPreorder {C = C} D X Y =
  let module B = Thin2Cat C
      A = base {D = D} X
      B₀ = base {D = D} Y
  in
  record
    { Con   = TotalHom D X Y
    ; _⊑_   = λ f g → _⊑_ (B.Hom A B₀) (baseHom {D = D} f) (baseHom {D = D} g)
    ; refl  = λ {f} → ConPreorder.refl (B.Hom A B₀) {c = baseHom {D = D} f}
    ; trans = λ {f} {g} {h} fg gh →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning (B.Hom A B₀)
        in
        R._⊑⟨_⟩_ (baseHom {D = D} f) fg gh
    }

-- --------------------------------------------------------------------------
-- Refinement on total morphisms is inherited from the base only.
--
-- Engineering consequence:
-- displayed evidence (port obligations) does not participate in `_⊑_`/`≈`
-- between total morphisms; refinement is exactly refinement of `baseHom`.

total⊑→base⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
    {X Y : TotalObj D}
    {f g : TotalHom D X Y}
  → _⊑_ (TotalHomPreorder D X Y) f g
  → _⊑_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
      (baseHom {D = D} f)
      (baseHom {D = D} g)
total⊑→base⊑ _ le = le

base⊑→total⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
    {X Y : TotalObj D}
    {f g : TotalHom D X Y}
  → _⊑_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
      (baseHom {D = D} f)
      (baseHom {D = D} g)
  → _⊑_ (TotalHomPreorder D X Y) f g
base⊑→total⊑ _ le = le

total≈→base≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
    {X Y : TotalObj D}
    {f g : TotalHom D X Y}
  → _≈_ (TotalHomPreorder D X Y) f g
  → _≈_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
      (baseHom {D = D} f)
      (baseHom {D = D} g)
total≈→base≈ _ fg = fg

base≈→total≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
    {X Y : TotalObj D}
    {f g : TotalHom D X Y}
  → _≈_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
      (baseHom {D = D} f)
      (baseHom {D = D} g)
  → _≈_ (TotalHomPreorder D X Y) f g
base≈→total≈ _ fg = fg

-- If two total morphisms have definitionally the same base morphism, then
-- they are observationally equivalent at the total level.
--
-- This is the canonical “ignore displayed evidence” principle, used frequently
-- when proving functor laws out of Σ-totalisations.
baseHom≡→total≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
    {f g : TotalHom D X Y}
  → baseHom {D = D} f ≡ baseHom {D = D} g
  → _≈_ (TotalHomPreorder D X Y) f g
baseHom≡→total≈ {D = D} {X = X} {Y = Y} {f = f} {g = g} eq with eq
... | refl = ≈-refl (TotalHomPreorder D X Y) f

-- Convenience wrapper: provide the two total morphisms explicitly.
--
-- This is often better for inference than `baseHom≡→total≈` when the goal type
-- reduces to a statement about base morphisms only (so `f`/`g` do not appear).
byBaseHom≡
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {D : DisplayedThin2Cat C ℓDObj ℓDHom}
    {X Y : TotalObj D}
  → (f g : TotalHom D X Y)
  → baseHom {D = D} f ≡ baseHom {D = D} g
  → _≈_ (TotalHomPreorder D X Y) f g
byBaseHom≡ {D = D} {X = X} {Y = Y} f g eq =
  baseHom≡→total≈ {D = D} {X = X} {Y = Y} {f = f} {g = g} eq

TotalThin2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → DisplayedThin2Cat C ℓDObj ℓDHom
  → Thin2Cat (ℓObj ⊔ ℓDObj) (ℓHomCon ⊔ ℓDHom) ℓHomRel
TotalThin2Cat {C = C} D =
  let module B = Thin2Cat C in
  record
    { Obj = TotalObj D
    ; Hom = TotalHomPreorder D
    ; id  = λ {A} →
        mkTotalHomR
          (B.id {A = base {D = D} A})
          (idD D (disp {D = D} A))
    ; _∘_ = λ {A} {B₀} {C₀} g f →
        mkTotalHomR
          (baseHom {D = D} g B.∘ baseHom {D = D} f)
          (compD D (dispHom {D = D} f) (dispHom {D = D} g))
    ; comp-mono-l = λ {A} {B₀} {C₀} {f} {f'} {g} le →
        B.comp-mono-l {A = base {D = D} A} {B = base {D = D} B₀} {C = base {D = D} C₀}
          {f = baseHom {D = D} f} {f' = baseHom {D = D} f'} {g = baseHom {D = D} g}
          le
    ; comp-mono-r = λ {A} {B₀} {C₀} {f} {g} {g'} le →
        B.comp-mono-r {A = base {D = D} A} {B = base {D = D} B₀} {C = base {D = D} C₀}
          {f = baseHom {D = D} f} {g = baseHom {D = D} g} {g' = baseHom {D = D} g'}
          le
    }

-- Forgetful functor from the totalisation back to the base.
forgetTotal
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat C ℓDObj ℓDHom)
  → Thin2Functor (TotalThin2Cat D) C
forgetTotal {C = C} D =
  let module B = Thin2Cat C in
  record
    { mapObj = λ X → base {D = D} X
    ; mapHom = baseHom {D = D}
    ; mapHom-mono = λ le → le
    ; id-pres = λ {A} →
        ≈-refl (B.Hom (base {D = D} A) (base {D = D} A)) (B.id {A = base {D = D} A})
    ; comp-pres = λ {A} {B₀} {C₀} f g →
        ≈-refl (B.Hom (base {D = D} A) (base {D = D} C₀)) (baseHom {D = D} f B.∘ baseHom {D = D} g)
    }

-- --------------------------------------------------------------------------
-- Stable v1.1 aliases for the totalisation surface.
DecoratedObj = TotalObj
DecoratedHom = TotalHom
DecoratedHomPreorder = TotalHomPreorder
DecoratedThin2Cat = TotalThin2Cat
forgetDecorated = forgetTotal
