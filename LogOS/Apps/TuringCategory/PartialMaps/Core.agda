{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.PartialMaps.Core where

-- Canonical “classical” partial maps as a Kleisli-style thin 2-category.
--
-- Objects: `ConPreorder` (fixed universe parameters).
-- Morphisms X ⇀ Y: monotone maps `Con X → Lift (Con Y)`.
-- 2-cells: pointwise refinement.
--
-- This module is intended as the ZFC-friendly semantic target for
-- extensional/partial-map readings.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  ; refl⊑
  ; MonoMap
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Apps.TuringCategory.Lift using
  ( LiftCP
  ; returnᴸ
  ; bindᴸ
  ; bindᴸ-returnᴸ-left≈
  ; bindᴸ-returnᴸ-right≈
  ; bindᴸ-assoc≈
  ; transLiftCP
  ; bindᴸ-mono-l
  ; bindᴸ-mono-r
  )

-- Partial maps between preorders.
record PartialMap {ℓCon ℓRel : Level}
  (X Y : ConPreorder ℓCon ℓRel)
  : Set (ℓCon ⊔ ℓRel) where
  field
    map  : Con X → Con (LiftCP Y)
    mono : MonoMap X (LiftCP Y) map

open PartialMap public

infixr 40 _∘p_
_∘p_
  : ∀ {ℓCon ℓRel : Level}
    {X Y Z : ConPreorder ℓCon ℓRel}
  → PartialMap Y Z
  → PartialMap X Y
  → PartialMap X Z
_∘p_ {X = X} {Y = Y} {Z = Z} g f =
  record
    { map = λ x → bindᴸ {A = Y} {B = Z} (map f x) (map g)
    ; mono = λ {x} {y} xy →
        bindᴸ-mono-l
          {A = Y}
          {B = Z}
          {k = map g}
          (mono g)
          {x = map f x}
          {y = map f y}
          (mono f xy)
    }

idp
  : ∀ {ℓCon ℓRel : Level}
    {X : ConPreorder ℓCon ℓRel}
  → PartialMap X X
idp {X = X} =
  record
    { map = returnᴸ {CP = X}
    ; mono = λ {x} {y} xy → xy
    }

-- Pointwise refinement on partial maps.
PartialMapPreorder
  : ∀ {ℓCon ℓRel : Level}
  → ConPreorder ℓCon ℓRel
  → ConPreorder ℓCon ℓRel
  → ConPreorder (ℓCon ⊔ ℓRel) (ℓCon ⊔ ℓRel)
PartialMapPreorder {ℓCon} {ℓRel} X Y =
  record
    { Con   = PartialMap X Y
    ; _⊑_   = λ f g → ∀ x → _⊑_ (LiftCP Y) (map f x) (map g x)
    ; refl  = λ {f} x → refl⊑ (LiftCP Y) {c = map f x}
    ; trans =
        λ {f} {g} {h} fg gh x →
          transLiftCP
            {CP = Y}
            {a = map f x}
            {b = map g x}
            {c = map h x}
            (fg x)
            (gh x)
    }

-- The partial-map thin 2-category (for fixed universe parameters).
Par
  : ∀ {ℓCon ℓRel : Level}
  → Thin2Cat
      (lsuc (ℓCon ⊔ ℓRel))
      (ℓCon ⊔ ℓRel)
      (ℓCon ⊔ ℓRel)
Par {ℓCon} {ℓRel} =
  record
    { Obj = ConPreorder ℓCon ℓRel
    ; Hom = PartialMapPreorder
    ; id  = idp
    ; _∘_ = _∘p_
    ; comp-mono-l =
        λ {A} {B} {C} {f} {f'} {g} ff' a →
          -- bind is monotone in its continuation (pointwise)
          bindᴸ-mono-r
            {A = B}
            {B = C}
            {x = map g a}
            {k = map f}
            {k' = map f'}
            (λ b → ff' b)
    ; comp-mono-r =
        λ {A} {B} {C} {f} {g} {g'} gg' a →
          -- bind is monotone in its lifted argument (requires monotone continuation)
          bindᴸ-mono-l
            {A = B}
            {B = C}
            {k = map f}
            (PartialMap.mono f)
            {x = map g a}
            {y = map g' a}
            (gg' a)
    }

-- Laws for the partial-map thin 2-category.

Par-id-left≈
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
  → (f : PartialMap A B)
  → _≈_ (PartialMapPreorder A B) (idp ∘p f) f
Par-id-left≈ {B = B} f =
  ( forward , backward )
  where
    forward : ∀ x → _⊑_ (LiftCP B) (map (idp ∘p f) x) (map f x)
    forward x = fst (bindᴸ-returnᴸ-right≈ {A = B} (map f x))

    backward : ∀ x → _⊑_ (LiftCP B) (map f x) (map (idp ∘p f) x)
    backward x = snd (bindᴸ-returnᴸ-right≈ {A = B} (map f x))

Par-id-left
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
  → (f : PartialMap A B)
  → _≈_ (PartialMapPreorder A B) (idp ∘p f) f
Par-id-left = Par-id-left≈

Par-id-right≈
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
  → (f : PartialMap A B)
  → _≈_ (PartialMapPreorder A B) (f ∘p idp) f
Par-id-right≈ {A = A} {B = B} f =
  ( forward , backward )
  where
    forward : ∀ x → _⊑_ (LiftCP B) (map (f ∘p idp) x) (map f x)
    forward x = fst (bindᴸ-returnᴸ-left≈ {A = A} {B = B} x (map f))

    backward : ∀ x → _⊑_ (LiftCP B) (map f x) (map (f ∘p idp) x)
    backward x = snd (bindᴸ-returnᴸ-left≈ {A = A} {B = B} x (map f))

Par-id-right
  : ∀ {ℓCon ℓRel : Level}
    {A B : ConPreorder ℓCon ℓRel}
  → (f : PartialMap A B)
  → _≈_ (PartialMapPreorder A B) (f ∘p idp) f
Par-id-right = Par-id-right≈

Par-assoc
  : ∀ {ℓCon ℓRel : Level}
    {A B C D : ConPreorder ℓCon ℓRel}
  → (f : PartialMap C D)
  → (g : PartialMap B C)
  → (h : PartialMap A B)
  → _≈_ (PartialMapPreorder A D) ((f ∘p g) ∘p h) (f ∘p (g ∘p h))
Par-assoc {B = B} {C = C} {D = D} f g h =
  ( forward , backward )
  where
    forward : ∀ x → _⊑_ (LiftCP D) (map ((f ∘p g) ∘p h) x) (map (f ∘p (g ∘p h)) x)
    forward x = snd (bindᴸ-assoc≈ (map h x) (map g) (map f))

    backward : ∀ x → _⊑_ (LiftCP D) (map (f ∘p (g ∘p h)) x) (map ((f ∘p g) ∘p h) x)
    backward x = fst (bindᴸ-assoc≈ (map h x) (map g) (map f))

ParLaws : ∀ {ℓCon ℓRel : Level} → Thin2CatLaws (Par {ℓCon} {ℓRel})
ParLaws =
  record
    { id-left = Par-id-left≈
    ; id-right = Par-id-right≈
    ; assoc = Par-assoc
    }
