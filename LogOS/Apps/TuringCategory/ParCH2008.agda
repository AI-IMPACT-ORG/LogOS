{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.ParCH2008 where

-- Concrete CH2008-style structure on the canonical partial-map model `Par`:
-- - restriction structure (`bar`) = “definedness filter”,
-- - cartesian structure = terminal + product on `ConPreorder`.
--
-- This module is the ZFC-friendly semantic anchor: it provides the classical
-- partial-map category together with the restriction discipline CH uses.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap; _×CP_; refl⊑)

import LogOS.Apps.TuringCategory.CH2008 as CH
import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using
  ( LiftCP
  ; bindᴸ
  ; some
  ; transLiftCP
  ; bindᴸ-mono-l
  ; bindᴸ-mono-r
  )

-- --------------------------------------------------------------------------
-- Cartesian structure on `Par` (objects = preorders, products = `_×CP_`).

parCartesian
  : ∀ {ℓCon ℓRel : Level}
  → CH.CartesianStructure (PM.Par {ℓCon} {ℓRel})
parCartesian {ℓCon} {ℓRel} =
  record
    { 𝟙 = PM.UnitCP {ℓCon} {ℓRel}
    ; !_ = PM.! {ℓCon = ℓCon} {ℓRel = ℓRel}
    ; prod = _×CP_
    ; π₁ = PM.π₁
    ; π₂ = PM.π₂
    ; ⟨_,_⟩ = PM.⟨_,_⟩
    }

-- --------------------------------------------------------------------------
-- Restriction structure on `Par`.

-- Restriction idempotent for a partial map: keep the input iff the map is defined.
parBar
  : ∀ {ℓCon ℓRel : Level}
    {X Y : ConPreorder ℓCon ℓRel}
  → PM.PartialMap X Y
  → PM.PartialMap X X
parBar {X = X} {Y = Y} f =
  record
    { map = λ x →
        bindᴸ {A = Y} {B = X} (PM.map f x) (λ _ → some {CP = X} x)
    ; mono = monoBar
    }
  where
    monoBar : MonoMap X (LiftCP X) (λ x → bindᴸ {A = Y} {B = X} (PM.map f x) (λ _ → some {CP = X} x))
    monoBar {x} {x'} xx' =
      let
        m≤ : _⊑_ (LiftCP Y) (PM.map f x) (PM.map f x')
        m≤ = PM.mono f xx'

        k  : Con Y → Con (LiftCP X)
        k _ = some {CP = X} x

        k' : Con Y → Con (LiftCP X)
        k' _ = some {CP = X} x'

        k≤k' : ∀ y → _⊑_ (LiftCP X) (k y) (k' y)
        k≤k' _ = xx'

        monoK' : MonoMap Y (LiftCP X) k'
        monoK' _ = ConPreorder.refl X {c = x'}

        step₁
          : _⊑_ (LiftCP X)
              (bindᴸ {A = Y} {B = X} (PM.map f x) k)
              (bindᴸ {A = Y} {B = X} (PM.map f x) k')
        step₁ =
          bindᴸ-mono-r
            {A = Y}
            {B = X}
            {x = PM.map f x}
            {k = k}
            {k' = k'}
            k≤k'

        step₂
          : _⊑_ (LiftCP X)
              (bindᴸ {A = Y} {B = X} (PM.map f x) k')
              (bindᴸ {A = Y} {B = X} (PM.map f x') k')
        step₂ =
          bindᴸ-mono-l
            {A = Y}
            {B = X}
            {k = k'}
            monoK'
            {x = PM.map f x}
            {y = PM.map f x'}
            m≤
      in
      transLiftCP
        {CP = X}
        {a = bindᴸ {A = Y} {B = X} (PM.map f x) k}
        {b = bindᴸ {A = Y} {B = X} (PM.map f x) k'}
        {c = bindᴸ {A = Y} {B = X} (PM.map f x') k'}
        step₁
        step₂

parRestriction
  : ∀ {ℓCon ℓRel : Level}
  → CH.RestrictionStructure (PM.Par {ℓCon} {ℓRel})
parRestriction {ℓCon} {ℓRel} =
  record
    { bar = parBar
    ; R1 = R1
    ; R2 = R2
    ; R3 = R3
    ; R4 = R4
    }
  where
    -- Helper: the refinement relation on partial maps is pointwise refinement on lifted outputs.
    --
    -- We prove restriction axioms by case-splitting on the observable `none/some` boundary.

    R1
      : ∀ {A B : ConPreorder ℓCon ℓRel} (f : PM.PartialMap A B)
      → _≈_ (PM.PartialMapPreorder A B) (f PM.∘p parBar f) f
    R1 {A = A} {B = B} f =
      ( forward , backward )
      where
        forward : ∀ x → _⊑_ (LiftCP B) (PM.map (f PM.∘p parBar f) x) (PM.map f x)
        forward x with PM.map f x in eq
        ... | inj₁ ttℓ = tt
        ... | inj₂ _ rewrite eq = refl⊑ (LiftCP B)

        backward : ∀ x → _⊑_ (LiftCP B) (PM.map f x) (PM.map (f PM.∘p parBar f) x)
        backward x with PM.map f x in eq
        ... | inj₁ ttℓ = tt
        ... | inj₂ _ rewrite eq = refl⊑ (LiftCP B)

    R2
      : ∀ {A B C₀ : ConPreorder ℓCon ℓRel}
        (f : PM.PartialMap A B) (g : PM.PartialMap A C₀)
      → _≈_ (PM.PartialMapPreorder A A) (parBar f PM.∘p parBar g) (parBar g PM.∘p parBar f)
    R2 {A = A} f g =
      ( forward , backward )
      where
        forward : ∀ x → _⊑_ (LiftCP A) (PM.map (parBar f PM.∘p parBar g) x) (PM.map (parBar g PM.∘p parBar f) x)
        forward x with PM.map f x in eqf | PM.map g x in eqg
        ... | inj₁ ttℓ | inj₁ ttℓ = tt
        ... | inj₁ ttℓ | inj₂ _ rewrite eqf = tt
        ... | inj₂ _ | inj₁ ttℓ = tt
        ... | inj₂ _ | inj₂ _ rewrite eqf | eqg = ConPreorder.refl A {c = x}

        backward : ∀ x → _⊑_ (LiftCP A) (PM.map (parBar g PM.∘p parBar f) x) (PM.map (parBar f PM.∘p parBar g) x)
        backward x with PM.map f x in eqf | PM.map g x in eqg
        ... | inj₁ ttℓ | inj₁ ttℓ = tt
        ... | inj₁ ttℓ | inj₂ _ = tt
        ... | inj₂ _ | inj₁ ttℓ rewrite eqg = tt
        ... | inj₂ _ | inj₂ _ rewrite eqf | eqg = ConPreorder.refl A {c = x}

    R3
      : ∀ {A B C₀ : ConPreorder ℓCon ℓRel}
        (f : PM.PartialMap A B) (g : PM.PartialMap A C₀)
      → _≈_ (PM.PartialMapPreorder A A) (parBar (g PM.∘p parBar f)) (parBar g PM.∘p parBar f)
    R3 {A = A} f g =
      ( forward , backward )
      where
        forward : ∀ x → _⊑_ (LiftCP A) (PM.map (parBar (g PM.∘p parBar f)) x) (PM.map (parBar g PM.∘p parBar f) x)
        forward x with PM.map f x in eqf | PM.map g x in eqg
        ... | inj₁ ttℓ | _ = tt
        ... | inj₂ _ | inj₁ ttℓ rewrite eqg = tt
        ... | inj₂ _ | inj₂ _ rewrite eqg = ConPreorder.refl A {c = x}

        backward : ∀ x → _⊑_ (LiftCP A) (PM.map (parBar g PM.∘p parBar f) x) (PM.map (parBar (g PM.∘p parBar f)) x)
        backward x with PM.map f x in eqf | PM.map g x in eqg
        ... | inj₁ ttℓ | _ = tt
        ... | inj₂ _ | inj₁ ttℓ rewrite eqg = tt
        ... | inj₂ _ | inj₂ _ rewrite eqg = ConPreorder.refl A {c = x}

    R4
      : ∀ {A B C₀ : ConPreorder ℓCon ℓRel}
        (f : PM.PartialMap A B) (g : PM.PartialMap B C₀)
      → _≈_ (PM.PartialMapPreorder A B) (parBar g PM.∘p f) (f PM.∘p parBar (g PM.∘p f))
    R4 {A = A} {B = B} f g =
      ( forward , backward )
      where
        forward : ∀ x → _⊑_ (LiftCP B) (PM.map (parBar g PM.∘p f) x) (PM.map (f PM.∘p parBar (g PM.∘p f)) x)
        forward x with PM.map f x in eqf
        ... | inj₁ ttℓ = tt
        ... | inj₂ b with PM.map g b in eqg
        ...   | inj₁ ttℓ = tt
        ...   | inj₂ c rewrite eqf = ConPreorder.refl B {c = b}

        backward : ∀ x → _⊑_ (LiftCP B) (PM.map (f PM.∘p parBar (g PM.∘p f)) x) (PM.map (parBar g PM.∘p f) x)
        backward x with PM.map f x in eqf
        ... | inj₁ ttℓ = tt
        ... | inj₂ b with PM.map g b in eqg
        ...   | inj₁ ttℓ = tt
        ...   | inj₂ c rewrite eqf = ConPreorder.refl B {c = b}

parRC
  : ∀ {ℓCon ℓRel : Level}
  → CH.RestrictionCategory
      {ℓObj = lsuc (ℓCon ⊔ ℓRel)}
      {ℓHomCon = ℓCon ⊔ ℓRel}
      {ℓHomRel = ℓCon ⊔ ℓRel}
parRC {ℓCon} {ℓRel} =
  record
    { C = PM.Par {ℓCon} {ℓRel}
    ; laws = PM.ParLaws
    ; R = parRestriction {ℓCon} {ℓRel}
    }
