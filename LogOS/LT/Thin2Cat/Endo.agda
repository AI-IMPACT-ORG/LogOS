{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Cat.Endo where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

-- --------------------------------------------------------------------------
-- Endomorphisms (dynamical systems) as a thin 2-category.
--
-- Reading:
-- - an object is a “state space” `A` together with a designated step `A → A`;
-- - a morphism is a “simulation/observation” map `h : A → B` equipped with a
--   commuting 2-cell `h ∘ stepA ⇒ stepB ∘ h` (semiconjugacy, lax in general).
--
-- This construction needs associativity/unit laws (up to `≈`) from the base
-- thin 2-category to build the commuting proof for composed morphisms.

record EndoObj
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (ℓObj ⊔ ℓHomCon) where
  constructor mkEndoObj
  field
    carrier : Thin2Cat.Obj C
    step    : Con (Thin2Cat.Hom C carrier carrier)

open EndoObj public
record EndoHom
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (L : Thin2CatLaws C)
  (A B : EndoObj C)
  : Set (ℓHomCon ⊔ ℓHomRel) where
  field
    map     : Con (Thin2Cat.Hom C (carrier A) (carrier B))
    commute
      : _⊑_
          (Thin2Cat.Hom C (carrier A) (carrier B))
          (Thin2Cat._∘_ C map (step A))
          (Thin2Cat._∘_ C (step B) map)

open EndoHom public
EndoHomPreorder
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (L : Thin2CatLaws C)
  → EndoObj C → EndoObj C
  → ConPreorder (ℓHomCon ⊔ ℓHomRel) ℓHomRel
EndoHomPreorder {C = C} L A B =
  let module C = Thin2Cat C in
  record
    { Con   = EndoHom L A B
    ; _⊑_   = λ f g → _⊑_ (C.Hom (carrier A) (carrier B)) (map f) (map g)
    ; refl  = λ {f} → ConPreorder.refl (C.Hom (carrier A) (carrier B))
    ; trans = λ {f} {g} {h} fg gh →
        let
          module R = ≤-Reasoning (C.Hom (carrier A) (carrier B))
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
        in
        begin⊑
          map f ⊑⟨ fg ⟩
          map g ⊑⟨ gh ⟩
          map h ∎⊑
    }

Endo2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  → Thin2CatLaws C
  → Thin2Cat
      (ℓObj ⊔ ℓHomCon)
      (ℓHomCon ⊔ ℓHomRel)
      ℓHomRel
Endo2Cat C L =
  let
    module Base = Thin2Cat C
    module Laws = Thin2CatLaws L
    open Base
    -- Identity commutes (up to refinement) by the unit laws.
    id-commute
      : ∀ (A : EndoObj C)
      → _⊑_ (Hom (carrier A) (carrier A))
          (id ∘ step A)
          (step A ∘ id)
    id-commute A =
      let
        module R = ≤-Reasoning (Hom (carrier A) (carrier A))
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        (id ∘ step A)
          ⊑⟨ fst (Laws.id-left (step A)) ⟩
        step A
          ⊑⟨ snd (Laws.id-right (step A)) ⟩
        (step A ∘ id) ∎⊑

    -- Composition of commuting maps commutes (semiconjugacy is stable under composition).
    comp-commute
      : ∀ {A B D : EndoObj C}
        (f : EndoHom L B D)
        (g : EndoHom L A B)
      → _⊑_ (Hom (carrier A) (carrier D))
          ((map f ∘ map g) ∘ step A)
          (step D ∘ (map f ∘ map g))
    comp-commute {A} {B} {D} f g =
      let
        -- Abbreviations.
        a = carrier A
        b = carrier B
        d = carrier D

        f₀ = map f
        g₀ = map g

        α = step A
        β = step B
        δ = step D

        HomAD = Hom a d
        -- Assoc witnesses in both directions.
        assoc-fgα : _≈_ HomAD ((f₀ ∘ g₀) ∘ α) (f₀ ∘ (g₀ ∘ α))
        assoc-fgα = Laws.assoc f₀ g₀ α

        assoc-fβα : _≈_
          (Hom a d)
          (Base._∘_ (Base._∘_ f₀ β) g₀)
          (Base._∘_ f₀ (Base._∘_ β g₀))
        assoc-fβα = Laws.assoc f₀ β g₀

        assoc-δfg : _≈_ HomAD ((δ ∘ f₀) ∘ g₀) (δ ∘ (f₀ ∘ g₀))
        assoc-δfg = Laws.assoc δ f₀ g₀

        step1 : _⊑_ HomAD ((f₀ ∘ g₀) ∘ α) (f₀ ∘ (g₀ ∘ α))
        step1 = fst assoc-fgα

        step2 : _⊑_ HomAD (f₀ ∘ (g₀ ∘ α)) (f₀ ∘ (β ∘ g₀))
        step2 = comp-mono-r (commute g)

        step3 : _⊑_ HomAD (f₀ ∘ (β ∘ g₀)) ((f₀ ∘ β) ∘ g₀)
        step3 = snd assoc-fβα

        step4 : _⊑_ HomAD ((f₀ ∘ β) ∘ g₀) ((δ ∘ f₀) ∘ g₀)
        step4 = comp-mono-l (commute f)

        step5 : _⊑_ HomAD ((δ ∘ f₀) ∘ g₀) (δ ∘ (f₀ ∘ g₀))
        step5 = fst assoc-δfg

      in
      let
        module R = ≤-Reasoning HomAD
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      begin⊑
        ((f₀ ∘ g₀) ∘ α)
          ⊑⟨ step1 ⟩
        (f₀ ∘ (g₀ ∘ α))
          ⊑⟨ step2 ⟩
        (f₀ ∘ (β ∘ g₀))
          ⊑⟨ step3 ⟩
        ((f₀ ∘ β) ∘ g₀)
          ⊑⟨ step4 ⟩
        ((δ ∘ f₀) ∘ g₀)
          ⊑⟨ step5 ⟩
        (δ ∘ (f₀ ∘ g₀)) ∎⊑
  in
  record
    { Obj = EndoObj C
    ; Hom = EndoHomPreorder L
    ; id = λ {A} →
        record
          { map = id
          ; commute = id-commute A
          }
    ; _∘_ = λ {A} {B} {D} f g →
        record
          { map = map f ∘ map g
          ; commute = comp-commute f g
          }
    ; comp-mono-l = λ {A} {B} {D} {f} {f'} {g} le →
        Base.comp-mono-l le
    ; comp-mono-r = λ {A} {B} {D} {f} {g} {g'} le →
        Base.comp-mono-r le
    }
