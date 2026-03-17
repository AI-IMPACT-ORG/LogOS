{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Functor where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Functors between locally preordered 2-categories.
--
-- We only demand preservation of identity/composition up to mutual refinement (`≈`),
-- matching the 1.1 stance that equations live in S-tier while refinement lives in G-tier.
--
-- Engineering reading:
-- a structure-preserving translation between “component graphs”, which may only
-- preserve wiring laws up to refinement (not strict equality).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; MonoMap
  ; _≈_
  ; _⊑_
  ; Reflects⊑
  ; Reflects≈
  ; idMonoMap
  ; monoMap-≈
  ; ≈-refl
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat; PullbackThin2Cat)

record Thin2Functor
  {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
  (C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁)
  (C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂)
  : Set (lsuc (ℓObj₁ ⊔ ℓHomCon₁ ⊔ ℓHomRel₁ ⊔ ℓObj₂ ⊔ ℓHomCon₂ ⊔ ℓHomRel₂)) where
  private
    module C = Thin2Cat C₁
    module D = Thin2Cat C₂
  field
    mapObj : C.Obj → D.Obj

    mapHom : ∀ {A B} → Con (C.Hom A B) → Con (D.Hom (mapObj A) (mapObj B))
    mapHom-mono
      : ∀ {A B}
      → MonoMap (C.Hom A B) (D.Hom (mapObj A) (mapObj B)) mapHom

    id-pres
      : ∀ {A}
      → _≈_ (D.Hom (mapObj A) (mapObj A)) (mapHom (C.id {A})) (D.id {A = mapObj A})

    comp-pres
      : ∀ {A B C₀}
        (f : Con (C.Hom B C₀))
        (g : Con (C.Hom A B))
      → _≈_ (D.Hom (mapObj A) (mapObj C₀))
          (mapHom (f C.∘ g))
          (mapHom f D.∘ mapHom g)

open Thin2Functor public
-- --------------------------------------------------------------------------
-- Basic algebra: identity and composition.

mapHom-≈
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → (F : Thin2Functor C₁ C₂)
  → ∀ {A B} {f g : Con (Thin2Cat.Hom C₁ A B)}
  → _≈_ (Thin2Cat.Hom C₁ A B) f g
  → _≈_ (Thin2Cat.Hom C₂ (mapObj F A) (mapObj F B)) (mapHom F f) (mapHom F g)
mapHom-≈ {C₁ = C₁} {C₂ = C₂} F {A} {B} {f = f} {g = g} eq =
  monoMap-≈
    {CP₁ = Thin2Cat.Hom C₁ A B}
    {CP₂ = Thin2Cat.Hom C₂ (mapObj F A) (mapObj F B)}
    {f = mapHom F}
    (mapHom-mono F {A = A} {B = B})
    f g eq

HomwiseReflects⊑
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → (F : Thin2Functor C₁ C₂)
  → Set (ℓObj₁ ⊔ ℓHomCon₁ ⊔ ℓHomRel₁ ⊔ ℓHomRel₂)
HomwiseReflects⊑ {C₁ = C₁} {C₂ = C₂} F =
  ∀ {A B}
  → Reflects⊑
      (Thin2Cat.Hom C₁ A B)
      (Thin2Cat.Hom C₂ (mapObj F A) (mapObj F B))
      (mapHom F)

HomwiseReflects≈
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → (F : Thin2Functor C₁ C₂)
  → Set (ℓObj₁ ⊔ ℓHomCon₁ ⊔ ℓHomRel₁ ⊔ ℓHomRel₂)
HomwiseReflects≈ {C₁ = C₁} {C₂ = C₂} F =
  ∀ {A B}
  → Reflects≈
      (Thin2Cat.Hom C₁ A B)
      (Thin2Cat.Hom C₂ (mapObj F A) (mapObj F B))
      (mapHom F)

record ConservativeThin2Functor
  {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
  (C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁)
  (C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂)
  : Set (lsuc (ℓObj₁ ⊔ ℓHomCon₁ ⊔ ℓHomRel₁ ⊔ ℓObj₂ ⊔ ℓHomCon₂ ⊔ ℓHomRel₂)) where
  field
    functor : Thin2Functor C₁ C₂
    reflects-hom⊑ : HomwiseReflects⊑ functor

  reflects-hom≈ : HomwiseReflects≈ functor
  reflects-hom≈ {A} {B} {f} {g} (fg , gf) =
    (reflects-hom⊑ {A} {B} fg , reflects-hom⊑ {A} {B} gf)

  open Thin2Functor functor public

idThin2Functor
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
  → (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  → Thin2Functor C C
idThin2Functor C =
  let module C = Thin2Cat C in
  record
    { mapObj = λ X → X
    ; mapHom = λ f → f
    ; mapHom-mono = λ {A} {B} → idMonoMap {CP = C.Hom A B}
    ; id-pres = λ {A} →
        ≈-refl (C.Hom A A) (C.id {A})
    ; comp-pres = λ {A} {B} {C₀} f g →
        ≈-refl (C.Hom A C₀) (f C.∘ g)
    }

idConservativeThin2Functor
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
  → (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  → ConservativeThin2Functor C C
idConservativeThin2Functor C =
  let
    module C = Thin2Cat C
  in
  record
    { functor = idThin2Functor C
    ; reflects-hom⊑ = λ {A} {B} h≤k → h≤k
    }

-- --------------------------------------------------------------------------
-- Standard constructors (keep “identity on morphisms” boilerplate out of ports/apps).

forgetPullbackThin2Functor
  : ∀ {ℓObj' ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (Obj' : Set ℓObj')
  → (F : Obj' → Thin2Cat.Obj C)
  → Thin2Functor (PullbackThin2Cat {C = C} Obj' F) C
forgetPullbackThin2Functor {C = C} Obj' F =
  let module C = Thin2Cat C in
  record
    { mapObj = F
    ; mapHom = λ f → f
    ; mapHom-mono = λ le → le
    ; id-pres = λ {A} → ≈-refl (C.Hom (F A) (F A)) _
    ; comp-pres = λ {A} {B} {C₀} f g → ≈-refl (C.Hom (F A) (F C₀)) _
    }

infixr 9 _∘F_
_∘F_
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ ℓObj₃ ℓHomCon₃ ℓHomRel₃ : Level}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
    {C₃ : Thin2Cat ℓObj₃ ℓHomCon₃ ℓHomRel₃}
  → Thin2Functor C₂ C₃
  → Thin2Functor C₁ C₂
  → Thin2Functor C₁ C₃
_∘F_ {C₁ = C₁} {C₂ = C₂} {C₃ = C₃} G F =
  let
    module C₁ = Thin2Cat C₁
    module C₂ = Thin2Cat C₂
    module C₃ = Thin2Cat C₃
  in
  record
    { mapObj = λ X → mapObj G (mapObj F X)
    ; mapHom = λ f → mapHom G (mapHom F f)
    ; mapHom-mono = λ {A} {B} →
        λ {x} {y} le →
          mapHom-mono G {A = mapObj F A} {B = mapObj F B}
            (mapHom-mono F {A = A} {B = B} le)
    ; id-pres = λ {A} →
        let
          CP = C₃.Hom (mapObj G (mapObj F A)) (mapObj G (mapObj F A))
          module R = LogOS.Prelude.RefinementKit.Reasoning CP
          ab = mapHom-≈ G (id-pres F {A = A})
          bc = id-pres G {A = mapObj F A}
        in
        R._≈⟨_⟩_
          (mapHom G (mapHom F (C₁.id {A})))
          ab
          bc
    ; comp-pres = λ {A} {B} {C₀} f g →
        let
          CP = C₃.Hom (mapObj G (mapObj F A)) (mapObj G (mapObj F C₀))
          module R = LogOS.Prelude.RefinementKit.Reasoning CP
          ab = mapHom-≈ G (comp-pres F f g)
          bc = comp-pres G (mapHom F f) (mapHom F g)
        in
        R._≈⟨_⟩_
          (mapHom G (mapHom F (f C₁.∘ g)))
          ab
          bc
    }
