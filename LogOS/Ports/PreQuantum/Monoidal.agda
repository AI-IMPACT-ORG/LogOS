{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.Monoidal where

-- Symmetric monoidal structure as an explicit port/assumption layer.
--
-- This is intentionally phrased over `Thin2Cat`: the LogOS kernel does not
-- assume parallel composition; it is supplied explicitly when wanted.
--
-- Discipline note:
-- - laws are stated up to mutual refinement (`≈`) in the hom-preorders;
-- - coherence is isolated into a separate record (`SymmetricMonoidalLaws`),
--   so one can work with “data only” when appropriate.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

-- Isomorphisms in a locally preordered 2-category:
-- a pair of 1-cells with inverse laws up to observational equivalence (`≈`).
record Iso {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (A B : Thin2Cat.Obj C)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    to   : Con (Hom A B)
    from : Con (Hom B A)

    to-from≈id : _≈_ (Hom B B) (to ∘ from) id
    from-to≈id : _≈_ (Hom A A) (from ∘ to) id

open Iso public
-- Tensor as a bifunctor (no coherence assumed here).
record BifunctorTensor {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  infixl 7 _⊗₀_
  infixl 7 _⊗₁_

  field
    _⊗₀_ : Obj → Obj → Obj

    _⊗₁_
      : ∀ {A B C D}
      → Con (Hom A B)
      → Con (Hom C D)
      → Con (Hom (A ⊗₀ C) (B ⊗₀ D))

    ⊗₁-mono
      : ∀ {A B C D}
        {f f' : Con (Hom A B)}
        {g g' : Con (Hom C D)}
      → _⊑_ (Hom A B) f f'
      → _⊑_ (Hom C D) g g'
      → _⊑_ (Hom (A ⊗₀ C) (B ⊗₀ D)) (f ⊗₁ g) (f' ⊗₁ g')

    ⊗₁-id≈
      : ∀ {A C}
      → _≈_ (Hom (A ⊗₀ C) (A ⊗₀ C))
          (id {A} ⊗₁ id {A = C})
          (id {A = A ⊗₀ C})

    ⊗₁-comp≈
      : ∀ {A B D C E F}
        (f : Con (Hom A B))
        (g : Con (Hom B D))
        (h : Con (Hom C E))
        (k : Con (Hom E F))
      → _≈_ (Hom (A ⊗₀ C) (D ⊗₀ F))
          ((g ∘ f) ⊗₁ (k ∘ h))
          ((g ⊗₁ k) ∘ (f ⊗₁ h))

-- Note: we intentionally do not `open BifunctorTensor public` here.
-- The field names are common (`_⊗₀_`, `_⊗₁_`), and making them global invites
-- ambiguous projection errors in refinement-first developments.

-- Symmetric monoidal *data* over a thin 2-category.
--
-- This is the standard package of:
-- - a tensor bifunctor (on objects + morphisms),
-- - a unit object `I`,
-- - associator/unitors/braiding isomorphisms.
record SymmetricMonoidalData {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    tensor : BifunctorTensor C

  open BifunctorTensor tensor renaming (_⊗₀_ to _⊗₀ᵒ_; _⊗₁_ to _⊗₁ᵐ_) public

  field
    I : Obj

    α : ∀ {A B C₀} → Iso C ((A ⊗₀ᵒ B) ⊗₀ᵒ C₀) (A ⊗₀ᵒ (B ⊗₀ᵒ C₀))
    λᵤ : ∀ {A} → Iso C (I ⊗₀ᵒ A) A
    ρᵤ : ∀ {A} → Iso C (A ⊗₀ᵒ I) A
    σ : ∀ {A B} → Iso C (A ⊗₀ᵒ B) (B ⊗₀ᵒ A)

-- As above, we keep the symmetric monoidal vocabulary namespaced unless the
-- caller explicitly opens the record.

-- Coherence/naturality laws for symmetric monoidal structure.
--
-- This is a separate record so that developments can remain explicit about
-- when they are using only the operations vs the full monoidal theory.
record SymmetricMonoidalLaws {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  (M : SymmetricMonoidalData C)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  private
    infixl 7 _⊗₀ᵐ_
    infixl 7 _⊗₁ᵐ_

    _⊗₀ᵐ_ : Obj → Obj → Obj
    A ⊗₀ᵐ B = SymmetricMonoidalData._⊗₀ᵒ_ M A B

    _⊗₁ᵐ_
      : ∀ {A B C₀ D}
      → Con (Hom A B)
      → Con (Hom C₀ D)
      → Con (Hom (A ⊗₀ᵐ C₀) (B ⊗₀ᵐ D))
    f ⊗₁ᵐ g = SymmetricMonoidalData._⊗₁ᵐ_ M f g

    I : Obj
    I = SymmetricMonoidalData.I M

  private
    α→ : ∀ {A B C₀} → Con (Hom ((A ⊗₀ᵐ B) ⊗₀ᵐ C₀) (A ⊗₀ᵐ (B ⊗₀ᵐ C₀)))
    α→ {A} {B} {C₀} = to (SymmetricMonoidalData.α M {A = A} {B = B} {C₀ = C₀})

    α← : ∀ {A B C₀} → Con (Hom (A ⊗₀ᵐ (B ⊗₀ᵐ C₀)) ((A ⊗₀ᵐ B) ⊗₀ᵐ C₀))
    α← {A} {B} {C₀} = from (SymmetricMonoidalData.α M {A = A} {B = B} {C₀ = C₀})

    λ→ : ∀ {A} → Con (Hom (I ⊗₀ᵐ A) A)
    λ→ {A} = to (SymmetricMonoidalData.λᵤ M {A = A})

    λ← : ∀ {A} → Con (Hom A (I ⊗₀ᵐ A))
    λ← {A} = from (SymmetricMonoidalData.λᵤ M {A = A})

    ρ→ : ∀ {A} → Con (Hom (A ⊗₀ᵐ I) A)
    ρ→ {A} = to (SymmetricMonoidalData.ρᵤ M {A = A})

    ρ← : ∀ {A} → Con (Hom A (A ⊗₀ᵐ I))
    ρ← {A} = from (SymmetricMonoidalData.ρᵤ M {A = A})

    σ→ : ∀ {A B} → Con (Hom (A ⊗₀ᵐ B) (B ⊗₀ᵐ A))
    σ→ {A} {B} = to (SymmetricMonoidalData.σ M {A = A} {B = B})

    σ← : ∀ {A B} → Con (Hom (B ⊗₀ᵐ A) (A ⊗₀ᵐ B))
    σ← {A} {B} = from (SymmetricMonoidalData.σ M {A = A} {B = B})

  field
    -- Naturality of the associator.
    α-natural
      : ∀ {A A' B B' C₀ C₀'}
        (f : Con (Hom A A'))
        (g : Con (Hom B B'))
        (h : Con (Hom C₀ C₀'))
      → _≈_ (Hom ((A ⊗₀ᵐ B) ⊗₀ᵐ C₀) (A' ⊗₀ᵐ (B' ⊗₀ᵐ C₀')))
          ((f ⊗₁ᵐ (g ⊗₁ᵐ h)) ∘ α→ {A = A} {B = B} {C₀ = C₀})
          (α→ {A = A'} {B = B'} {C₀ = C₀'} ∘ ((f ⊗₁ᵐ g) ⊗₁ᵐ h))

    -- Naturality of the unitors.
    λ-natural
      : ∀ {A B}
        (f : Con (Hom A B))
      → _≈_ (Hom (I ⊗₀ᵐ A) B)
          (f ∘ λ→ {A = A})
          (λ→ {A = B} ∘ (id {A = I} ⊗₁ᵐ f))

    ρ-natural
      : ∀ {A B}
        (f : Con (Hom A B))
      → _≈_ (Hom (A ⊗₀ᵐ I) B)
          (f ∘ ρ→ {A = A})
          (ρ→ {A = B} ∘ (f ⊗₁ᵐ id {A = I}))

    -- Naturality of the braiding.
    σ-natural
      : ∀ {A A' B B'}
        (f : Con (Hom A A'))
        (g : Con (Hom B B'))
      → _≈_ (Hom (A ⊗₀ᵐ B) (B' ⊗₀ᵐ A'))
          ((g ⊗₁ᵐ f) ∘ σ→ {A = A} {B = B})
          (σ→ {A = A'} {B = B'} ∘ (f ⊗₁ᵐ g))

    -- Coherence: pentagon for the associator.
    pentagon
      : ∀ {A B C₀ D}
      → _≈_ (Hom (((A ⊗₀ᵐ B) ⊗₀ᵐ C₀) ⊗₀ᵐ D) (A ⊗₀ᵐ (B ⊗₀ᵐ (C₀ ⊗₀ᵐ D))))
          (α→ {A = A} {B = B} {C₀ = C₀ ⊗₀ᵐ D}
            ∘
            α→ {A = A ⊗₀ᵐ B} {B = C₀} {C₀ = D})
          ((id {A = A} ⊗₁ᵐ α→ {A = B} {B = C₀} {C₀ = D})
            ∘
            (α→ {A = A} {B = B ⊗₀ᵐ C₀} {C₀ = D}
              ∘
              (α→ {A = A} {B = B} {C₀ = C₀} ⊗₁ᵐ id {A = D})))

    -- Coherence: triangle for associator + unitors.
    triangle
      : ∀ {A B}
      → _≈_ (Hom ((A ⊗₀ᵐ I) ⊗₀ᵐ B) (A ⊗₀ᵐ B))
          ((id {A = A} ⊗₁ᵐ λ→ {A = B}) ∘ α→ {A = A} {B = I} {C₀ = B})
          (ρ→ {A = A} ⊗₁ᵐ id {A = B})

    -- Coherence: braiding is involutive.
    symmetry
      : ∀ {A B}
      → _≈_ (Hom (A ⊗₀ᵐ B) (A ⊗₀ᵐ B))
          (σ→ {A = B} {B = A} ∘ σ→ {A = A} {B = B})
          (id {A = A ⊗₀ᵐ B})

-- Coherence laws are accessed by opening `SymmetricMonoidalLaws` explicitly.

-- Full symmetric monoidal structure as explicitly stacked packs.
record SymmetricMonoidal {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  field
    data₀ : SymmetricMonoidalData C
    laws₀ : SymmetricMonoidalLaws data₀

-- Full structure can be accessed by opening `SymmetricMonoidal` explicitly.
