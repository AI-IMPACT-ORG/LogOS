{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.CH2008 where

-- CH2008 (Cockett–Hofstra) style interfaces for restriction/Turing categories,
-- phrased in the LogOS “refinement-first” discipline:
-- - base categories are `Thin2Cat` (locally preordered 2-categories),
-- - laws are stated up to mutual refinement (`≈`), not strict equality (`≡`),
-- - “a vs b” variants expose where an explicit choice/indexing function is used.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

-- --------------------------------------------------------------------------
-- Restriction structure (the partial-map discipline).

record RestrictionStructure
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C

  infix 30 _̄
  field
    -- Restriction idempotent (a partial identity on the domain of definition).
    bar : ∀ {A B} → Con (Hom A B) → Con (Hom A A)

    -- Restriction category axioms (CH style), stated up to `≈`.
    R1 : ∀ {A B} (f : Con (Hom A B)) → _≈_ (Hom A B) (f ∘ bar f) f

    R2 : ∀ {A B C₀} (f : Con (Hom A B)) (g : Con (Hom A C₀))
       → _≈_ (Hom A A) (bar f ∘ bar g) (bar g ∘ bar f)

    R3 : ∀ {A B C₀} (f : Con (Hom A B)) (g : Con (Hom A C₀))
       → _≈_ (Hom A A) (bar (g ∘ bar f)) (bar g ∘ bar f)

    R4 : ∀ {A B C₀} (f : Con (Hom A B)) (g : Con (Hom B C₀))
       → _≈_ (Hom A B) (bar g ∘ f) (f ∘ bar (g ∘ f))

  _̄ : ∀ {A B} → Con (Hom A B) → Con (Hom A A)
  _̄ = bar

open RestrictionStructure public

Total
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (R : RestrictionStructure C)
  → ∀ {A B} → Con (Thin2Cat.Hom C A B) → Set _
Total {C = C} R {A} f =
  _≈_ (Thin2Cat.Hom C A A) (RestrictionStructure.bar R f) (Thin2Cat.id C {A = A})

-- A bundled “restriction category” here is: a thin 2-category + its laws + a
-- restriction structure on top.
record RestrictionCategory
  {ℓObj ℓHomCon ℓHomRel : Level}
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  field
    C    : Thin2Cat ℓObj ℓHomCon ℓHomRel
    laws : Thin2CatLaws C
    R    : RestrictionStructure C

open RestrictionCategory public

-- --------------------------------------------------------------------------
-- Cartesian structure (needed for “program + input”).

record CartesianStructure
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  infix 30 !_
  field
    𝟙   : Obj
    !_  : ∀ {A} → Con (Hom A 𝟙)

    prod : Obj → Obj → Obj
    π₁   : ∀ {A B} → Con (Hom (prod A B) A)
    π₂   : ∀ {A B} → Con (Hom (prod A B) B)

    ⟨_,_⟩ : ∀ {Z A B} → Con (Hom Z A) → Con (Hom Z B) → Con (Hom Z (prod A B))

open CartesianStructure public

-- --------------------------------------------------------------------------
-- Turing objects (globalised/indexed view; “a vs b” = existence vs choice).

-- CH-style *global* evaluation family.
--
-- Reading: `τ X Y : U×X ⇀ Y` runs code/programs in `U` on an input from `X`,
-- producing an output in `Y` (possibly undefined, tracked by restriction).
record EvalFamily
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (cart : CartesianStructure C)
  (U : Thin2Cat.Obj C)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  open CartesianStructure cart
  field
    τ : (X Y : Obj) → Con (Hom (CartesianStructure.prod cart U X) Y)

open EvalFamily public

-- (a) Existence-only indexing axiom (no global choice function).
record TuringObjectᵃ
  {ℓObj ℓHomCon ℓHomRel : Level}
  (RC : RestrictionCategory {ℓObj} {ℓHomCon} {ℓHomRel})
  (cart : CartesianStructure (RestrictionCategory.C RC))
  (U : Thin2Cat.Obj (RestrictionCategory.C RC))
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  private
    C₀ = RestrictionCategory.C RC
  open Thin2Cat C₀
  open RestrictionStructure (RestrictionCategory.R RC)
  open CartesianStructure cart

  field
    eval : EvalFamily C₀ cart U

    -- Universal indexing (existence form):
    -- every map `f : X ⇀ Y` is simulated by running some *total* index `p : X → U`
    -- at the boundary: `f ≈ τ X Y ∘ ⟨p , id⟩`.
    indexᵃ
      : ∀ {X Y : Obj}
      → (f : Con (Hom X Y))
      → Σ
          (Con (Hom X U))
          (λ p →
            Total (RestrictionCategory.R RC) {A = X} {B = U} p
            × _≈_
                (Hom X Y)
                (EvalFamily.τ eval X Y ∘ CartesianStructure.⟨_,_⟩ cart p (id {A = X}))
                f)

open TuringObjectᵃ public

-- (b) Chosen indexer (a concrete “compiler” into `U`), exposing the extra data.
record TuringObjectᵇ
  {ℓObj ℓHomCon ℓHomRel : Level}
  (RC : RestrictionCategory {ℓObj} {ℓHomCon} {ℓHomRel})
  (cart : CartesianStructure (RestrictionCategory.C RC))
  (U : Thin2Cat.Obj (RestrictionCategory.C RC))
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  private
    C₀ = RestrictionCategory.C RC
  open Thin2Cat C₀
  open RestrictionStructure (RestrictionCategory.R RC)
  open CartesianStructure cart

  field
    eval : EvalFamily C₀ cart U

    index : ∀ {X Y : Obj} → Con (Hom X Y) → Con (Hom X U)

    index-total : ∀ {X Y : Obj} (f : Con (Hom X Y))
      → Total (RestrictionCategory.R RC) {A = X} {B = U} (index f)

    index-sound : ∀ {X Y : Obj} (f : Con (Hom X Y))
      → _≈_
          (Hom X Y)
          (EvalFamily.τ eval X Y ∘ CartesianStructure.⟨_,_⟩ cart (index f) (id {A = X}))
          f

open TuringObjectᵇ public

-- A CH-style “Turing category” (globalised form, as requested):
-- a restriction category with cartesian structure + a designated Turing object.
record TuringCategoryᵃ
  {ℓObj ℓHomCon ℓHomRel : Level}
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  field
    RC   : RestrictionCategory {ℓObj} {ℓHomCon} {ℓHomRel}
    cart : CartesianStructure (RestrictionCategory.C RC)
    U    : Thin2Cat.Obj (RestrictionCategory.C RC)
    TU   : TuringObjectᵃ RC cart U

open TuringCategoryᵃ public

record TuringCategoryᵇ
  {ℓObj ℓHomCon ℓHomRel : Level}
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  field
    RC   : RestrictionCategory {ℓObj} {ℓHomCon} {ℓHomRel}
    cart : CartesianStructure (RestrictionCategory.C RC)
    U    : Thin2Cat.Obj (RestrictionCategory.C RC)
    TU   : TuringObjectᵇ RC cart U

open TuringCategoryᵇ public
