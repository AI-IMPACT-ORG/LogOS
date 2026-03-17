{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.PreQuantum.Purification where

-- Purification / Stinespring-style assumptions as an explicit strengthening.
--
-- This file intentionally does *not* build a CPM/environment construction.
-- Instead it packages a “dilation exists” claim as a record, so that the
-- additional strength is explicit and dependency-injected. The law-port layer
-- also asks for an explicit witness calculus (identity + composition), rather
-- than silently re-choosing witnesses after totalisation.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PreQuantum.Monoidal using (SymmetricMonoidalData; SymmetricMonoidalLaws; Iso)
open import LogOS.Ports.PreQuantum.Discard using (DiscardStructure)

-- A single purification witness for a morphism `f : A → B`.
--
-- Data:
-- - an environment object `E`,
-- - a dilation `u : A → B ⊗ E`.
--
-- Law:
-- - discarding the environment recovers `f` up to observation.
record PurificationWitness {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (M : SymmetricMonoidalData C)
  (ML : SymmetricMonoidalLaws M)
  (D : DiscardStructure C M)
  {A B : Thin2Cat.Obj C}
  (f : Con (Thin2Cat.Hom C A B))
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  open SymmetricMonoidalData M
  open SymmetricMonoidalLaws ML
  open DiscardStructure D
  private
    infixl 7 _⊗₀_
    infixl 7 _⊗₁_

    _⊗₀_ : Obj → Obj → Obj
    A ⊗₀ B = SymmetricMonoidalData._⊗₀ᵒ_ M A B

    _⊗₁_
      : ∀ {A B C₀ D}
      → Con (Hom A B)
      → Con (Hom C₀ D)
      → Con (Hom (A ⊗₀ C₀) (B ⊗₀ D))
    f ⊗₁ g = SymmetricMonoidalData._⊗₁ᵐ_ M f g

    ρ→ : ∀ {A} → Con (Hom (A ⊗₀ I) A)
    ρ→ {A} = Iso.to (ρᵤ {A = A})

  field
    E : Obj
    u : Con (Hom A (B ⊗₀ E))

    law
      : _≈_ (Hom A B)
          (ρ→ {A = B} ∘ ((id {A = B} ⊗₁ discard {A = E}) ∘ u))
          f

open PurificationWitness public

record PurificationWitnessOps {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (M : SymmetricMonoidalData C)
  (ML : SymmetricMonoidalLaws M)
  (D : DiscardStructure C M)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    idWitness
      : ∀ {A}
      → PurificationWitness C M ML D (id {A = A})

    composeWitness
      : ∀ {A B C₀}
        {f : Con (Hom A B)}
        {g : Con (Hom B C₀)}
      → PurificationWitness C M ML D f
      → PurificationWitness C M ML D g
      → PurificationWitness C M ML D (g ∘ f)

open PurificationWitnessOps public

record PurificationAssumptions {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (M : SymmetricMonoidalData C)
  (ML : SymmetricMonoidalLaws M)
  (D : DiscardStructure C M)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    purify
      : ∀ {A B}
        (f : Con (Hom A B))
      → PurificationWitness C M ML D f

    witnessOps
      : PurificationWitnessOps C M ML D

purify-id
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {M : SymmetricMonoidalData C}
    {ML : SymmetricMonoidalLaws M}
    {D : DiscardStructure C M}
  → (P : PurificationAssumptions C M ML D)
  → ∀ {A}
  → PurificationWitness C M ML D (Thin2Cat.id C {A = A})
purify-id P =
  idWitness (PurificationAssumptions.witnessOps P)

purify-comp
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {M : SymmetricMonoidalData C}
    {ML : SymmetricMonoidalLaws M}
    {D : DiscardStructure C M}
  → (P : PurificationAssumptions C M ML D)
  → ∀ {A B C₀}
    {f : Con (Thin2Cat.Hom C A B)}
    {g : Con (Thin2Cat.Hom C B C₀)}
  → PurificationWitness C M ML D f
  → PurificationWitness C M ML D g
  → PurificationWitness C M ML D (Thin2Cat._∘_ C g f)
purify-comp P =
  composeWitness (PurificationAssumptions.witnessOps P)

open PurificationAssumptions public
