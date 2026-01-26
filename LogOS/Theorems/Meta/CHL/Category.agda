{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Category where

-- Category-theory view: code refinements form a thin category, and `Box`
-- (stable closure at Th*) is a monotone endofunctor on it.
--
-- Note: the core packaging here is intentionally “ops-only”: we do not assume
-- proof-irrelevance for refinement proofs, so the usual category laws
-- (associativity/unit) are not stated by default. A fully lawful category view
-- is recoverable under an explicit thinness/proof-irrelevance assumption; see
-- `ThinCatLaws` / `EndoFunctorLaws` below.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (MonoOn)

open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
open import LogOS.Kernel.Core as KCore hiding (FlowCode)
import LogOS.Theorems.Meta.CHL.Core as CHL

record ThinCat (ℓ : Level) : Set (lsuc ℓ) where
  infixr 9 _∘_
  field
    Obj : Set ℓ
    Hom : Obj → Obj → Set ℓ
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

record EndoFunctor {ℓ : Level} (C : ThinCat ℓ) : Set (lsuc ℓ) where
  open ThinCat C
  field
    F     : Obj → Obj
    map   : ∀ {A B} → Hom A B → Hom (F A) (F B)
    map-id : ∀ {A} → Hom (F A) (F A)
    map-cut : ∀ {A B C} → Hom A B → Hom B C → Hom (F A) (F C)

-- -----------------------------------------------------------------------------
-- Optional strengthening: make the category/functor laws explicit
-- -----------------------------------------------------------------------------

ThinHom : ∀ {ℓ} (C : ThinCat ℓ) → Set ℓ
ThinHom C =
  let open ThinCat C in
  ∀ {A B} (f g : Hom A B) → f ≡ g

record ThinCatLaws {ℓ : Level} (C : ThinCat ℓ) : Set ℓ where
  open ThinCat C
  field
    id-left  : ∀ {A B} (f : Hom A B) → (id ∘ f) ≡ f
    id-right : ∀ {A B} (f : Hom A B) → (f ∘ id) ≡ f
    assoc    : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B)
             → ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))

thin→laws : ∀ {ℓ} {C : ThinCat ℓ} → ThinHom C → ThinCatLaws C
thin→laws {C = C} thin =
  let open ThinCat C in
  record
    { id-left  = λ f → thin (id ∘ f) f
    ; id-right = λ f → thin (f ∘ id) f
    ; assoc    = λ h g f → thin ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
    }

record EndoFunctorLaws {ℓ : Level} {C : ThinCat ℓ} (E : EndoFunctor C) : Set ℓ where
  open ThinCat C
  open EndoFunctor E
  field
    preserves-id
      : ∀ {A}
      → map (id {A = A}) ≡ id {A = F A}
    preserves-∘
      : ∀ {A B C₁} (g : Hom B C₁) (f : Hom A B)
      → map (g ∘ f) ≡ (map g ∘ map f)

thin→endoFunctorLaws
  : ∀ {ℓ} {C : ThinCat ℓ} (thin : ThinHom C) (E : EndoFunctor C)
  → EndoFunctorLaws E
thin→endoFunctorLaws {C = C} thin E =
  let open ThinCat C
      open EndoFunctor E
  in
  record
    { preserves-id = λ {A} → thin (map (id {A = A})) (id {A = F A})
    ; preserves-∘  = λ g f → thin (map (g ∘ f)) (map g ∘ map f)
    }

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C = CHL.For K
  open C hiding (box-monoOn; box-respects-equiv)

  CodeThinCat : ThinCat ℓ
  CodeThinCat =
    record
      { Obj = Ty
      ; Hom = Refines
      ; id  = refl-refines
      ; _∘_ = λ g f → cut-refines f g
      }

  -- Box acts as a monotone endofunctor on the thin code category.
  box-monoOn : MonoOn (KCore.CodePreorder (Kernel.shape K)) Box
  box-monoOn = C.box-monoOn

  box-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Box gamma) (Box delta)
  box-respects-equiv = C.box-respects-equiv

  -- Box as an endofunctor (proof-relevant: we only claim the mapped morphisms).
  BoxFunctor : EndoFunctor CodeThinCat
  BoxFunctor =
    record
      { F       = Box
      ; map     = box-mono
      ; map-id  = refl-refines
      ; map-cut = λ f g → box-mono (cut-refines f g)
      }

  -- Lawful category/functor view under a “thinness” assumption for refinement.

  ThinRefines : Set ℓ
  ThinRefines = ThinHom CodeThinCat

  codeCat-laws : ThinRefines → ThinCatLaws CodeThinCat
  codeCat-laws = thin→laws

  boxFunctor-laws : (thin : ThinRefines) → EndoFunctorLaws BoxFunctor
  boxFunctor-laws thin = thin→endoFunctorLaws thin BoxFunctor
