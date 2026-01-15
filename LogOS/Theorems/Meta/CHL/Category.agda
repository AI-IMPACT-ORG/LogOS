{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Category where

-- Category-theory view: code refinements form a thin category, and FlowCode is
-- a monotone endofunctor on it.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (MonoOn)

open import LogOS.Kernel
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

  -- FlowCode acts as a monotone endofunctor on the thin code category.
  box-monoOn : MonoOn (KCore.CodePoset (Kernel.shape K)) Box
  box-monoOn = C.box-monoOn

  box-respects-equiv : ∀ {gamma delta} → Equiv gamma delta → Equiv (Box gamma) (Box delta)
  box-respects-equiv = C.box-respects-equiv

  -- FlowCode as an endofunctor (proof-relevant: we only claim the mapped morphisms).
  BoxFunctor : EndoFunctor CodeThinCat
  BoxFunctor =
    record
      { F       = Box
      ; map     = box-mono
      ; map-id  = refl-refines
      ; map-cut = λ f g → box-mono (cut-refines f g)
      }
