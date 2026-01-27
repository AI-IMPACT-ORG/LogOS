{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.2Cat where

-- 2-categorical view: kernels as objects, morphisms as 1-cells,
-- refinements as preorder 2-cells.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
import LogOS.Kernel.Hom2Cat as K2
import LogOS.Theorems.CategoryTheory.WrapperCore as Wrap

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  open K2 public
    using
      ( KernelThin2Cat
      ; KernelThin2CatLaws
      ; KernelHom₁
      ; KernelHomPreorder
      ; idKernelHom₁
      ; _∘₁_
      ; _⇒_
      ; _≈_
      ; refl⇒
      ; trans⇒
      ; whiskerL
      ; whiskerR
      ; _⊙_
      )

  -- Naming coherence: provide the Thin2Cat-style whisker names.
  whisker-left = whiskerL
  whisker-right = whiskerR

  -- Unpack a refinement 2-cell as pointwise decoded refinement.
  refines-at
    : ∀ {K₁ K₂ : Kernel Sig Q}
      {f g : KernelHom₁ K₁ K₂}
    → f ⇒ g
    → ∀ gamma
    → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
        (Kernel.decode K₂ (KernelHom₁.mapCode₁ f gamma))
        (Kernel.decode K₂ (KernelHom₁.mapCode₁ g gamma))
  refines-at r gamma = r gamma

  -- Wrapper-core 2-category interface instance.
  KernelRef2Cat : Wrap.Ref2Cat Sig Q
  KernelRef2Cat =
    record
      { Obj = Kernel Sig Q
      ; Hom = KernelHom₁
      ; _∘_ = λ g f → _∘₁_ g f
      ; id  = λ {A} → idKernelHom₁ A
      ; _⇒_ = _⇒_
      ; id⇒ = λ {A} {B} f → refl⇒ f
      ; _∙_ = λ {A} {B} {f} {g} {h} fg gh →
                trans⇒ {f = f} {g = g} {h = h} fg gh
      ; whiskerL = λ {A} {B} {C} g {f} {f'} ff' →
                     whiskerL {K₁ = A} {K₂ = B} {K₃ = C} g {f = f} {f' = f'} ff'
      ; whiskerR = λ {A} {B} {C} {g} {g'} f gg' →
                     whiskerR {K₁ = A} {K₂ = B} {K₃ = C} {g = g} {g' = g'} f gg'
      ; _⊙_ = λ {A} {B} {C} {f} {f'} {g} {g'} ff' gg' →
               _⊙_ {K₁ = A} {K₂ = B} {K₃ = C} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg'
      }
