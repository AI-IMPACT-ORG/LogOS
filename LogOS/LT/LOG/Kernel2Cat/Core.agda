{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Kernel2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Kernel using (Kernel; bnd; Code)
open import LogOS.LT.Hom.Core using
    ( KernelHom
    ; idKernelHom
    ; _∘_
    ; _⇒∂_
    ; transportObs
    ; whiskerL∂
    ; whiskerR∂
    )
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
import LogOS.LT.Thin2Cat.Pointwise as Pointwise
import LogOS.LT.Thin2Cat.Pointwise.Strictification as PointwiseStrict

KernelHomPreorder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode → ConPreorder (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) (ℓCode ⊔ ℓRel)
KernelHomPreorder {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseHom
    Code
    bnd
    KernelHom
    transportObs

LOG
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
      (ℓCode ⊔ ℓRel)
LOG {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseThin2Cat
    (Kernel ℓ ℓRel ℓCode)
    Code
    bnd
    KernelHom
    transportObs
    (λ {A} → idKernelHom A)
    _∘_
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerR∂ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerL∂ f {f = g} {g = g'} le)

LOGLaws : ∀ {ℓ ℓRel ℓCode : Level} → Thin2CatLaws (LOG {ℓ} {ℓRel} {ℓCode})
LOGLaws {ℓ} {ℓRel} {ℓCode} =
  PointwiseStrict.PointwiseThin2CatLaws
    (Kernel ℓ ℓRel ℓCode)
    Code
    bnd
    KernelHom
    transportObs
    (λ {A} → idKernelHom A)
    _∘_
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerR∂ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerL∂ f {f = g} {g = g'} le)
    (λ _ _ → refl)
    (λ _ _ → refl)
    (λ _ _ _ _ → refl)
