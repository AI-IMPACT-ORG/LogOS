{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom2Cat.FlowSub2Cat where

open import LogOS.Prelude

-- Generic packaging: given a 2-category of kernel-like objects with 1-cells `Hom₁`
-- and a predicate/witness `Flow₁` on 1-cells (closed under id/compose),
-- bundle “flow-preserving 1-cells” into a sub-2-category.
--
-- This is purely structural (no quotienting, no extra axioms).

module With
  {ℓObj ℓHom ℓFlow : Level}
  (Obj : Set ℓObj)
  (Hom₁ : Obj → Obj → Set ℓHom)
  (Flow₁ : ∀ {K₁ K₂} → Hom₁ K₁ K₂ → Set ℓFlow)
  (idHom₁ : ∀ K → Hom₁ K K)
  (composeHom₁ : ∀ {K₁ K₂ K₃} → Hom₁ K₁ K₂ → Hom₁ K₂ K₃ → Hom₁ K₁ K₃)
  (idFlow₁ : ∀ K → Flow₁ (idHom₁ K))
  (composeFlow₁
    : ∀ {K₁ K₂ K₃} {f : Hom₁ K₁ K₂} {g : Hom₁ K₂ K₃}
    → Flow₁ f → Flow₁ g → Flow₁ (composeHom₁ f g))
  where

  record Hom₁ᶠ (K₁ K₂ : Obj) : Set (ℓObj ⊔ ℓHom ⊔ ℓFlow) where
    field
      hom  : Hom₁ K₁ K₂
      flow : Flow₁ hom

  open Hom₁ᶠ public

  idHom₁ᶠ : ∀ K → Hom₁ᶠ K K
  idHom₁ᶠ K = record { hom = idHom₁ K ; flow = idFlow₁ K }

  composeHom₁ᶠ
    : ∀ {K₁ K₂ K₃}
    → Hom₁ᶠ K₁ K₂ → Hom₁ᶠ K₂ K₃ → Hom₁ᶠ K₁ K₃
  composeHom₁ᶠ f g =
    record
      { hom  = composeHom₁ (Hom₁ᶠ.hom f) (Hom₁ᶠ.hom g)
      ; flow = composeFlow₁ (Hom₁ᶠ.flow f) (Hom₁ᶠ.flow g)
      }

