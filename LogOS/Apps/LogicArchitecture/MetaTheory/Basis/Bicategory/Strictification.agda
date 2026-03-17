{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory.Strictification where

-- Optional S-tier bicategory coherence equalities.

open import LogOS.Prelude
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using (BicatW)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps; TwoCellOpsLaws)

record BicatWCoherence {ℓObj ℓHom₁ ℓHom₂ : Level} (B : BicatW ℓObj ℓHom₁ ℓHom₂)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  private
    C = BicatW.ops B
    L = BicatW.laws B

  open TwoCellOps C using
    ( Hom₁
    ; Hom₂
    ; id1
    ; _∘1_
    ; _∙2_
    ; whiskerL2
    ; whiskerR2
    )

  open TwoCellOpsLaws L using (id-left; id-right; assoc)

  id-left2
    : ∀ {A B} (f : Hom₁ A B)
    → Hom₂ ((id1 {A = B}) ∘1 f) f
  id-left2 f = fst (id-left f)

  id-right2
    : ∀ {A B} (f : Hom₁ A B)
    → Hom₂ (f ∘1 (id1 {A = A})) f
  id-right2 f = fst (id-right f)

  assoc2
    : ∀ {A B C D}
      (h : Hom₁ C D)
      (g : Hom₁ B C)
      (f : Hom₁ A B)
    → Hom₂ ((h ∘1 g) ∘1 f) (h ∘1 (g ∘1 f))
  assoc2 h g f = fst (assoc h g f)

  field
    pentagon
      : ∀ {A B C D E}
        (k : Hom₁ D E)
        (h : Hom₁ C D)
        (g : Hom₁ B C)
        (f : Hom₁ A B)
      → ((whiskerL2 {g = f} (assoc2 k h g) ∙2 assoc2 k (h ∘1 g) f)
          ∙2 whiskerR2 {f = k} (assoc2 h g f))
        ≡
        (assoc2 (k ∘1 h) g f ∙2 assoc2 k h (g ∘1 f))

    triangle
      : ∀ {A B C}
        (g : Hom₁ B C)
        (f : Hom₁ A B)
      → whiskerL2 {g = f} (id-right2 g)
        ≡
        (assoc2 g (id1 {A = B}) f ∙2 whiskerR2 {f = g} (id-left2 f))
