{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Functor.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; mapObj; mapHom)

record StrictThin2Functor
  {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ : Level}
  (C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁)
  (C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂)
  : Set (lsuc (ℓObj₁ ⊔ ℓHomCon₁ ⊔ ℓHomRel₁ ⊔ ℓObj₂ ⊔ ℓHomCon₂ ⊔ ℓHomRel₂)) where
  private
    module C = Thin2Cat C₁
    module D = Thin2Cat C₂
  field
    F : Thin2Functor C₁ C₂

    id-pres≡
      : ∀ {A}
      → mapHom F (C.id {A = A})
        ≡ D.id {A = mapObj F A}

    comp-pres≡
      : ∀ {A B C₀}
        (f : Con (C.Hom B C₀))
        (g : Con (C.Hom A B))
      → mapHom F (f C.∘ g)
        ≡ mapHom F f D.∘ mapHom F g

open StrictThin2Functor public
