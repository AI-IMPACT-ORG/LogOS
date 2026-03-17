{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.GuardedKernel2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core using (KernelHom⊑; idKernelHomLike; _∘Like_; map∂; map∂-mono)
open import LogOS.LT.Coherence using (under)
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
import LogOS.LT.Thin2Cat.Pointwise as Pointwise
import LogOS.LT.Thin2Cat.Pointwise.Strictification as PointwiseStrict

infix 4 _⇒⊑_
_⇒⊑_
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → KernelHom⊑ K K'
  → KernelHom⊑ K K'
  → Set (ℓ ⊔ ℓRel)
_⇒⊑_ {K = K} {K' = K'} f g = ∀ c → _⊑_ (bnd K') (map∂ f c) (map∂ g c)

map∂-∘⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    (g : KernelHom⊑ K₂ K₃)
    (f : KernelHom⊑ K₁ K₂)
    (c : Con (bnd K₁))
  → map∂ (_∘Like_ {m = under} g f) c ≡ map∂ g (map∂ f c)
map∂-∘⊑ g f c = refl

whiskerL⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode}
    {K₂ : Kernel ℓ ℓRel ℓCode}
    {K₃ : Kernel ℓ ℓRel ℓCode}
  → (h : KernelHom⊑ K₂ K₃)
  → {f g : KernelHom⊑ K₁ K₂}
  → f ⇒⊑ g
  → (h ∘Like f) ⇒⊑ (h ∘Like g)
whiskerL⊑ h {f} {g} le c
  = map∂-mono h (le c)

whiskerR⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode}
    {K₂ : Kernel ℓ ℓRel ℓCode}
    {K₃ : Kernel ℓ ℓRel ℓCode}
  → {f g : KernelHom⊑ K₂ K₃}
  → (k : KernelHom⊑ K₁ K₂)
  → f ⇒⊑ g
  → (f ∘Like k) ⇒⊑ (g ∘Like k)
whiskerR⊑ {f = f} {g = g} k le c
  = le (map∂ k c)

KernelHomPreorder⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode → ConPreorder (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) (ℓ ⊔ ℓRel)
KernelHomPreorder⊑ {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseHom
    (λ K → Con (bnd K))
    bnd
    KernelHom⊑
    map∂

LOG⊑
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
      (ℓ ⊔ ℓRel)
LOG⊑ {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseThin2Cat
    (Kernel ℓ ℓRel ℓCode)
    (λ K → Con (bnd K))
    bnd
    KernelHom⊑
    map∂
    (λ {A} → idKernelHomLike {m = under} A)
    (_∘Like_ {m = under})
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerR⊑ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerL⊑ f {f = g} {g = g'} le)

LOGGuarded = LOG⊑

LOG⊑Laws : ∀ {ℓ ℓRel ℓCode : Level} → Thin2CatLaws (LOG⊑ {ℓ} {ℓRel} {ℓCode})
LOG⊑Laws {ℓ} {ℓRel} {ℓCode} =
  PointwiseStrict.PointwiseThin2CatLaws
    (Kernel ℓ ℓRel ℓCode)
    (λ K → Con (bnd K))
    bnd
    KernelHom⊑
    map∂
    (λ {A} → idKernelHomLike {m = under} A)
    (_∘Like_ {m = under})
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerR⊑ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerL⊑ f {f = g} {g = g'} le)
    (λ _ _ → refl)
    (λ _ _ → refl)
    (λ _ _ _ _ → refl)
