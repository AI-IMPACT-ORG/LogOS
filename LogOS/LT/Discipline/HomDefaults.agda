{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.HomDefaults where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Hom-default discipline gates.
--
-- This module is intentionally brittle: it asserts that the default LT kernel
-- morphism surface uses `≈`-coherence, and that identity/composition are
-- definitionally the generic coherence-polymorphic operations specialised to
-- that default.

open import LogOS.Prelude using (Level; lzero; ⊤; tt; _≡_; refl)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (_⊑[_]_)
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.Hom.Core using
  ( KernelHomLike
  ; KernelHom≈
  ; KernelHom
  ; idKernelHomLike
  ; idKernelHom
  ; _∘Like_
  ; _∘_
  ; transportView
  ; _⇒∂_
  )
open import LogOS.LT.LOG.Kernel2Cat using (KernelHomPreorder)

private
  KernelHom-def
    : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
      (K : Kernel ℓ ℓRel ℓCode)
      (K' : Kernel ℓ ℓRel ℓCode')
    → KernelHom K K' ≡ KernelHom≈ K K'
  KernelHom-def _ _ = refl

  idKernelHom-def
    : ∀ {ℓ ℓRel ℓCode : Level}
      (K : Kernel ℓ ℓRel ℓCode)
    → idKernelHom K ≡ idKernelHomLike {m = approx} K
  idKernelHom-def _ = refl

  ∘-def
    : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
      {K₁ : Kernel ℓ ℓRel ℓCode₁}
      {K₂ : Kernel ℓ ℓRel ℓCode₂}
      {K₃ : Kernel ℓ ℓRel ℓCode₃}
    → (_∘_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃})
      ≡ (_∘Like_ {m = approx} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃})
  ∘-def = refl

  ⇒∂-def
    : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {K' : Kernel ℓ ℓRel ℓCode'}
    → (f g : KernelHom K K')
    → (f ⇒∂ g) ≡ (f ⊑[ forget (transportView {K = K} {K' = K'}) ] g)
  ⇒∂-def _ _ = refl

  KernelHomPreorder-⊑-def
    : ∀ {ℓ ℓRel ℓCode : Level}
      (K : Kernel ℓ ℓRel ℓCode)
      (K' : Kernel ℓ ℓRel ℓCode)
    → ConPreorder._⊑_ (KernelHomPreorder K K') ≡ _⇒∂_
  KernelHomPreorder-⊑-def _ _ = refl

-- Export one harmless witness so this module can be imported via the API
-- without re-exporting all internal discipline lemmas.
ok : ⊤ {ℓ = lzero}
ok = tt
