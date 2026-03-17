{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.HomFlow where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Flow preservation for kernel morphisms.
-- (design-target spec v5.8: “Normalisation doctrine”, subsection “Morphisms preserving flow”.)
--
-- A kernel morphism is flow-preserving when it commutes with the boundary
-- stabiliser/normaliser `Flow` up to refinement:
--
--   map∂ (Flow c) ⊑ Flow (map∂ c)
--
-- (Direction note: the right side is the stronger/entailing constraint.)
--
-- This is the single “lax categorical” coherence that upgrades a per-boundary
-- closure into a functorial doctrine across translations.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_; map∂; map∂-mono)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

record KernelHomFlow
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  (GC  : GuardedClosure (bnd K))
  (GC' : GuardedClosure (bnd K'))
  (h   : KernelHom K K')
  : Set (lsuc (ℓ ⊔ ℓRel)) where
  field
    preserves-Flow
      : ∀ c
      → _⊑_ (bnd K') (map∂ h (Flow GC c)) (Flow GC' (map∂ h c))

open KernelHomFlow public
idKernelHomFlow
  : ∀ {ℓ ℓRel ℓCode} {K : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → KernelHomFlow GC GC (idKernelHom K)
idKernelHomFlow {K = K} GC =
  record { preserves-Flow = λ _ → refl⊑ (bnd K) }

composeKernelHomFlow
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    {GC₁ : GuardedClosure (bnd K₁)}
    {GC₂ : GuardedClosure (bnd K₂)}
    {GC₃ : GuardedClosure (bnd K₃)}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
  → KernelHomFlow GC₁ GC₂ f
  → KernelHomFlow GC₂ GC₃ g
  → KernelHomFlow GC₁ GC₃ (g ∘ f)
composeKernelHomFlow {K₃ = K₃} {GC₁ = GC₁} {GC₂ = GC₂} {GC₃ = GC₃} {f = f} {g = g} ff gg =
  record
    { preserves-Flow = λ c →
        let
          module R = ≤-Reasoning (bnd K₃)
          open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
        in
        begin⊑
          (map∂ g (map∂ f (Flow GC₁ c))) ⊑⟨ map∂-mono g (preserves-Flow ff c) ⟩
          (map∂ g (Flow GC₂ (map∂ f c))) ⊑⟨ preserves-Flow gg (map∂ f c) ⟩
          (Flow GC₃ (map∂ g (map∂ f c))) ∎⊑
    }
