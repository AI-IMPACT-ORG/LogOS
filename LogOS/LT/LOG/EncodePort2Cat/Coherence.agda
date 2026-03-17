{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.EncodePort2Cat.Coherence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_≈_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; EncodePort; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; mapCode; idKernelHom; _∘_)
open import LogOS.LT.LOG.EncodePort2Cat using (EncodeLaw)

import LogOS.LT.LOG.EncodePort2Cat as EncodeLaw
import LogOS.LT.Presentation.ExtensionalMinimality as ExtMin
open import LogOS.LT.ConPreorder using (monoMap-≈)

record EncodeCoherence {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
  (h : KernelHom K K')
  (EK  : EncodePort K)
  (EK' : EncodePort K')
  : Set (ℓ ⊔ ℓRel ⊔ ℓCode) where
  field
    mapCode-encode
      : ∀ c
      → _≈_ (CodePreorder K')
          (mapCode h (LogOS.LT.Kernel.encode EK c))
          (LogOS.LT.Kernel.encode EK' (map∂ h c))

open EncodeCoherence public

coherence→law
  : ∀ {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
    {h : KernelHom K K'}
    {EK : EncodePort K}
    {EK' : EncodePort K'}
  → EncodeCoherence h EK EK'
  → EncodeLaw h EK EK'
coherence→law coh =
  record { mapCode-encode⊑ = λ c → fst (mapCode-encode coh c) }

idEncodeCoherence
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → (EK : EncodePort K)
  → EncodeCoherence (idKernelHom K) EK EK
idEncodeCoherence {K = K} _ =
  record
    { mapCode-encode = λ _ → (refl⊑ (CodePreorder K) , refl⊑ (CodePreorder K))
    }

composeEncodeCoherence
  : ∀ {ℓ ℓRel ℓCode : Level} {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {EK₁ : EncodePort K₁}
    {EK₂ : EncodePort K₂}
    {EK₃ : EncodePort K₃}
  → EncodeCoherence f EK₁ EK₂
  → EncodeCoherence g EK₂ EK₃
  → EncodeCoherence (g ∘ f) EK₁ EK₃
composeEncodeCoherence {K₂ = K₂} {K₃ = K₃} {f = f} {g = g} {EK₁ = EK₁} {EK₂ = EK₂} {EK₃ = EK₃} cf cg =
  record
    { mapCode-encode =
        λ c →
          let
            monoMapCodeG = ExtMin.mapCode-mono g
            module R = LogOS.Prelude.RefinementKit.Reasoning (CodePreorder K₃)
            open R using (begin≈_; _≈⟨_⟩_; _∎≈)
          in
          begin≈
            mapCode (g ∘ f) (LogOS.LT.Kernel.encode EK₁ c)
              ≈⟨ monoMap-≈
                    {CP₁ = CodePreorder K₂}
                    {CP₂ = CodePreorder K₃}
                    {f = mapCode g}
                    monoMapCodeG
                    (mapCode f (LogOS.LT.Kernel.encode EK₁ c))
                    (LogOS.LT.Kernel.encode EK₂ (map∂ f c))
                    (mapCode-encode cf c)
              ⟩
            mapCode g (LogOS.LT.Kernel.encode EK₂ (map∂ f c))
              ≈⟨ mapCode-encode cg (map∂ f c) ⟩
            LogOS.LT.Kernel.encode EK₃ (map∂ (g ∘ f) c)
            ∎≈
    }
