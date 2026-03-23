{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.StrictDecode2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Strict decode law as a law-port over `LOG`.
--
-- Engineering reading:
-- this is the explicit S-tier robustness check that a kernel morphism preserves
-- decoding on-the-nose (`≡`, S-tier), rather than only up to `≈`.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.Kernel using (Kernel; decode)
open import LogOS.LT.Hom.Core as Hom using (KernelHom; mapCode; map∂; idKernelHom; _∘_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)

import LogOS.LT.Ports.Template.Singleton2Cat as Template
import LogOS.LT.Ports.Template.LawSingleton2Cat as LawTemplate

StrictDecodeLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K K' : Kernel ℓ ℓRel ℓCode}
  → KernelHom K K'
  → Set (ℓ ⊔ ℓCode)
StrictDecodeLaw {K = K} {K' = K'} h =
  ∀ γ → decode K' (mapCode h γ) ≡ map∂ h (decode K γ)

idStrictDecodeLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → StrictDecodeLaw (idKernelHom K)
idStrictDecodeLaw _ = refl

composeStrictDecodeLaw
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
  → StrictDecodeLaw f
  → StrictDecodeLaw g
  → StrictDecodeLaw (g ∘ f)
composeStrictDecodeLaw {f = f} {g = g} sf sg γ =
  trans (sg (mapCode f γ)) (cong (map∂ g) (sf γ))

-- --------------------------------------------------------------------------
-- PortStack packaging: tag + signature + singleton stack.

data StrictDecodeTag : Set where
  strictDecodeTag : StrictDecodeTag

strictDecodeTagId : ℕ
strictDecodeTagId = 25

-- Use an explicit unit type for the (trivial) object payload.
-- This avoids `⊤`/`tt` footguns when composing multiple law ports.
data StrictDecodeUnit : Set where
  strictDecodeUnit : StrictDecodeUnit

module Port {ℓ ℓRel ℓCode : Level} =
  LawTemplate.LawExports
    {C = LOG {ℓ} {ℓRel} {ℓCode}}
    {Tag = StrictDecodeTag}
    strictDecodeTagId
    StrictDecodeUnit
    StrictDecodeLaw
    (λ {A} → idStrictDecodeLaw {K = A})
    (λ {A} {B} {C₀} {f} {g} sf sg →
      composeStrictDecodeLaw {K₁ = A} {K₂ = B} {K₃ = C₀} {f = f} {g = g} sf sg)

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
