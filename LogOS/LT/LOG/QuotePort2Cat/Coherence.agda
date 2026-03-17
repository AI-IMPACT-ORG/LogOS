{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.QuotePort2Cat.Coherence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_)
open import LogOS.LT.HomFlow using (KernelHomFlow; idKernelHomFlow; composeKernelHomFlow)
import LogOS.LT.LOG.EncodePort2Cat.Coherence as EncodeCoherence
import LogOS.LT.LOG.QuotePort2Cat.Displayed as QuoteLaw
import LogOS.LT.LOG.QuotePort2Cat.Port as Port

open Port using (QuotePort; GC; EK)

record QuoteCoherence {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
  (h : KernelHom K K')
  (QP  : QuotePort K)
  (QP' : QuotePort K')
  : Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) where
  field
    flow   : KernelHomFlow (GC QP) (GC QP') h
    encode : EncodeCoherence.EncodeCoherence h (EK QP) (EK QP')

open QuoteCoherence public

coherence→law
  : ∀ {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
    {h : KernelHom K K'}
    {QP : QuotePort K}
    {QP' : QuotePort K'}
  → QuoteCoherence h QP QP'
  → QuoteLaw.QuoteLaw h QP QP'
coherence→law q =
  record
    { flow = flow q
    ; encode = EncodeCoherence.coherence→law (encode q)
    }

idQuoteCoherence
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → QuoteCoherence (idKernelHom K) QP QP
idQuoteCoherence QP =
  record
    { flow = idKernelHomFlow (GC QP)
    ; encode = EncodeCoherence.idEncodeCoherence (EK QP)
    }

composeQuoteCoherence
  : ∀ {ℓ ℓRel ℓCode : Level} {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {QP₁ : QuotePort K₁}
    {QP₂ : QuotePort K₂}
    {QP₃ : QuotePort K₃}
  → QuoteCoherence f QP₁ QP₂
  → QuoteCoherence g QP₂ QP₃
  → QuoteCoherence (g ∘ f) QP₁ QP₃
composeQuoteCoherence cf cg =
  record
    { flow = composeKernelHomFlow (flow cf) (flow cg)
    ; encode = EncodeCoherence.composeEncodeCoherence (encode cf) (encode cg)
    }
