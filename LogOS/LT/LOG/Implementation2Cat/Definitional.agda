{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Implementation2Cat.Definitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Definitional/bookkeeping equalities for the architecture/implementation
-- displayed layer.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Coherence using (CohMode; approx)
open import LogOS.LT.DisplayedThin2Cat using (DecoratedHom)
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.LOG.Implementation2Cat.Core as Core

to-fromKernelHomLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (h : Hom.KernelHomLike m K K')
  → Core.toKernelHomLike (Core.fromKernelHomLike {m = m} {ℓ} {ℓRel} {ℓCode} {K} {K'} h) ≡ h
to-fromKernelHomLike _ = refl

to-fromKernelHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (h : Hom.KernelHom K K')
  → Core.toKernelHom (Core.fromKernelHom {ℓ} {ℓRel} {ℓCode} {K} {K'} h) ≡ h
to-fromKernelHom = to-fromKernelHomLike {m = approx}

from-toKernelHomLike
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (f : DecoratedHom
            (Core.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})
            (Core.embedLike {m = m} K)
            (Core.embedLike {m = m} K'))
  → Core.fromKernelHomLike {m = m} (Core.toKernelHomLike {m = m} {ℓ} {ℓRel} {ℓCode} {K} {K'} f) ≡ f
from-toKernelHomLike _ = refl

from-toKernelHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (f : DecoratedHom (Core.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode}) (Core.embed K) (Core.embed K'))
  → Core.fromKernelHom (Core.toKernelHom {ℓ} {ℓRel} {ℓCode} {K} {K'} f) ≡ f
from-toKernelHom = from-toKernelHomLike {m = approx}
