{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.ArchitectureImplementationLaw where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Discipline gate for the architecture / implementation / façade split.
--
-- This module is intentionally brittle: it asserts that the implementation layer
-- is literally a displayed totalisation over architectural boundary transport,
-- and that the façade is still a definitional weakening of that totalisation.

open import LogOS.Prelude using (Level; lzero; ⊤; tt; _≡_; refl)
open import LogOS.LT.ConPreorder using (_⊑_)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.Hom.Core using (KernelHomLike; KernelHomLikeR; KernelHom; KernelHom≈)
open import LogOS.LT.DisplayedThin2Cat using (DecoratedThin2Cat)
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat

kernelHomLike≈-factorises
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (K' : Kernel ℓ ℓRel ℓCode')
  → KernelHomLike approx K K'
    ≡ KernelHomLikeR approx K K'
kernelHomLike≈-factorises _ _ = refl

kernelHom-default-is-approx
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    (K : Kernel ℓ ℓRel ℓCode)
    (K' : Kernel ℓ ℓRel ℓCode')
  → KernelHom K K' ≡ KernelHom≈ K K'
kernelHom-default-is-approx _ _ = refl

LOGArchitectureImplementation-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Implementation2Cat.LOGArchitectureImplementation {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (Implementation2Cat.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})
LOGArchitectureImplementation-isDecorated = refl

toFacadeHom-def
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → Implementation2Cat.toFacadeHom {ℓ} {ℓRel} {ℓCode} {K} {K'}
    ≡ Implementation2Cat.toKernelHom {ℓ} {ℓRel} {ℓCode} {K} {K'}
toFacadeHom-def = refl

fromFacadeHom-def
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → Implementation2Cat.fromFacadeHom {ℓ} {ℓRel} {ℓCode} {K} {K'}
    ≡ Implementation2Cat.fromKernelHom {ℓ} {ℓRel} {ℓCode} {K} {K'}
fromFacadeHom-def = refl

toFacadeLOG-def
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Implementation2Cat.toFacadeLOG {ℓ} {ℓRel} {ℓCode}
    ≡ Implementation2Cat.toLOG {ℓ} {ℓRel} {ℓCode}
toFacadeLOG-def = refl

ok : ⊤ {ℓ = lzero}
ok = tt
