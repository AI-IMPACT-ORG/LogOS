{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Implementation2Cat.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing laws for the implementation-layer displayed presentation.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode; CohRel)
open import LogOS.LT.Kernel using (Kernel; Code; bnd; decode)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using (DecoratedObj; DecoratedHom; base)
import LogOS.LT.BoundaryHom as Boundary
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat

toKernelHomLike-fromKernelHomLikeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
    (h : Hom.KernelHomLike m K K')
    (γ : Code K)
  → CohRel m (bnd K')
      (decode K' (Hom.mapCode (Implementation2Cat.toKernelHomLike (Implementation2Cat.fromKernelHomLike h)) γ))
      (Hom.map∂ h (decode K γ))
toKernelHomLike-fromKernelHomLikeLaw h = Hom.decode-mapCode h

fromKernelHomLike-toKernelHomLikeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {X Y : DecoratedObj (Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})}
    (h : DecoratedHom (Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}) X Y)
    (γ : Code (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} X))
  → CohRel m
      (bnd (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} Y))
      (decode
        (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} Y)
        (Hom.mapCode (Implementation2Cat.toKernelHomLike′ h) γ))
      (Hom.map∂
        (Implementation2Cat.toKernelHomLike′ h)
        (decode
          (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} X)
          γ))
fromKernelHomLike-toKernelHomLikeLaw h =
  Hom.decode-mapCode (Implementation2Cat.toKernelHomLike′ h)

forgetImplementationLikeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    {X Y : DecoratedObj (Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode})}
    (h : DecoratedHom (Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}) X Y)
    (γ : Code (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} X))
  → CohRel m
      (bnd (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} Y))
      (decode
        (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} Y)
        (Hom.mapCode (Implementation2Cat.toKernelHomLike′ h) γ))
      (Hom.boundaryMap∂
        (lower
          (Thin2Functor.mapHom
            (Implementation2Cat.forgetImplementationLike {m = m} {ℓ} {ℓRel} {ℓCode})
            h))
        (decode
          (base {D = Implementation2Cat.ImplementationDisplayedLike {m = m} {ℓ} {ℓRel} {ℓCode}} X)
          γ))
forgetImplementationLikeLaw h =
  Hom.decode-mapCode (Implementation2Cat.toKernelHomLike′ h)
