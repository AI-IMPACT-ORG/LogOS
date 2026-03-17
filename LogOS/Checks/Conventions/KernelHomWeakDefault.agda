{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.KernelHomWeakDefault where

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; KernelHom≈; BehavioralKernelHom)

KernelHom-default-isBehavioralDef
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → BehavioralKernelHom K K' ≡ KernelHom K K'
KernelHom-default-isBehavioralDef = refl

KernelHom-default-isApproxDef
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom K K' ≡ KernelHom≈ K K'
KernelHom-default-isApproxDef = refl
