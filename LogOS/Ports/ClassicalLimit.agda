{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.ClassicalLimit where

-- Explicit classical-limit ports:
-- bundle *antisymmetry* as an opt-in assumption, so strictness never becomes ambient.
-- (“Classical limit” here means extensional/posetal collapse, not classical logic/LEM.)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
import LogOS.LT.ConPreorder.Antisymmetry as Anti
open Anti public using (Antisymmetry; antisym; ≈→≡)
open import LogOS.LT.Kernel using (Kernel; bnd)
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.Hom.Strictification as StrictHom

strictifyKernelHom
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → Antisymmetry (bnd K')
  → Hom.KernelHom K K'
  → StrictHom.KernelHom≡ K K'
strictifyKernelHom anti h =
  StrictHom.mkKernelHom≡Parts
    (Hom.boundaryPart (Hom.toKernelHomLikeR h))
    (record
      { mapCode = Hom.mapCode h
      ; decode-mapCode = λ γ → ≈→≡ anti (Hom.decode-mapCode≈ h γ)
      })
