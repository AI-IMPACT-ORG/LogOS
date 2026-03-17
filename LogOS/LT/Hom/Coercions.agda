{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom.Coercions where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Explicit coherence coercions between the default refinement surfaces
-- (guarded refinement remains encoded as boundary constraints).

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; bnd)

import LogOS.LT.Hom.Core as Hom

approx→under
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → Hom.KernelHom K K'
  → Hom.KernelHom⊑ K K'
approx→under h =
  Hom.mkKernelHomParts
    (Hom.boundaryPart (Hom.toKernelHomLikeR h))
    (record
      { mapCode = Hom.mapCode h
      ; decode-mapCode = λ γ → fst (Hom.decode-mapCode h γ)
      })
