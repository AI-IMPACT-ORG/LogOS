{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomFlowShared where

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

module With
  {ℓObj ℓ : Level}
  (Obj : Set ℓObj)
  (BBOf : Obj → BulkBoundary ℓ)
  (ClosureOf : (K : Obj) → Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (BBOf K)))
  (Hom : Obj → Obj → Set (lsuc (lsuc ℓ)))
  (map∂Of : ∀ {K₁ K₂ : Obj} → Hom K₁ K₂
          → ConPreorder.Con (BulkBoundary.bnd (BBOf K₁))
          → ConPreorder.Con (BulkBoundary.bnd (BBOf K₂)))
  where

  record HomFlow (K₁ K₂ : Obj) (h : Hom K₁ K₂) : Set (lsuc (lsuc ℓ)) where
    field
      flow-hom
        : Truth.GuardedCore.FlowHom
            (BulkBoundary.bnd (BBOf K₁))
            (BulkBoundary.bnd (BBOf K₂))
            (ClosureOf K₁)
            (ClosureOf K₂)
            (map∂Of h)

  record HomFlowStable (K₁ K₂ : Obj) (h : Hom K₁ K₂) : Set (lsuc (lsuc ℓ)) where
    field
      stable-hom
        : Truth.GuardedCore.FlowHomStable
            (BulkBoundary.bnd (BBOf K₁))
            (BulkBoundary.bnd (BBOf K₂))
            (ClosureOf K₁)
            (ClosureOf K₂)
            (map∂Of h)

    open Truth.GuardedCore.FlowHomStable stable-hom public

  homFlowOfStable
    : ∀ {K₁ K₂ : Obj} {h : Hom K₁ K₂}
    → HomFlowStable K₁ K₂ h
    → HomFlow K₁ K₂ h
  homFlowOfStable hf =
    record { flow-hom = HomFlowStable.flow-hom hf }
