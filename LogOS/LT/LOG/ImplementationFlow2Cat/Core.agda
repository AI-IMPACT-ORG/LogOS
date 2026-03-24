{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ImplementationFlow2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Flow-equipped kernels as a law stack over the architectural base `LOGᴳ`.
--
-- Reading:
-- - architecture: boundary morphisms + boundary-only refinements
-- - implementation: displayed code-level witnesses over that architecture
-- - law: displayed guarded-closure structure layered afterwards

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_; refl⊑)
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.Kernel using (bnd)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.LT.LOG.Boundary2Cat using
  ( LOGᴳ
  ; map∂
  ; map∂-mono
  )

import LogOS.LT.LOG.Flow2Cat as FlowLOG
import LogOS.LT.LOG.ImplementationLawStack2Cat as ImplementationLaw

FlowDisplayedᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOGᴳ {ℓ} {ℓRel} {ℓCode}) (lsuc (ℓ ⊔ ℓRel)) (ℓ ⊔ ℓRel)
FlowDisplayedᴳ {ℓ} {ℓRel} {ℓCode} =
  let
    C = LOGᴳ {ℓ} {ℓRel} {ℓCode}
    module C = Thin2Cat C
  in
  record
    { Ob = λ K → GuardedClosure (bnd K)
    ; HomD =
        λ {K} {K'} (h : Con (C.Hom K K'))
          (GC : GuardedClosure (bnd K))
          (GC' : GuardedClosure (bnd K'))
        → ∀ c
        → _⊑_ (bnd K') (map∂ h (Flow GC c)) (Flow GC' (map∂ h c))
    ; idD = λ {K} GC c → refl⊑ (bnd K)
    ; compD =
        λ {K₁} {K₂} {K₃} {h} {k} {GC₁} {GC₂} {GC₃} compat₁₂ compat₂₃ c →
          let
            module R = ≤-Reasoning (bnd K₃)
            open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
          in
          begin⊑
            map∂ k (map∂ h (Flow GC₁ c)) ⊑⟨ map∂-mono k (compat₁₂ c) ⟩
            map∂ k (Flow GC₂ (map∂ h c)) ⊑⟨ compat₂₃ (map∂ h c) ⟩
            Flow GC₃ (map∂ k (map∂ h c)) ∎⊑
    }

module Base {ℓ ℓRel ℓCode : Level} =
  ImplementationLaw.Build
    FlowLOG.FlowTag
    (FlowDisplayedᴳ {ℓ} {ℓRel} {ℓCode})
    (FlowLOG.FlowDisplayed {ℓ} {ℓRel} {ℓCode})
    (λ GC → GC)
    (λ _ _ compat → record { preserves-Flow = compat })

open Base public
  renaming
    ( lawSig to flowSig
    ; lawSingleton to flowSingleton
    ; lawStackᴳ to flowStackᴳ
    ; ImplementationLawStackLike to ImplementationFlowStackLike
    ; ImplementationLawStack to ImplementationFlowStack
    ; ImplementationLawStackUnder to ImplementationFlowStackUnder
    ; ImplementationLawCatLike to LOGᴳʳᶠLike
    ; ImplementationLawCat to LOGᴳʳᶠ
    ; ImplementationLawCatUnder to LOGᴳʳᶠ⊑
    ; forgetImplementationLaw to forgetᴳʳᶠ→ᶠ
    )

LOGArchitectureImplementationFlow = LOGᴳʳᶠ
LOGArchitectureImplementationFlowUnder = LOGᴳʳᶠ⊑
